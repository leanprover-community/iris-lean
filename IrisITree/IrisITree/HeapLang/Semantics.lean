/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import ITree
public import IrisITree.Effects.Heap
public import Iris.HeapLang
public import Iris.Std.BitOp
import Iris.Std.FromMathlib

@[expose] public section

namespace IrisITree

open Iris.HeapLang ITree ITree.Effects ITree.Exec

instance lawfulLoc_heaplang : LawfulLoc Loc where
  decEq := inferInstance
  add_zero l := by ext; simp
  add_nat_inj l i j := by ext; simp [Int.add_assoc]
  add_pos_gt l m := by
    simp [compare, compareOfLessAndEq]
    grind

abbrev heaplangE := concE ⊕ₑ heapE Loc Val ⊕ₑ failE ⊕ₑ demonicE Loc ⊕ₑ stepE

structure HeaplangState (T : Type) : Type where
  tp : ConcState T
  heap : heapE.T Loc Val
  steps : Nat
  steps_left : Nat

@[simp]
def HeaplangStateIso T : Iso (ConcState T × heapE.T Loc Val × PUnit × PUnit × (ULift Nat × ULift Nat)) (HeaplangState T) where
  toFun x := ⟨x.1, x.2.fst, ULift.down x.2.2.2.2.1, ULift.down x.2.2.2.2.2⟩
  invFun x := ⟨x.tp, x.heap, ⟨⟩, ⟨⟩, ⟨ULift.up x.steps, ULift.up x.steps_left⟩⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

abbrev heaplangEH {GE GR} (nl : Nat → Nat) : EHandler heaplangE GE GR (HeaplangState (ITree GE GR)) :=
  isoEH (HeaplangStateIso (ITree GE GR)) (concEH ⊕ₑₕ (heapEH Loc Val ⊕ₛₑₕ failEH ⊕ₛₑₕ demonicEH Loc ⊕ₛₑₕ stepEH nl).toEHandler)

instance isoEHBind {E GE : Effect} {GR GR' : Type _} {σ₁ σ₂ : Type _} (iso : Iso σ₁ σ₂)
    (eh : EHandler E GE GR σ₁) (ehb : EHandler E GE GR' σ₁) [ib : EHandlerBind eh ehb] :
    EHandlerBind (isoEH iso eh) (isoEH iso ehb) where
  bind_handle i s k₁ k₂ p h :=
    ib.bind_handle i (iso.invFun s) k₁ k₂ (fun t s' => p t (iso.toFun s')) h

/-- Binding inside a HeapLang program: the heap, failure, demonic and step effects keep working
in the bound computation, while concurrency (`fork`, `yield`) fails there (`failingEH`). -/
instance heaplangEHBind {GE GR GR'} (nl : Nat → Nat) :
    EHandlerBind (GR' := GR') (heaplangEH nl)
      (isoEH (HeaplangStateIso (ITree GE GR))
        (failingEH ⊕ₑₕ (heapEH Loc Val ⊕ₛₑₕ failEH ⊕ₛₑₕ demonicEH Loc ⊕ₛₑₕ stepEH nl).toEHandler)) :=
  inferInstance

abbrev heaplangM := StateT (ConcState ((n : Nat) × ITreeN heaplangE Val n)) (StateT (heapE.T Loc Val) (ExceptT String IO))

instance : MonadEval heaplangM IO where
  monadEval x := do
    let r ← x |>.run (ConcState.new) |>.run ∅
    match r with
    | .ok v => return v.1.1
    | .error msg => IO.ofExcept <| .error (s!"Evaluation failed: {msg}")

end IrisITree

namespace Iris.HeapLang

open IrisITree ITree ITree.Effects ITree.Exec

def Val.int! [failE -< E] : Val → ITree E Int
  | .lit (.int i) => return i
  | x => fail s!"{reprStr x} is not Int"

def Val.bool! [failE -< E] : Val → ITree E Bool
  | .lit (.bool b) => return b
  | x => fail s!"{reprStr x} is not Bool"

def Val.loc! [failE -< E] : Val → ITree E Loc
  | .lit (.loc l) => return l
  | x => fail s!"{reprStr x} is not Loc"

def Val.pair! [failE -< E] : Val → ITree E (Val × Val)
  | .pair v1 v2 => return (v1, v2)
  | x => fail s!"{reprStr x} is not Pair"

def Val.rec! [failE -< E] : Val → ITree E (Binder × Binder × Exp)
  | .rec_ f x e => return (f, x, e)
  | x => fail s!"{reprStr x} is not Rec"

def Val.injL! [failE -< E] : Val → ITree E Val
  | .injL v => return v
  | x => fail s!"{reprStr x} is not InjL"

def Val.injR! [failE -< E] : Val → ITree E Val
  | .injR v => return v
  | x => fail s!"{reprStr x} is not InjR"

def UnOp.denote (op : UnOp) (v : Val) : ITree heaplangE Val :=
  match op, v with
  | .neg, .lit (.bool b) => return .lit (.bool !b)
  | .neg, .lit (.int n) => return .lit (.int (~~~n))
  | .minus, .lit (.int n) => return .lit (.int (-n))
  | _, _ => fail "UnOp: type mismatch"

def BinOp.denote (op : BinOp) (v₁ v₂ : Val) : ITree heaplangE Val :=
  if op == .eq then
    if Val.compareSafe v₁ v₂ then
      return .lit (.bool (decide (v₁ = v₂)))
    else
      fail "EqOp: comparing boxed values"
  else
    match v₁, v₂ with
    | .lit (.int n₁), .lit (.int n₂) => do
      let .some l := BinOp.evalInt op n₁ n₂
        | fail "BinOp: invalid int operation"
      return .lit l
    | .lit (.bool b₁), .lit (.bool b₂) => do
      let some l := BinOp.evalBool op b₁ b₂
        | fail "BinOp: invalid bool operation"
      return .lit l
    | .lit (.loc l₁), .lit v₂ => do
      let some l := BinOp.evalLoc op l₁ v₂
        | fail "BinOp: invalid loc operation"
      return .lit l
    | _, _ => fail "BinOp: type mismatch"

def Exp.yieldIfNotVal : Exp → ITree heaplangE Unit
  | .val _ => return ()
  | _ => yield

mutual

/-- Recursively denote the given expression `e`. -/
def Exp.denote (e : Exp) : ITree heaplangE Val :=
  -- continue the denotation with expression e
  let cont e := do step; e.yieldIfNotVal; denote e
  -- like cont but specialized for the value case
  let contVal v := do step; return v
  match e with
  | .val v => return v
  | .var x => fail s!"Unbound variable {reprStr x}"
  | .rec_ f x e => do contVal <| .rec_ f x e
  | .app e₁ e₂ => do
    let v ← Exp.denoteYield e₂
    let f ← Exp.denoteYield e₁
    let ⟨f', x', e⟩ ← f.rec!
    let body := e.subst f' f |>.subst x' v
    cont body
  | .unop op e => do
    let v ← Exp.denoteYield e
    let r ← op.denote v
    contVal r
  | .binop op e₁ e₂ => do
    let v₂ ← Exp.denoteYield e₂
    let v₁ ← Exp.denoteYield e₁
    let r ← op.denote v₁ v₂
    contVal r
  | .if e₀ e₁ e₂ => do
    let c ← Exp.denoteYield e₀
    if ← c.bool! then cont e₁
    else cont e₂
  | .pair e₁ e₂ => do
    let v₂ ← Exp.denoteYield e₂
    let v₁ ← Exp.denoteYield e₁
    contVal <| .pair v₁ v₂
  | .fst e => do
    let v ← Exp.denoteYield e
    let p ← v.pair!
    contVal p.1
  | .snd e => do
    let v ← Exp.denoteYield e
    let p ← v.pair!
    contVal <| p.2
  | .injL e => do
    let v ← Exp.denoteYield e
    contVal <| .injL v
  | .injR e => do
    let v ← Exp.denoteYield e
    contVal <| .injR v
  | .case e₀ e₁ e₂ => do
    let v ← Exp.denoteYield e₀
    match v with
    | .injL w => cont (.app e₁ (.val w))
    | .injR w => cont (.app e₂ (.val w))
    | _ => fail "Case: not a sum value"
  | .allocN e₁ e₂ => do
    let v ← Exp.denoteYield e₂
    let vn ← Exp.denoteYield e₁
    let n ← vn.int!
    if n ≤ 0 then fail "AllocN: count must be positive"
    let l ← HeapE.allocN n.toNat v
    contVal <| .lit (.loc l)
  | .free e => do
    let v ← Exp.denoteYield e
    let l ← v.loc!
    let .some _ ← storeOpt (Val:=Val) l none
      | fail "free: location not allocated"
    contVal <| .lit .unit
  | .load e => do
    let v ← Exp.denoteYield e
    let r ← load! (← v.loc!)
    contVal r
  | .store e₁ e₂ => do
    let v₂ ← Exp.denoteYield e₂
    let v₁ ← Exp.denoteYield e₁
    let _ ← store! (← v₁.loc!) v₂
    contVal <| .lit .unit
  | .cmpXchg e₀ e₁ e₂ => do
    let v₂ ← Exp.denoteYield e₂
    let v₁ ← Exp.denoteYield e₁
    let v₀ ← Exp.denoteYield e₀
    let l ← v₀.loc!
    let vl ← load! l
    if !Val.compareSafe vl v₁ then
      fail "CmpXchg: comparing boxed values"
    if vl = v₁ then
      let _ ← store! l v₂
      contVal <| .pair vl (.lit <| .bool true)
    else
      contVal <| .pair vl (.lit <| .bool false)
  | .xchg e₁ e₂ => do
    let v₂ ← Exp.denoteYield e₂
    let v₁ ← Exp.denoteYield e₁
    let r ← store! (← v₁.loc!) v₂
    contVal r
  | .faa e₁ e₂ => do
    let v₂ ← Exp.denoteYield e₂
    let v₁ ← Exp.denoteYield e₁
    let l ← v₁.loc!
    let i₂ ← v₂.int!
    let old ← load! l
    let i₁ ← old.int!
    let _ ← store! l (.lit (.int (i₁ + i₂)) : Val)
    contVal old
  | .fork e => do
    let _ ← ConcE.fork (Exp.denoteYield e >>= fun _ => return ⟨⟩)
    contVal <| .lit .unit
  | .newProph => do
    fail "prophecy is not implemented"
  | .resolve e₀ e₁ e₂ => do
    let _ ← Exp.denoteYield e₂
    let _ ← Exp.denoteYield e₁
    let _ ← Exp.denoteYield e₀
    fail "prophecy is not implemented"
partial_fixpoint

/-- Evaluate a subexpression, yielding afterwards exactly when it was not already a value. -/
def Exp.denoteYield (e : Exp) : ITree heaplangE Val :=
  if e.isVal then e.denote else yieldAfter <| e.denote
partial_fixpoint

end

open Iris.ProgramLogic.EctxItemLanguage

/-- A filled context item is never a value, so `denoteYield` evaluates it and then yields. -/
private theorem denoteYield_fill_item (Ki : ECtxItem) (e : Exp) :
    (Ki.fill e).denoteYield = yieldAfter (Ki.fill e).denote := by
  rw [Exp.denoteYield]
  cases Ki <;> rfl

/-- Evaluate the expression in the hole before evaluation of a context item. -/
theorem denote_bind_item (Ki : ECtxItem) (e : Exp) :
    (Ki.fill e).denote = e.denoteYield >>= fun v => (Ki.fill (.val v)).denote := by
  have denoteVal : ∀ v : Val, (Exp.val v).denoteYield = pure v := by
    intro v; simp only [Exp.denoteYield, Exp.isVal, ↓reduceIte, Exp.denote]
  revert e; induction Ki <;>
    simp only [ECtxItem.fill, ← val_to_ofVal, Exp.denote, denoteYield_fill_item,
      denoteVal, LawfulMonad.pure_bind, implies_true]
  case resolveL Ki v1 v2 IH =>
    intro e; simp only [yieldAfter, bind_pure_comp]
    rw [IH]; simp only [bind_assoc, val_to_ofVal]

/-- The yielding denotation composes with every evaluation-context item. -/
theorem denoteYield_bind_item (Ki : ECtxItem) (e : Exp) :
    (Ki.fill e).denoteYield =
      e.denoteYield >>= fun v => (Ki.fill (.val v)).denoteYield := by
  simp only [denoteYield_fill_item, ConcE.yieldAfter]
  rw [denote_bind_item]
  simp only [bind_assoc]

/-- The yielding denotation composes with arbitrary evaluation contexts. -/
theorem denoteYield_bind (K : List ECtxItem) (e : Exp) :
    (ProgramLogic.fill K e).denoteYield =
      e.denoteYield >>= fun v => (ProgramLogic.fill K (Exp.val v)).denoteYield := by
  induction K generalizing e with
  | nil =>
    simp only [fill_nil, Exp.denoteYield,
      Exp.isVal, ↓reduceIte, Exp.denote.eq_1, bind_pure]
  | cons Ki K IH =>
    simp only [fill_cons, fillItem]
    rw [IH, denoteYield_bind_item, bind_assoc]
    apply congrArg; funext v
    exact (IH (Ki.fill (.val v))).symm
   
/-- A nonempty context evaluates its hole before continuing with the resulting value. -/
theorem denote_bind (K : List ECtxItem) (e : Exp) (hK : K ≠ []) :
    (ProgramLogic.fill K e).denote =
      e.denoteYield >>= fun v => (ProgramLogic.fill K (Exp.val v)).denote := by
  cases K using FromMathlib.List.reverseCases with
  | nil => contradiction
  | append_singleton Ks Ki =>
    simp only [fill_append, fill_cons, fill_nil, fillItem]
    rw [denote_bind_item, denoteYield_bind, LawfulMonad.bind_assoc]
    apply congrArg; funext v
    exact (denote_bind_item Ki (ProgramLogic.fill Ks (Exp.val v))).symm

end Iris.HeapLang
