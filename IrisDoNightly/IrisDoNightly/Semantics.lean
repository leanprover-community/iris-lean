/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IrisDoNightly.Syntax
public import Std.Data.ExtTreeMap
public import Std.Data.ExtTreeSet

@[expose] public section
namespace Iris.HeapLang

open _root_.Std Iris.Std

inductive ECtxItem where
  | appL (v2 : Val)
  | appR (e1 : Exp)
  | unOp (op : UnOp)
  | binOpL (op : BinOp) (v2 : Val)
  | binOpR (op : BinOp) (e1 : Exp)
  | if (e1 e2 : Exp)
  | pairL (v2 : Val)
  | pairR (e1 : Exp)
  | fst
  | snd
  | injL
  | injR
  | case (e1 e2 : Exp)
  | allocNL (v2 : Val)
  | allocNR (e1 : Exp)
  | free
  | load
  | storeL (v2 : Val)
  | storeR (e1 : Exp)
  | xchgL (v2 : Val)
  | xchgR (e1 : Exp)
  | cmpXchgL (v1 v2 : Val)
  | cmpXchgM (e0 : Exp) (v2 : Val)
  | cmpXchgR (e0 e1 : Exp)
  | faaL (v2 : Val)
  | faaR (e1 : Exp)
  | resolveL (ctx : ECtxItem) (v1 v2 : Val)
  | resolveM (e0 : Exp) (v2 : Val)
  | resolveR (e0 e1 : Exp)
  deriving Inhabited, Repr, DecidableEq

def ECtxItem.fill (Ki : ECtxItem) (e : Exp) : Exp :=
  match Ki with
  | .appL v2        => .app e (.ofVal v2)
  | .appR e1        => .app e1 e
  | .unOp op        => .unop op e
  | .binOpL op v2   => .binop op e (.ofVal v2)
  | .binOpR op e1   => .binop op e1 e
  | .if e1 e2       => .if e e1 e2
  | .pairL v2       => .pair e (.ofVal v2)
  | .pairR e1       => .pair e1 e
  | .fst            => .fst e
  | .snd            => .snd e
  | .injL           => .injL e
  | .injR           => .injR e
  | .case e1 e2     => .case e e1 e2
  | .allocNL v2     => .allocN e (.ofVal v2)
  | .allocNR e1     => .allocN e1 e
  | .free           => .free e
  | .load           => .load e
  | .storeL v2      => .store e (.ofVal v2)
  | .storeR e1      => .store e1 e
  | .xchgL v2       => .xchg e (.ofVal v2)
  | .xchgR e1       => .xchg e1 e
  | .cmpXchgL v1 v2 => .cmpXchg e (.ofVal v1) (.ofVal v2)
  | .cmpXchgM e0 v2 => .cmpXchg e0 e (.ofVal v2)
  | .cmpXchgR e0 e1 => .cmpXchg e0 e1 e
  | .faaL v2        => .faa e (.ofVal v2)
  | .faaR e1        => .faa e1 e
  | .resolveL K v1 v2 => .resolve (K.fill e) (.ofVal v1) (.ofVal v2)
  | .resolveM e0 v2   => .resolve e0 e (.ofVal v2)
  | .resolveR e0 e1   => .resolve e0 e1 e

structure State where
  heap : Std.ExtTreeMap Loc (Option Val)
  usedProphId : Std.ExtTreeSet ProphId

instance : Inhabited State := ⟨.empty, .empty⟩

abbrev Observation := ProphId × (Val × Val)

def UnOp.eval : UnOp → Val → Option Val
  | .neg,   .lit (.bool b) => some (.lit (.bool (!b)))
  | .minus, .lit (.int n)  => some (.lit (.int (-n)))
  | _,      _              => none

def BinOp.eval : BinOp → Val → Val → Option Val
  | .plus,   .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1 + n2)))
  | .minus,  .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1 - n2)))
  | .mult,   .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1 * n2)))
  | .tdiv,   .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1.tdiv n2)))
  | .tmod,   .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1.tmod n2)))
  | .and,    .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1 &&& n2)))
  | .or,     .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1 ||| n2)))
  | .xor,    .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1 ^^^ n2)))
  | .and,    .lit (.bool b1), .lit (.bool b2) => some (.lit (.bool (b1 && b2)))
  | .or,     .lit (.bool b1), .lit (.bool b2) => some (.lit (.bool (b1 || b2)))
  | .xor,    .lit (.bool b1), .lit (.bool b2) => some (.lit (.bool (b1 ^^ b2)))
  | .shiftl, .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1 <<< n2)))
  | .shiftr, .lit (.int n1),  .lit (.int n2)  => some (.lit (.int (n1 >>> n2)))
  | .le,     .lit (.int n1),  .lit (.int n2)  => some (.lit (.bool (n1 ≤ n2)))
  | .lt,     .lit (.int n1),  .lit (.int n2)  => some (.lit (.bool (n1 < n2)))
  | .eq,     v1,              v2              =>
      if v1.compareSafe v2 then some (.lit (.bool (v1 == v2))) else none
  | .offset, .lit (.loc l),   .lit (.int n)   => some (.lit (.loc (l + n)))
  | _,       _,               _               => none

abbrev State.initHeap (σ : State) (l : Loc) (n : Int) (v : Option Val) : State :=
  { σ with heap := (List.range n.toNat).foldl
            (fun h (i : Nat) => Std.insert
                (M := fun V => Std.ExtTreeMap Loc V compare)
                h (l + (i : Int)) v) σ.heap }

abbrev State.get? (σ : State) (l : Loc) : Option (Option Val) :=
    PartialMap.get? (M := fun V => Std.ExtTreeMap Loc V compare) σ.heap l

inductive BaseStep : Exp → State → List Observation → Exp → State → List Exp → Prop where
  | recS (f x : Binder) (e : Exp) (σ : State) :
      BaseStep (.rec_ f x e) σ [] (.ofVal (.rec_ f x e)) σ []
  | pairS (v1 v2 : Val) (σ : State) :
      BaseStep (.pair (.ofVal v1) (.ofVal v2)) σ [] (.ofVal (.pair v1 v2)) σ []
  | injLS (v : Val) (σ : State) :
      BaseStep (.injL (.ofVal v)) σ [] (.ofVal (.injL v)) σ []
  | injRS (v : Val) (σ : State) :
      BaseStep (.injR (.ofVal v)) σ [] (.ofVal (.injR v)) σ []
  | betaS (f x : Binder) (e1 : Exp) (v2 : Val) (e' : Exp) (σ : State) :
      e' = (e1.subst f (.rec_ f x e1)).subst x v2 →
      BaseStep (.app (.ofVal (.rec_ f x e1)) (.ofVal v2)) σ [] e' σ []
  | unOpS (op : UnOp) (v v' : Val) (σ : State) :
      op.eval v = some v' →
      BaseStep (.unop op (.ofVal v)) σ [] (.ofVal v') σ []
  | binOpS (op : BinOp) (v1 v2 v' : Val) (σ : State) :
      op.eval v1 v2 = some v' →
      BaseStep (.binop op (.ofVal v1) (.ofVal v2)) σ [] (.ofVal v') σ []
  | ifTrueS (e1 e2 : Exp) (σ : State) :
      BaseStep (.if (.ofVal (.lit (.bool true))) e1 e2) σ [] e1 σ []
  | ifFalseS (e1 e2 : Exp) (σ : State) :
      BaseStep (.if (.ofVal (.lit (.bool false))) e1 e2) σ [] e2 σ []
  | fstS (v1 v2 : Val) (σ : State) :
      BaseStep (.fst (.ofVal (Val.pair v1 v2))) σ [] (.ofVal v1) σ []
  | sndS (v1 v2 : Val) (σ : State) :
      BaseStep (.snd (.ofVal (Val.pair v1 v2))) σ [] (.ofVal v2) σ []
  | caseLS (v : Val) (e1 e2 : Exp) (σ : State) :
      BaseStep (.case (.ofVal (.injL v)) e1 e2) σ [] (.app e1 (.ofVal v)) σ []
  | caseRS (v : Val) (e1 e2 : Exp) (σ : State) :
      BaseStep (.case (.ofVal (.injR v)) e1 e2) σ [] (.app e2 (.ofVal v)) σ []
  | allocNS (n : Int) (v : Val) (σ : State) (l : Loc) :
      0 < n →
      (∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none) →
      BaseStep (.allocN (.ofVal (.lit (.int n))) (.ofVal v)) σ
               [] (.ofVal (.lit (.loc l))) (σ.initHeap l n v) []
  | freeS (l : Loc) (v : Val) (σ : State) :
      σ.get? l = some v →
      BaseStep (.free (.ofVal (.lit (.loc l)))) σ
               [] (.ofVal (.lit .unit)) (σ.initHeap l 1 none) []
  | loadS (l : Loc) (v : Val) (σ : State) :
      σ.get? l = some v →
      BaseStep (.load (.ofVal (.lit (.loc l)))) σ [] (.ofVal v) σ []
  | storeS (l : Loc) (v w : Val) (σ : State) :
      σ.get? l = some v →
      BaseStep (.store (.ofVal (.lit (.loc l))) (.ofVal w)) σ
               [] (.ofVal (.lit .unit)) (σ.initHeap l 1 w) []
  | xchgS (l : Loc) (v1 v2 : Val) (σ : State) :
      σ.get? l = some v1 →
      BaseStep (.xchg (.ofVal (.lit (.loc l))) (.ofVal v2)) σ
               [] (.ofVal v1) (σ.initHeap l 1 v2) []
  | cmpXchgS (l : Loc) (v1 v2 vl : Val) (σ : State) (b : Bool) :
      σ.get? l = some vl →
      vl.compareSafe v1 →
      decide (vl = v1) = b →
      BaseStep (.cmpXchg (.ofVal (.lit (.loc l))) (.ofVal v1) (.ofVal v2)) σ
               []
               (.ofVal (.pair vl (.lit (.bool b))))
               (if b then (σ.initHeap l 1 v2) else σ) []
  | faaS (l : Loc) (i1 i2 : Int) (σ : State) :
      σ.get? l = some (some (.lit (.int i1))) →
      BaseStep (.faa (.ofVal (.lit (.loc l))) (.ofVal (.lit (.int i2)))) σ
               [] (.ofVal (.lit (.int i1)))
               (σ.initHeap l 1 (some (.lit (.int (i1 + i2))))) []
  | forkS (e : Exp) (σ : State) :
      BaseStep (.fork e) σ [] (.ofVal (.lit .unit)) σ [e]
  | newProphS (σ : State) (p : ProphId) :
      ¬ σ.usedProphId.contains p →
      BaseStep .newProph σ
               [] (.ofVal (.lit (.prophecy p)))
               { σ with usedProphId := σ.usedProphId.insert p } []
  | resolveS (p : ProphId) (v : Val) (e : Exp) (σ : State) (w : Val) (σ' : State)
             (κs : List Observation) (ts : List Exp) :
      BaseStep e σ κs (.ofVal v) σ' ts →
      σ.usedProphId.contains p →
      BaseStep (.resolve e (.ofVal (.lit (.prophecy p))) (.ofVal w)) σ
               (κs ++ [(p, (v, w))]) (.ofVal v) σ' ts

end Iris.HeapLang
