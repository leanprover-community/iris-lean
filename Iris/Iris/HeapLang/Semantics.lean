/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Linter
public import Std.Data.ExtTreeMap
public import Std.Data.ExtTreeSet
public import Iris.Std.BitOp
public import Iris.Std.RocqPorting
public import Iris.Std.PartialMap
public import Iris.Std.HeapInstances
import Iris.Std.List

@[expose] public section
namespace Iris.HeapLang

open Std

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

abbrev HeapF := fun V => Std.ExtTreeMap Loc V compare

abbrev State.initHeap (σ : State) (l : Loc) (n : Int) (v : Option Val) : State :=
  { σ with heap := (List.range n.toNat).foldl
            (fun h (i : Nat) => Std.insert (M := HeapF) h (l + (i : Int)) v) σ.heap }

abbrev State.get? (σ : State) (l : Loc) : Option (Option Val) :=
    PartialMap.get? (M := HeapF) σ.heap l

/-! ### Multi-cell allocation -/

def allocCells (l : Loc) (n : Nat) (v : Option Val) : HeapF (Option Val) :=
  (List.range n).foldl (fun h (i : Nat) => Std.insert (M := HeapF) h (l + (i : Int)) v) ∅

theorem get?_foldl_insert (l : Loc) (v : Option Val) (m : HeapF (Option Val)) (n : Nat) (k : Loc) :
    PartialMap.get? (M := HeapF) ((List.range n).foldl
        (fun h (i : Nat) => Std.insert (M := HeapF) h (l + (i : Int)) v) m) k
      = if (∃ i, i < n ∧ k = l + (i : Int)) then some v
        else PartialMap.get? (M := HeapF) m k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.LawfulPartialMap.get?_insert, ih]
    by_cases hk : (l + (n : Int)) = k
    · rw [if_pos hk, if_pos ⟨n, Nat.lt_succ_self n, hk.symm⟩]
    · rw [if_neg hk]
      by_cases hex : ∃ i, i < n ∧ k = l + (i : Int)
      · obtain ⟨i, hi, hki⟩ := hex
        rw [if_pos ⟨i, hi, hki⟩, if_pos ⟨i, Nat.lt_succ_of_lt hi, hki⟩]
      · grind

theorem get?_allocCells {l : Loc} {n : Nat} {v : Option Val} {k : Loc} :
    PartialMap.get? (M := HeapF) (allocCells l n v) k
      = if (∃ i, i < n ∧ k = l + (i : Int)) then some v else none := by
  simp [allocCells, get?_foldl_insert, Std.LawfulPartialMap.get?_empty]

theorem initHeap_heap_eq {σ : State} {l : Loc} {n : Int} {v : Option Val} :
    Std.PartialMap.equiv (M := HeapF) (σ.initHeap l n v).heap
      (Std.PartialMap.union (allocCells l n.toNat v) σ.heap) := by
  intro k
  show PartialMap.get? (M := HeapF) ((List.range n.toNat).foldl
      (fun h (i : Nat) => Std.insert (M := HeapF) h (l + (i : Int)) v) σ.heap) k = _
  rw [get?_foldl_insert, Std.PartialMap.union, Std.LawfulPartialMap.get?_merge, get?_allocCells]
  by_cases hex : ∃ i, i < n.toNat ∧ k = l + (i : Int)
  · simp only [if_pos hex]; cases PartialMap.get? (M := HeapF) σ.heap k <;> rfl
  · simp only [if_neg hex]; cases PartialMap.get? (M := HeapF) σ.heap k <;> rfl

theorem allocCells_disjoint {l : Loc} {n : Int} {v : Val} {m : HeapF (Option Val)}
    (hf : ∀ i : Int, 0 ≤ i → i < n → PartialMap.get? (M := HeapF) m (l + i) = none) :
    Std.PartialMap.disjoint (M := HeapF) (allocCells l n.toNat (some v)) m := by
  intro k ⟨h1, h2⟩
  rw [get?_allocCells] at h1
  split at h1 <;> rename_i hcond
  · obtain ⟨i, hi, hki⟩ := hcond
    rw [hki, hf (i : Int) (Int.natCast_nonneg i) (by omega)] at h2
    simp at h2
  · simp at h1

theorem exists_fresh_block (m : HeapF (Option Val)) (n : Int) :
    ∃ l : Loc, ∀ i : Int, 0 ≤ i → i < n → PartialMap.get? (M := HeapF) m (l + i) = none := by
  refine ⟨Loc.mk ((m.keys.map Loc.n).foldr max 0 + 1), fun i hi0 hin => ?_⟩
  simp only [PartialMap.get?, getElem?_eq_none_iff, ← Std.ExtTreeMap.mem_keys]
  intro hmem
  have hle : (Loc.mk ((m.keys.map Loc.n).foldr max 0 + 1) + i).n ≤ (m.keys.map Loc.n).foldr max 0 :=
    List.mem_le_foldr_max _ _ (List.mem_map_of_mem hmem)
  simp only [loc_add_n] at hle
  grind

/-- Writing back a cell's current contents leaves the state unchanged. -/
theorem State.initHeap_self {σ : State} {l : Loc} {v : Option Val}
    (h : PartialMap.get? (M := HeapF) σ.heap l = some v) : σ.initHeap l 1 v = σ := by
  have hl : l + (0 : Int) = l := by
    cases l
    simp only [HAdd.hAdd, Loc.mk.injEq]
    grind
  have hins : Std.insert (M := HeapF) σ.heap l v = σ.heap := by
    refine Std.LawfulPartialMap.equiv_iff_eq.mp fun k => ?_
    rw [Std.LawfulPartialMap.get?_insert]
    split
    · next heq => exact heq ▸ h.symm
    · rfl
  simp only [State.initHeap, Int.toNat_one, List.range_one, List.foldl_cons, List.foldl_nil,
    Int.cast_ofNat_Int, hl, hins]

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
