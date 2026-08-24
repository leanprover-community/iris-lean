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
public import Iris.Std.PartialMap
public import Iris.Std.HeapInstances
import Iris.Std.List

@[expose] public section
namespace Iris.HeapLang

open Std

@[rocq_alias heap_lang.heap_lang.ectx_item]
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

@[rocq_alias heap_lang.heap_lang.fill_item]
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

@[rocq_alias heap_lang.heap_lang.state]
structure State where
  heap : Std.ExtTreeMap Loc (Option Val)
  usedProphId : Std.ExtTreeSet ProphId

instance : Inhabited State := ⟨.empty, .empty⟩

attribute [rocq_alias heap_lang.heap_lang.state_inhabited] instInhabitedState

-- Rocq threads state updates through the two `state_upd_*` functions; in Lean that role is
-- played by record-update syntax, as in `State.initHeap` below.
#rocq_ignore heap_lang.heap_lang.state_upd_heap
  "Lean updates the `State` record directly: `{ σ with heap := f σ.heap }`."
#rocq_ignore heap_lang.heap_lang.state_upd_used_proph_id
  "Lean updates the `State` record directly: `{ σ with usedProphId := f σ.usedProphId }`."
#rocq_ignore heap_lang.heap_lang.stateO
  "Canonical Leibniz OFE on `state`; Lean uses the generic `stateO State`, i.e. `DiscreteO State`."

@[rocq_alias heap_lang.heap_lang.observation]
abbrev Observation := ProphId × (Val × Val)

@[rocq_alias heap_lang.heap_lang.un_op_eval]
def UnOp.eval : UnOp → Val → Option Val
  | .neg,   .lit (.bool b) => some (.lit (.bool (!b)))
  | .neg,   .lit (.int n)  => some (.lit (.int (~~~n)))
  | .minus, .lit (.int n)  => some (.lit (.int (-n)))
  | _,      _              => none

/-- Binary operations on two integer literals. `BinOp.eval` agrees with this on integers
(`BinOp.eval_lit_int`); `.eq` is listed here because Rocq's `bin_op_eval_int` does, even though
`BinOp.eval` routes equality through `Val.compareSafe`. -/
@[rocq_alias heap_lang.heap_lang.bin_op_eval_int]
def BinOp.evalInt : BinOp → Int → Int → Option BaseLit
  | .plus,   n1, n2 => some (.int (n1 + n2))
  | .minus,  n1, n2 => some (.int (n1 - n2))
  | .mult,   n1, n2 => some (.int (n1 * n2))
  | .tdiv,   n1, n2 => some (.int (n1.tdiv n2))
  | .tmod,   n1, n2 => some (.int (n1.tmod n2))
  | .and,    n1, n2 => some (.int (n1 &&& n2))
  | .or,     n1, n2 => some (.int (n1 ||| n2))
  | .xor,    n1, n2 => some (.int (n1 ^^^ n2))
  | .shiftl, n1, n2 => some (.int (n1 <<< n2))
  | .shiftr, n1, n2 => some (.int (n1 >>> n2))
  | .le,     n1, n2 => some (.bool (n1 ≤ n2))
  | .lt,     n1, n2 => some (.bool (n1 < n2))
  | .eq,     n1, n2 => some (.bool (n1 = n2))
  | .offset, _,  _  => none -- Pointer arithmetic

/-- Binary operations on two boolean literals; see `BinOp.eval_lit_bool`. -/
@[rocq_alias heap_lang.heap_lang.bin_op_eval_bool]
def BinOp.evalBool : BinOp → Bool → Bool → Option BaseLit
  | .and, b1, b2 => some (.bool (b1 && b2))
  | .or,  b1, b2 => some (.bool (b1 || b2))
  | .xor, b1, b2 => some (.bool (b1 ^^ b2))
  | .eq,  b1, b2 => some (.bool (b1 == b2))
  | _,    _,  _  => none

/-- Binary operations whose left argument is a location: pointer arithmetic and the comparison
of two locations. See `BinOp.eval_lit_loc`. -/
@[rocq_alias heap_lang.heap_lang.bin_op_eval_loc]
def BinOp.evalLoc : BinOp → Loc → BaseLit → Option BaseLit
  | .offset, l1, .int off => some (.loc (l1 + off))
  | .le,     l1, .loc l2  => some (.bool (l1 ≤ l2))
  | .lt,     l1, .loc l2  => some (.bool (l1 < l2))
  | _,       _,  _        => none

@[rocq_alias heap_lang.heap_lang.bin_op_eval]
def BinOp.eval (op : BinOp) (v1 v2 : Val) : Option Val :=
  if op = .eq then
    if v1.compareSafe v2 then some (.lit (.bool (v1 == v2))) else none
  else
    match v1, v2 with
    | .lit (.int n1), .lit (.int n2) => Val.lit <$> op.evalInt n1 n2
    | .lit (.bool b1), .lit (.bool b2) => Val.lit <$> op.evalBool b1 b2
    | .lit (.loc l1), .lit lit2 => Val.lit <$> op.evalLoc l1 lit2
    | _, _ => none

theorem BinOp.eval_lit_int (op : BinOp) (n1 n2 : Int) :
    BinOp.eval op (.lit (.int n1)) (.lit (.int n2)) = (Val.lit <$> op.evalInt n1 n2) := by
  cases op <;> simp [BinOp.eval, BinOp.evalInt, Val.compareSafe, BaseLit.isUnboxed, Val.isUnboxed]
    <;> by_cases h : n1 = n2 <;> simp [h]

theorem BinOp.eval_lit_bool (op : BinOp) (b1 b2 : Bool) :
    BinOp.eval op (.lit (.bool b1)) (.lit (.bool b2)) = (Val.lit <$> op.evalBool b1 b2) := by
  cases b1 <;> cases b2 <;> cases op <;> rfl

/-- Unlike the integer and boolean cases, this one needs `op ≠ .eq`: Rocq's `bin_op_eval`
dispatches `EqOp` before it ever reaches `bin_op_eval_loc`, and `BinOp.eval` likewise routes
equality of two locations through `Val.compareSafe`. -/
theorem BinOp.eval_lit_loc (op : BinOp) (l : Loc) (lit : BaseLit) (hop : op ≠ .eq) :
    BinOp.eval op (.lit (.loc l)) (.lit lit) = (Val.lit <$> op.evalLoc l lit) := by
  cases op <;> cases lit <;> simp_all [BinOp.eval, BinOp.evalLoc]

abbrev HeapF := fun V => Std.ExtTreeMap Loc V compare

@[rocq_alias heap_lang.heap_lang.state_init_heap]
abbrev State.initHeap (σ : State) (l : Loc) (n : Int) (v : Option Val) : State :=
  { σ with heap := (List.range n.toNat).foldl
            (fun h (i : Nat) => Std.insert (M := HeapF) h (l + (i : Int)) v) σ.heap }

abbrev State.get? (σ : State) (l : Loc) : Option (Option Val) :=
    PartialMap.get? (M := HeapF) σ.heap l

/-! ### Multi-cell allocation -/

@[rocq_alias heap_lang.heap_lang.heap_array]
def heapArray (l : Loc) (vs : List (Option Val)) : HeapF (Option Val) :=
  match vs with
  | .nil => ∅
  | v :: vs' => Std.insert (M := HeapF) (heapArray (l + (1 : Int)) vs') l v

abbrev allocCells (l : Loc) (n : Nat) (v : Option Val) : HeapF (Option Val) :=
  heapArray l (List.replicate n v)

@[simp]
theorem heapArray_nil {l : Loc} : heapArray l [] = (∅ : HeapF (Option Val)) := rfl

@[rocq_alias heap_lang.heap_lang.heap_array_singleton]
theorem heapArray_singleton {l : Loc} : heapArray l [v] = PartialMap.singleton l v := rfl

theorem heapArray_snoc {l : Loc} {vs : List (Option Val)} {v : Option Val} :
    heapArray l (vs ++ [v]) =
      Std.insert (M := HeapF) (heapArray l vs) (l + (vs.length : Int)) v := by
  induction vs generalizing l with
  | nil => simp [heapArray]
  | cons w vs ih =>
    simp only [List.cons_append, heapArray, List.length_cons]
    rw [ih, Std.LawfulPartialMap.insert_insert_comm]
    · congr 1
      rw [loc_add_assoc]
      congr 1
      omega
    · intro h
      have := congrArg Loc.n h
      simp only [loc_add_n] at this
      omega

@[rocq_alias heap_lang.heap_lang.heap_array_lookup]
theorem get?_heapArray {l : Loc} {vs : List (Option Val)} {ow : Option Val} {k : Loc} :
    PartialMap.get? (M := HeapF) (heapArray l vs) k = some ow ↔
      ∃ j : Nat, k = l + (j : Int) ∧ vs[j]? = some ow := by
  induction vs generalizing l with
  | nil => simp [heapArray, Std.LawfulPartialMap.get?_empty]
  | cons v vs ih =>
    rw [heapArray, Std.LawfulPartialMap.get?_insert]
    have hadd (j : Nat) :
        l + (1 : Int) + (j : Int) = l + ((j + 1 : Nat) : Int) := by
      rw [loc_add_assoc, Int.add_comm (1 : Int)]
      congr 1
    constructor
    · split
      · rename_i hlk
        intro how
        exact ⟨0, by simpa using hlk.symm, by simpa using how⟩
      · intro hget
        obtain ⟨j, hkj, hj⟩ := ih.mp hget
        exact ⟨j + 1, hkj.trans (hadd j), by simpa using hj⟩
    · rintro ⟨_ | j, hkj, hj⟩
      · rw [if_pos (by simpa using hkj.symm)]
        simpa using hj
      · rw [if_neg]
        · exact ih.mpr ⟨j, hkj.trans (hadd j).symm, by simpa using hj⟩
        · intro hlk
          have := congrArg Loc.n (hlk.trans hkj)
          simp only [loc_add_n] at this
          omega

@[rocq_alias heap_lang.heap_lang.heap_array_map_disjoint]
theorem heapArray_disjoint {l : Loc} {vs : List (Option Val)} {m : HeapF (Option Val)}
    (hf : ∀ i : Int, 0 ≤ i → i < (vs.length : Int) →
      PartialMap.get? (M := HeapF) m (l + i) = none) :
    PartialMap.disjoint (M := HeapF) (heapArray l vs) m := by
  intro k ⟨h1, h2⟩
  rcases hget : PartialMap.get? (M := HeapF) (heapArray l vs) k with _ | ow
  · simp [hget] at h1
  · obtain ⟨i, hki, hvi⟩ := get?_heapArray.mp hget
    have hi := (List.getElem?_eq_some_iff.mp hvi).1
    rw [hki, hf (i : Int) (Int.natCast_nonneg i) (by omega)] at h2
    simp at h2

theorem get?_heapArray_self {l : Loc} {vs : List (Option Val)} :
    PartialMap.get? (M := HeapF) (heapArray l vs) (l + (vs.length : Int)) = none := by
  rcases hget : PartialMap.get? (M := HeapF) (heapArray l vs)
    (l + (vs.length : Int)) with _ | ow
  · rfl
  · obtain ⟨i, hik, hvi⟩ := get?_heapArray.mp hget
    have hi := (List.getElem?_eq_some_iff.mp hvi).1
    exact False.elim (Nat.ne_of_lt hi (Int.ofNat_inj.mp (loc_add_inj hik).symm))

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
  by_cases h : ∃ i, i < n ∧ k = l + (i : Int)
  · rw [if_pos h]
    obtain ⟨i, hi, hki⟩ := h
    apply get?_heapArray.mpr
    exact ⟨i, hki, List.getElem?_replicate_of_lt hi⟩
  · rw [if_neg h]
    rcases hget : PartialMap.get? (M := HeapF) (allocCells l n v) k with _ | ow
    · rfl
    · obtain ⟨i, hki, hvi⟩ := get?_heapArray.mp hget
      have hi := (List.getElem?_eq_some_iff.mp hvi).1
      exact False.elim (h ⟨i, by simpa using hi, hki⟩)

@[simp]
theorem allocCells_zero {l : Loc} {v : Option Val} : allocCells l 0 v = ∅ := rfl

/-- `allocCells` peels off its *last* cell. -/
theorem allocCells_succ {l : Loc} {n : Nat} {v : Option Val} :
    allocCells l (n + 1) v = Std.insert (M := HeapF) (allocCells l n v) (l + (n : Int)) v := by
  rw [allocCells, List.replicate_succ', heapArray_snoc, List.length_replicate]

theorem get?_allocCells_self {l : Loc} {n : Nat} {v : Option Val} :
    PartialMap.get? (M := HeapF) (allocCells l n v) (l + (n : Int)) = none := by
  simpa [allocCells] using
    (get?_heapArray_self (l := l) (vs := List.replicate n v))

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
    Std.PartialMap.disjoint (M := HeapF) (allocCells l n.toNat v) m := by
  apply heapArray_disjoint
  intro i hi hin
  apply hf i hi
  simp only [List.length_replicate] at hin
  omega

theorem exists_fresh_block (m : HeapF (Option Val)) (n : Int) :
    ∃ l : Loc, ∀ i : Int, 0 ≤ i → i < n → PartialMap.get? (M := HeapF) m (l + i) = none := by
  refine ⟨Loc.mk ((m.keys.map Loc.n).foldr max 0 + 1), fun i hi0 hin => ?_⟩
  simp only [PartialMap.get?, getElem?_eq_none_iff, ← Std.ExtTreeMap.mem_keys]
  intro hmem
  have hle : (Loc.mk ((m.keys.map Loc.n).foldr max 0 + 1) + i).n ≤ (m.keys.map Loc.n).foldr max 0 :=
    List.mem_le_foldr_max _ _ (List.mem_map_of_mem hmem)
  simp only [loc_add_n] at hle
  grind

/-- Initializing a single cell is a plain insert. Rocq adds `h` on the right in
`state_init_heap` to make this hold; here it falls out of the `foldl`. -/
@[rocq_alias heap_lang.heap_lang.state_init_heap_singleton]
theorem State.initHeap_singleton {σ : State} {l : Loc} {v : Option Val} :
    σ.initHeap l 1 v = { σ with heap := Std.insert (M := HeapF) σ.heap l v } := by
  simp [State.initHeap]

/-- Writing back a cell's current contents leaves the state unchanged. -/
theorem State.initHeap_self {σ : State} {l : Loc} {v : Option Val}
    (h : PartialMap.get? (M := HeapF) σ.heap l = some v) : σ.initHeap l 1 v = σ := by
  have hins : Std.insert (M := HeapF) σ.heap l v = σ.heap := by
    refine Std.LawfulPartialMap.equiv_iff_eq.mp fun k => ?_
    rw [Std.LawfulPartialMap.get?_insert]
    split
    · next heq => exact heq ▸ h.symm
    · rfl
  simp only [State.initHeap, Int.toNat_one, List.range_one, List.foldl_cons, List.foldl_nil,
    Int.cast_ofNat_Int, loc_add_zero, hins]

@[rocq_alias heap_lang.heap_lang.base_step]
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

/-- Allocation always has a step available: `Loc.fresh` picks a block that the heap does not
use. -/
@[rocq_alias heap_lang.heap_lang.alloc_fresh]
theorem alloc_fresh (v : Val) (n : Int) (σ : State) (hn : 0 < n) :
    BaseStep (.allocN (.ofVal (.lit (.int n))) (.ofVal v)) σ []
      (.ofVal (.lit (.loc (Loc.fresh σ.heap.keys))))
      (σ.initHeap (Loc.fresh σ.heap.keys) n v) [] :=
  .allocNS n v σ _ hn fun i hi0 _ => by
    simpa [State.get?, PartialMap.get?, getElem?_eq_none_iff, ← Std.ExtTreeMap.mem_keys]
      using Loc.fresh_fresh _ hi0

@[rocq_alias heap_lang.heap_lang.new_proph_id_fresh]
theorem new_proph_id_fresh (σ : State) :
    ∃ p : ProphId, BaseStep .newProph σ []
      (.ofVal (.lit (.prophecy p))) { σ with usedProphId := σ.usedProphId.insert p } [] :=
  let ⟨p, hp⟩ := _root_.Iris.Std.List.fresh σ.usedProphId.toList
  ⟨p, .newProphS σ p (hp <| Std.ExtTreeSet.mem_toList.mpr <| Std.ExtTreeSet.mem_iff_contains.mpr ·)⟩

end Iris.HeapLang
