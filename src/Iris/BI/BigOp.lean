/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BI.BI
import Iris.BI.DerivedLaws
import Iris.BI.DerivedLawsLater
import Iris.Algebra.BigOp
import Iris.Std.FiniteMap

/-! # BI-Level Big Operators

Reference: `iris/bi/big_op.v`

Iterated separating conjunction over lists and finite maps, specialized from the
algebra-level `bigOpL` and `bigOpM` to the BI separation connective `∗` with
unit `emp`.

The list version `big_sepL Φ l` computes:

    Φ 0 x₀ ∗ Φ 1 x₁ ∗ ⋯ ∗ Φ (n-1) xₙ₋₁

The map version `big_sepM Φ m` computes the same over the key-value pairs of `m`,
in the order given by `toList`. Since `∗` is commutative and associative, the
result is independent of enumeration order (up to `⊣⊢`).

These are the main iteration primitives used throughout the Iris base logic:
- `wsat` uses `[∗ map]` to assert that every registered invariant is either
  open or closed
- Proof mode tactics decompose `[∗ list]` and `[∗ map]` goals via
  `big_sepM_insert`, `big_sepM_delete`, etc.

## Main Definitions

- `big_sepL` — iterated `∗` over a list with index: `[∗ list] i ↦ x ∈ l, Φ i x`
- `big_sepM` — iterated `∗` over a finite map: `[∗ map] k ↦ v ∈ m, Φ k v`

## Main Results

- `big_sepL_nil`, `big_sepL_cons` — computation rules
- `big_sepL_mono` — pointwise entailment lifts to the big sep
- `big_sepM_empty`, `big_sepM_insert`, `big_sepM_delete` — map operations
- `big_sepM_lookup_acc` — extract one entry with a restoration wand
- `big_sepM_sep` — distribute `∗` over `[∗ map]`
-/

namespace Iris.BI

open Iris.Algebra Iris.Std

variable {PROP : Type _} [BI PROP]

/-! ## Separating Conjunction Monoid -/

/-- `sep` / `emp` form a monoid on any BI, enabling use of `bigOpL` and `bigOpM`. -/
instance sepMonoid : Monoid PROP BIBase.sep (BIBase.emp : PROP) where
  op_ne := by
    -- non-expansiveness is inherited from the BI structure
    simpa using (BI.sep_ne (PROP := PROP))
  op_assoc := by
    -- associativity follows from the derived bi-entailment
    intro a b c
    exact equiv_iff.mpr (sep_assoc (P := a) (Q := b) (R := c))
  op_comm := by
    -- commutativity follows from the derived bi-entailment
    intro a b
    exact equiv_iff.mpr (sep_comm (P := a) (Q := b))
  op_left_id := by
    -- left identity is `emp_sep` as a bi-entailment
    intro a
    exact equiv_iff.mpr (emp_sep (P := a))

/-! ## List Big Sep -/

/-- Iterated separating conjunction over a list with index.
    `big_sepL Φ l = Φ 0 x₀ ∗ Φ 1 x₁ ∗ ⋯ ∗ Φ (n-1) xₙ₋₁` -/
def big_sepL {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL BIBase.sep BIBase.emp Φ l

/-! ### List Computation Rules -/

/-- Empty list gives `emp`. -/
@[simp] theorem big_sepL_nil {A : Type _} (Φ : Nat → A → PROP) :
    big_sepL Φ ([] : List A) = (BIBase.emp : PROP) := rfl

/-- Cons unfolds to head `∗` tail. -/
@[simp] theorem big_sepL_cons {A : Type _} (Φ : Nat → A → PROP) (x : A) (l : List A) :
    big_sepL Φ (x :: l) = BIBase.sep (Φ 0 x) (big_sepL (fun n => Φ (n + 1)) l) := rfl

/-- Singleton list gives just the element. -/
theorem big_sepL_singleton {A : Type _} (Φ : Nat → A → PROP) (x : A) :
    big_sepL Φ [x] ⊣⊢ Φ 0 x := by
  -- reduce to the algebraic singleton lemma and translate equivalence
  have h : big_sepL Φ [x] ≡ Φ 0 x := by
    -- unfold and use the singleton simplification
    simp [big_sepL]
  exact (equiv_iff (P := big_sepL Φ [x]) (Q := Φ 0 x)).1 h

/-! ### List Structural Lemmas -/

/-- Pointwise entailment lifts to the iterated separating conjunction. -/
theorem big_sepL_mono {A : Type _} {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x ⊢ Ψ i x) :
    big_sepL Φ l ⊢ big_sepL Ψ l := by
  -- prove by list induction using `sep_mono`
  induction l generalizing Φ Ψ with
  | nil =>
    -- both sides are `emp`
    simp [big_sepL_nil]
  | cons x xs ih =>
    -- use monotonicity for head and tail
    have hhead : Φ 0 x ⊢ Ψ 0 x := h 0 x rfl
    have htail : ∀ i y, xs[i]? = some y → Φ (i + 1) y ⊢ Ψ (i + 1) y := by
      -- shift indices for the tail
      intro i y hget
      exact h (i + 1) y hget
    have ht : big_sepL (fun n => Φ (n + 1)) xs ⊢ big_sepL (fun n => Ψ (n + 1)) xs := ih htail
    -- unfold the head and apply `sep_mono`
    simpa [big_sepL_cons] using sep_mono hhead ht

/-- Append distributes: `[∗ list](l₁ ++ l₂) ⊣⊢ [∗ list]l₁ ∗ [∗ list]l₂`. -/
theorem big_sepL_app {A : Type _} (Φ : Nat → A → PROP) (l₁ l₂ : List A) :
    big_sepL Φ (l₁ ++ l₂) ⊣⊢
      BIBase.sep (big_sepL Φ l₁) (big_sepL (fun n => Φ (n + l₁.length)) l₂) := by
  -- use the algebraic append lemma and translate equivalence
  have h : big_sepL Φ (l₁ ++ l₂) ≡
      BIBase.sep (big_sepL Φ l₁) (big_sepL (fun n => Φ (n + l₁.length)) l₂) := by
    simpa [big_sepL] using
      (BigOpL.append (op := BIBase.sep) (unit := (BIBase.emp : PROP)) Φ l₁ l₂)
  exact equiv_iff.mp h

/-- Distribute `∗` inside: `[∗ list](Φ ∗ Ψ) ⊣⊢ [∗ list]Φ ∗ [∗ list]Ψ`. -/
theorem big_sepL_sep {A : Type _} (Φ Ψ : Nat → A → PROP) (l : List A) :
    big_sepL (fun i x => BIBase.sep (Φ i x) (Ψ i x)) l ⊣⊢
      BIBase.sep (big_sepL Φ l) (big_sepL Ψ l) := by
  -- use the algebraic distributivity lemma and translate equivalence
  have h : big_sepL (fun i x => BIBase.sep (Φ i x) (Ψ i x)) l ≡
      BIBase.sep (big_sepL Φ l) (big_sepL Ψ l) := by
    simpa [big_sepL] using
      (BigOpL.op_distr (op := BIBase.sep) (unit := (BIBase.emp : PROP)) Φ Ψ l)
  exact equiv_iff.mp h

/-! ## Map Big Sep -/

variable {K : Type _} {V : Type _}
variable {M' : Type _ → Type _} [FiniteMap K M']

/-- Iterated separating conjunction over a finite map.
    `big_sepM Φ m = ∗_{(k,v) ∈ m} Φ k v` -/
def big_sepM (Φ : K → V → PROP) (m : M' V) : PROP :=
  BigOpM.bigOpM (op := BIBase.sep) (unit := (BIBase.emp : PROP)) Φ m

/-! ## Notation -/

syntax "[∗" "list]" ident " ↦ " ident " ∈ " term ", " term : term
syntax "[∗" "map]" ident " ↦ " ident " ∈ " term ", " term : term

macro_rules
  | `(iprop([∗ list] $i ↦ $x ∈ $l, $P)) =>
      ``(big_sepL (fun $i $x => iprop($P)) $l)
  | `(iprop([∗ map] $k ↦ $v ∈ $m, $P)) =>
      ``(big_sepM (fun $k $v => iprop($P)) $m)

/-! ### Map Structural Lemmas -/

/-- Distribute `∗` inside: `[∗ map](Φ ∗ Ψ) ⊣⊢ [∗ map]Φ ∗ [∗ map]Ψ`. -/
theorem big_sepM_sep (Φ Ψ : K → V → PROP) (m : M' V) :
    big_sepM (fun k v => BIBase.sep (Φ k v) (Ψ k v)) m ⊣⊢
      BIBase.sep (big_sepM Φ m) (big_sepM Ψ m) := by
  -- use the algebraic distributivity lemma and translate equivalence
  have h : big_sepM (fun k v => BIBase.sep (Φ k v) (Ψ k v)) m ≡
      BIBase.sep (big_sepM Φ m) (big_sepM Ψ m) := by
    simpa [big_sepM] using
      (BigOpM.op_distr (op := BIBase.sep) (unit := (BIBase.emp : PROP)) Φ Ψ m)
  exact equiv_iff.mp h

section
variable [DecidableEq K] [FiniteMapLaws K M']

/-! ### Map Computation Rules -/

/-- Empty map gives `emp`. -/
@[simp] theorem big_sepM_empty (Φ : K → V → PROP) :
    big_sepM Φ (∅ : M' V) = (BIBase.emp : PROP) := by
  -- unfold to the algebraic empty lemma
  simp [big_sepM]

section
variable [DecidableEq V]

/-- Insert into a map with a fresh key unfolds to entry `∗` rest. -/
theorem big_sepM_insert (Φ : K → V → PROP) (m : M' V) (i : K) (x : V)
    (h : get? m i = none) :
    big_sepM Φ (insert m i x) ⊣⊢
      BIBase.sep (Φ i x) (big_sepM Φ m) := by
  -- use the algebraic insert lemma and translate equivalence
  have h' : big_sepM Φ (insert m i x) ≡
      BIBase.sep (Φ i x) (big_sepM Φ m) := by
    simpa [big_sepM] using
      (BigOpM.insert (op := BIBase.sep) (unit := (BIBase.emp : PROP)) Φ m i x h)
  exact equiv_iff.mp h'

/-- Delete from a map: `big_sepM m ⊣⊢ Φ k v ∗ big_sepM (delete k m)`. -/
theorem big_sepM_delete (Φ : K → V → PROP) (m : M' V) (i : K) (x : V)
    (h : get? m i = some x) :
    big_sepM Φ m ⊣⊢ BIBase.sep (Φ i x) (big_sepM Φ (delete m i)) := by
  -- use the algebraic delete lemma and translate equivalence
  have h' : big_sepM Φ m ≡
      BIBase.sep (Φ i x) (big_sepM Φ (delete m i)) := by
    simpa [big_sepM] using
      (BigOpM.delete (op := BIBase.sep) (unit := (BIBase.emp : PROP)) Φ m i x h)
  exact equiv_iff.mp h'

/-- Pointwise entailment lifts to the iterated map conjunction. -/
theorem big_sepM_mono {Φ Ψ : K → V → PROP} {m : M' V}
    (h : ∀ k v, get? m k = some v → Φ k v ⊢ Ψ k v) :
    big_sepM Φ m ⊢ big_sepM Ψ m := by
  -- strengthen induction to carry pointwise entailments
  refine FiniteMapLaws.induction_on
    (P := fun m' => (∀ k v, get? m' k = some v → Φ k v ⊢ Ψ k v) →
      big_sepM Φ m' ⊢ big_sepM Ψ m') ?hemp ?hins m h
  case hemp =>
    -- empty map: both sides are `emp`
    intro _
    simp [big_sepM_empty]
  case hins =>
    intro i x m' hnone IH hmap
    -- split the inserted map into head and tail
    have hhead : Φ i x ⊢ Ψ i x := by
      -- apply the pointwise hypothesis at the new key
      exact hmap i x (by simp [FiniteMapLaws.get?_insert_same])
    have htail : ∀ k v, get? m' k = some v → Φ k v ⊢ Ψ k v := by
      -- restrict the pointwise hypothesis to the tail map
      intro k v hk
      by_cases hki : k = i
      · subst hki; rw [hnone] at hk; cases hk
      · have hne : i ≠ k := Ne.symm hki
        have hk' : get? (insert m' i x) k = some v := by
          simpa [FiniteMapLaws.get?_insert_ne m' i k x hne] using hk
        exact hmap k v hk'
    have ht : big_sepM Φ m' ⊢ big_sepM Ψ m' := IH htail
    -- reassemble with `sep_mono`
    refine (big_sepM_insert Φ m' i x hnone).1.trans ?_
    refine (sep_mono hhead ht).trans ?_
    exact (big_sepM_insert Ψ m' i x hnone).2

/-- Extract one entry from the big sep and get a wand to put it back.
    This is the key lemma for opening/closing invariants in `wsat`. -/
theorem big_sepM_lookup_acc {Φ : K → V → PROP} {m : M' V} {i : K} {x : V}
    (h : get? m i = some x) :
    big_sepM Φ m ⊢ BIBase.sep (Φ i x) (BIBase.wand (Φ i x) (big_sepM Φ m)) := by
  -- peel out the entry and repackage with a wand
  have hdelete := big_sepM_delete Φ m i x h
  refine hdelete.1.trans ?_
  have hwand : big_sepM Φ (delete m i) ⊢ BIBase.wand (Φ i x) (big_sepM Φ m) := by
    -- derive the wand from the reversed delete lemma
    refine wand_intro ?_
    exact sep_symm.trans hdelete.2
  -- combine head and wand
  exact sep_mono .rfl hwand

/-- Distribute `▷` over the map big sep. -/
theorem big_sepM_later {Φ : K → V → PROP} {m : M' V} [BIAffine PROP] :
    BIBase.later (big_sepM Φ m) ⊢ big_sepM (fun k v => BIBase.later (Φ k v)) m := by
  -- prove by map induction using `later_sep`
  refine FiniteMapLaws.induction_on
    (P := fun m' => BIBase.later (big_sepM Φ m') ⊢
      big_sepM (fun k v => BIBase.later (Φ k v)) m') ?hemp ?hins m
  case hemp =>
    -- empty map: `▷ emp ⊢ emp`
    simpa [big_sepM_empty] using (later_emp (PROP := PROP)).1
  case hins =>
    intro i x m' hnone IH
    -- rewrite both sides using insertion and push `later` through `∗`
    have hinsΦ := big_sepM_insert Φ m' i x hnone
    have hinsΨ := big_sepM_insert (fun k v => BIBase.later (Φ k v)) m' i x hnone
    refine (later_congr hinsΦ).1.trans ?_
    refine (later_sep).1.trans ?_
    refine (sep_mono .rfl IH).trans ?_
    exact hinsΨ.2

/-- Singleton map. -/
theorem big_sepM_singleton (Φ : K → V → PROP) (i : K) (x : V) :
    big_sepM Φ (FiniteMap.singleton i x : M' V) ⊣⊢ Φ i x := by
  -- use the algebraic singleton lemma and translate equivalence
  have h : big_sepM Φ (FiniteMap.singleton i x : M' V) ≡ Φ i x := by
    simpa [big_sepM] using
      (BigOpM.singleton (op := BIBase.sep) (unit := (BIBase.emp : PROP)) Φ i x)
  exact equiv_iff.mp h

/-- Union of disjoint maps. -/
theorem big_sepM_union (Φ : K → V → PROP) (m₁ m₂ : M' V)
    (h : m₁ ##ₘ m₂) :
    big_sepM Φ (m₁ ∪ m₂) ⊣⊢
      BIBase.sep (big_sepM Φ m₁) (big_sepM Φ m₂) := by
  -- use the algebraic union lemma and translate equivalence
  have h' : big_sepM Φ (m₁ ∪ m₂) ≡
      BIBase.sep (big_sepM Φ m₁) (big_sepM Φ m₂) := by
    simpa [big_sepM] using
      (BigOpM.union (op := BIBase.sep) (unit := (BIBase.emp : PROP)) Φ m₁ m₂ h)
  exact equiv_iff.mp h'

end
end

end Iris.BI
