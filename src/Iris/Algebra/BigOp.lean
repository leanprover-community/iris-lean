/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Zongyuan Liu
-/
import Iris.Algebra.Monoid

namespace Iris.Algebra

/-! # Big Operators

This file defines big operators (fold operations) over lists at the abstract OFE level.
These are parameterized by a monoid operation and include theorems about their properties.

The key definitions are:
- `bigOpL`: Indexed fold over lists with index access
-/

open OFE

/-! ## Big Operators -/

/-- Indexed fold over a list. The function `Φ` receives the index and element.
This is the generic version parameterized by the monoid operation and unit. -/
def bigOpL {M : Type u} {A : Type v} (op : M → M → M) (unit : M)
    (Φ : Nat → A → M) (l : List A) : M :=
  match l with
  | [] => unit
  | x :: xs => op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs)

namespace BigOpL

variable {M : Type u} {A : Type v} [OFE M] {op : M → M → M} {unit : M} [Monoid M op unit]

/-! ### Basic lemmas -/

omit [OFE M] [Monoid M op unit] in
@[simp] theorem nil (Φ : Nat → A → M) :
    bigOpL op unit Φ ([] : List A) = unit := rfl

omit [OFE M] [Monoid M op unit] in
@[simp] theorem cons (Φ : Nat → A → M) (x : A) (xs : List A) :
    bigOpL op unit Φ (x :: xs) = op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs) := rfl

@[simp] theorem singleton (Φ : Nat → A → M) (x : A) :
    bigOpL op unit Φ [x] ≡ Φ 0 x := by
  simp only [cons, nil]
  exact Monoid.op_right_id _

/-! ### Congruence lemmas -/

/-- Congruence for bigOpL: if Φ and Ψ are pointwise equivalent on the list, the results are equivalent. -/
theorem congr {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x ≡ Ψ i x) :
    bigOpL op unit Φ l ≡ bigOpL op unit Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => exact Equiv.rfl
  | cons y ys ih =>
    simp only [cons]
    have h0 : Φ 0 y ≡ Ψ 0 y := h 0 y rfl
    have htail : ∀ i x, ys[i]? = some x → Φ (i + 1) x ≡ Ψ (i + 1) x := by
      intro i x hget
      exact h (i + 1) x hget
    exact Monoid.op_proper h0 (ih htail)

/-- Non-expansive version of congruence. -/
theorem congr_ne {Φ Ψ : Nat → A → M} {l : List A} {n : Nat}
    (h : ∀ i x, l[i]? = some x → Φ i x ≡{n}≡ Ψ i x) :
    bigOpL op unit Φ l ≡{n}≡ bigOpL op unit Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => exact Dist.rfl
  | cons y ys ih =>
    simp only [cons]
    have h0 : Φ 0 y ≡{n}≡ Ψ 0 y := h 0 y rfl
    have htail : ∀ i x, ys[i]? = some x → Φ (i + 1) x ≡{n}≡ Ψ (i + 1) x := by
      intro i x hget
      exact h (i + 1) x hget
    exact Monoid.op_ne_dist h0 (ih htail)

/-- Simplified congruence when the functions are equivalent on all indices. -/
theorem congr' {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, Φ i x ≡ Ψ i x) :
    bigOpL op unit Φ l ≡ bigOpL op unit Ψ l :=
  congr (fun i x _ => h i x)

/-! ### Append and snoc -/

theorem append (Φ : Nat → A → M) (l₁ l₂ : List A) :
    bigOpL op unit Φ (l₁ ++ l₂) ≡
      op (bigOpL op unit Φ l₁) (bigOpL op unit (fun n => Φ (n + l₁.length)) l₂) := by
  induction l₁ generalizing Φ with
  | nil => simp only [nil]; exact Equiv.symm (Monoid.op_left_id _)
  | cons x xs ih =>
    simp only [List.cons_append, cons, List.length_cons]
    have ih' := ih (fun n => Φ (n + 1))
    have heq : ∀ n, n + xs.length + 1 = n + (xs.length + 1) := fun n => by omega
    calc op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) (xs ++ l₂))
        _ ≡ op (Φ 0 x) (op (bigOpL op unit (fun n => Φ (n + 1)) xs)
              (bigOpL op unit (fun n => Φ (n + xs.length + 1)) l₂)) :=
            Monoid.op_congr_r ih'
        _ ≡ op (op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs))
              (bigOpL op unit (fun n => Φ (n + xs.length + 1)) l₂) :=
            Equiv.symm (Monoid.op_assoc _ _ _)
        _ ≡ op (op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs))
              (bigOpL op unit (fun n => Φ (n + (xs.length + 1))) l₂) := by
            simp only [heq]; exact Equiv.rfl

theorem snoc (Φ : Nat → A → M) (l : List A) (x : A) :
    bigOpL op unit Φ (l ++ [x]) ≡ op (bigOpL op unit Φ l) (Φ l.length x) := by
  have h := @append M A _ op unit _ Φ l [x]
  simp only [cons, nil, Nat.zero_add] at h
  have hr : op (Φ l.length x) unit ≡ Φ l.length x := Monoid.op_right_id (Φ l.length x)
  exact Monoid.op_congr_r hr |> Equiv.trans h

/-! ### Unit lemma -/

/-- Big op over constant unit collapses to unit. -/
theorem unit_const (l : List A) :
    bigOpL op unit (fun _ _ => unit) l ≡ unit := by
  induction l with
  | nil => exact Equiv.rfl
  | cons _ _ ih => simp only [cons]; exact Equiv.trans (Monoid.op_left_id _) ih

/-! ### Distribution over op -/

/-- Distribution of big op over the monoid operation. -/
theorem op_distr (Φ Ψ : Nat → A → M) (l : List A) :
    bigOpL op unit (fun i x => op (Φ i x) (Ψ i x)) l ≡
      op (bigOpL op unit Φ l) (bigOpL op unit Ψ l) := by
  induction l generalizing Φ Ψ with
  | nil => simp only [nil]; exact Equiv.symm (Monoid.op_left_id _)
  | cons x xs ih =>
    simp only [cons]
    exact Equiv.trans (Monoid.op_congr_r (ih _ _)) Monoid.op_op_swap

/-! ### Map/fmap -/

/-- Big op over mapped list equals big op with composed function. -/
theorem fmap {B : Type v} (h : A → B) (Φ : Nat → B → M) (l : List A) :
    bigOpL op unit Φ (l.map h) ≡ bigOpL op unit (fun i x => Φ i (h x)) l := by
  induction l generalizing Φ with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, cons]
    exact Monoid.op_proper Equiv.rfl (ih (fun n => Φ (n + 1)))

/-! ### Closure under predicates -/

omit [OFE M] [Monoid M op unit] in
/-- Property `P` is preserved by big op if it holds for unit and is closed under `op`. -/
theorem closed (P : M → Prop) (Φ : Nat → A → M) (l : List A)
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ i x, l[i]? = some x → P (Φ i x)) :
    P (bigOpL op unit Φ l) := by
  induction l generalizing Φ with
  | nil => exact hunit
  | cons y ys ih =>
    simp only [cons]
    have h0 : P (Φ 0 y) := hf 0 y rfl
    have htail : ∀ i x, ys[i]? = some x → P (Φ (i + 1) x) := fun i x hget => hf (i + 1) x hget
    exact hop _ _ h0 (ih _ htail)

/-! ### Permutation -/

/-- Big operators over commutative monoids are invariant under permutation.
Note: This uses definitional equality on elements, not the monoid equivalence. -/
theorem perm (Φ : A → M) {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    bigOpL op unit (fun _ => Φ) l₁ ≡ bigOpL op unit (fun _ => Φ) l₂ := by
  induction hp with
  | nil => exact Equiv.rfl
  | cons _ _ ih => simp only [cons]; exact Monoid.op_congr_r ih
  | swap _ _ _ => simp only [cons]; exact Monoid.op_swap_inner (unit := unit)
  | trans _ _ ih1 ih2 => exact Equiv.trans ih1 ih2

/-! ### Take and drop -/

/-- Split big op at position `n`. -/
theorem take_drop (Φ : Nat → A → M) (l : List A) (n : Nat) :
    bigOpL op unit Φ l ≡
      op (bigOpL op unit Φ (l.take n)) (bigOpL op unit (fun k => Φ (n + k)) (l.drop n)) := by
  by_cases hn : n ≤ l.length
  · have h := @append M A _ op unit _ Φ (l.take n) (l.drop n)
    simp only [List.take_append_drop, List.length_take_of_le hn, Nat.add_comm] at h
    exact h
  · simp only [Nat.not_le] at hn
    simp only [List.drop_eq_nil_of_le (Nat.le_of_lt hn), List.take_of_length_le (Nat.le_of_lt hn), nil]
    exact Equiv.symm (Monoid.op_right_id _)

/-! ### Extensional equality -/

omit [OFE M] [Monoid M op unit] in
/-- Extensional equality (propositional, not just equivalence). -/
theorem ext {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x = Ψ i x) :
    bigOpL op unit Φ l = bigOpL op unit Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => rfl
  | cons y ys ih =>
    simp only [cons]
    have h0 : Φ 0 y = Ψ 0 y := h 0 y rfl
    have htail : ∀ i x, ys[i]? = some x → Φ (i + 1) x = Ψ (i + 1) x :=
      fun i x hget => h (i + 1) x hget
    rw [h0, ih htail]

/-! ### FilterMap (omap) -/

/-- Big op over `filterMap` (called `omap` in Rocq). -/
theorem filterMap {B : Type v} (h : A → Option B) (Φ : B → M) (l : List A) :
    bigOpL op unit (fun _ => Φ) (l.filterMap h) ≡
      bigOpL op unit (fun _ x => (h x).elim unit Φ) l := by
  induction l with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    cases hx : h x <;> simp only [hx, Option.elim, cons]
    · exact Equiv.trans ih (Equiv.symm (Monoid.op_left_id _))
    · exact Monoid.op_congr_r ih

/-! ### Bind (flatMap) -/

/-- Big op over flattened list equals nested big op. -/
theorem bind {B : Type v} (h : A → List B) (Φ : B → M) (l : List A) :
    bigOpL op unit (fun _ => Φ) (l.flatMap h) ≡
      bigOpL op unit (fun _ x => bigOpL op unit (fun _ => Φ) (h x)) l := by
  induction l with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, cons]
    exact Equiv.trans (append _ _ _) (Monoid.op_congr_r ih)

/-! ### Sep zip -/

/-- Big op over zipped list with separated functions. -/
theorem sep_zip {B : Type v} (Φ : Nat → A → M) (Ψ : Nat → B → M) (l₁ : List A) (l₂ : List B)
    (hlen : l₁.length = l₂.length) :
    bigOpL op unit (fun i xy => op (Φ i xy.1) (Ψ i xy.2)) (l₁.zip l₂) ≡
      op (bigOpL op unit Φ l₁) (bigOpL op unit Ψ l₂) := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simp only [List.zip_nil_left, nil]; exact Equiv.symm (Monoid.op_left_id _)
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zip_cons_cons, cons]
      exact Equiv.trans (Monoid.op_congr_r (ih (fun n => Φ (n + 1)) (fun n => Ψ (n + 1)) ys hlen)) Monoid.op_op_swap

/-! ### Nested iterations commute -/

/-- Nested list iterations commute. -/
theorem opL_opL {B : Type v} (Φ : Nat → A → Nat → B → M) (l₁ : List A) (l₂ : List B) :
    bigOpL op unit (fun i x => bigOpL op unit (fun j y => Φ i x j y) l₂) l₁ ≡
      bigOpL op unit (fun j y => bigOpL op unit (fun i x => Φ i x j y) l₁) l₂ := by
  induction l₁ generalizing Φ with
  | nil => simp only [nil]; exact Equiv.symm (unit_const _)
  | cons x xs ih =>
    simp only [cons]
    exact Equiv.trans (Monoid.op_congr_r (ih _)) (Equiv.symm (op_distr _ _ _))

/-! ### Generic proper across two lists -/

omit [OFE M] [Monoid M op unit] in
/-- Generic proper lemma across two potentially different lists.
    If the relation R holds for unit, is proper for op, and holds pointwise
    between elements at matching indices, then R holds for the big ops. -/
theorem gen_proper_2 {B : Type v} (R : M → M → Prop)
    (Φ : Nat → A → M) (Ψ : Nat → B → M) (l₁ : List A) (l₂ : List B)
    (hunit : R unit unit)
    (hop : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hlen : l₁.length = l₂.length)
    (hf : ∀ i, ∀ x y, l₁[i]? = some x → l₂[i]? = some y → R (Φ i x) (Ψ i y)) :
    R (bigOpL op unit Φ l₁) (bigOpL op unit Ψ l₂) := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simp only [nil]; exact hunit
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [cons]
      have h0 : R (Φ 0 x) (Ψ 0 y) := hf 0 x y rfl rfl
      have htail : ∀ i, ∀ a b, xs[i]? = some a → ys[i]? = some b →
          R (Φ (i + 1) a) (Ψ (i + 1) b) := fun i a b ha hb => hf (i + 1) a b ha hb
      exact hop _ _ _ _ h0 (ih (fun n => Φ (n + 1)) (fun n => Ψ (n + 1)) ys hlen htail)

/-! ### Zip with sequence -/

/-- Big op over zip with a shifted sequence. -/
theorem zip_seq (Φ : Nat × A → M) (n : Nat) (l : List A) :
    bigOpL op unit (fun _ => Φ) ((List.range' n l.length).zip l) ≡
      bigOpL op unit (fun i x => Φ (n + i, x)) l := by
  induction l generalizing n with
  | nil => simp only [List.length_nil, List.range'_zero, List.zip_nil_left, nil]; exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, cons, Nat.add_zero]
    refine Monoid.op_proper Equiv.rfl (Equiv.trans (ih (n + 1)) (congr' fun i _ => ?_))
    simp only [Nat.add_assoc, Nat.add_comm 1 i]; exact Equiv.rfl

/-- Big op over zip with a sequence starting at 0. -/
theorem zip_with_range (Φ : Nat × A → M) (l : List A) :
    bigOpL op unit (fun _ => Φ) ((List.range l.length).zip l) ≡
      bigOpL op unit (fun i x => Φ (i, x)) l := by
  have h := @zip_seq M A _ op unit _ Φ 0 l
  simp only [Nat.zero_add] at h
  have heq : List.range l.length = List.range' 0 l.length := List.range_eq_range' (n := l.length)
  rw [heq]
  exact h

/-! ### Sep zip with custom zip function -/

/-- Generalized version of `sep_zip` with custom zip function. -/
theorem sep_zip_with {B C : Type v}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (Φ : Nat → A → M) (Ψ : Nat → B → M) (l₁ : List A) (l₂ : List B)
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hlen : l₁.length = l₂.length) :
    bigOpL op unit (fun i c => op (Φ i (g1 c)) (Ψ i (g2 c))) (List.zipWith f l₁ l₂) ≡
      op (bigOpL op unit Φ l₁) (bigOpL op unit Ψ l₂) := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simp only [List.zipWith_nil_left, nil]; exact Equiv.symm (Monoid.op_left_id _)
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, cons, hg1, hg2]
      exact Equiv.trans (Monoid.op_congr_r (ih (fun n => Φ (n + 1)) (fun n => Ψ (n + 1)) ys hlen)) Monoid.op_op_swap

/-! ### Homomorphism lemmas -/

variable {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
variable {op₁ : M₁ → M₁ → M₁} {op₂ : M₂ → M₂ → M₂} {unit₁ : M₁} {unit₂ : M₂}
variable [Monoid M₁ op₁ unit₁] [Monoid M₂ op₂ unit₂]
variable {B : Type w}

/-- Monoid homomorphisms distribute over big ops. -/
theorem commute {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : MonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : Nat → B → M₁) (l : List B) :
    R (f (bigOpL op₁ unit₁ Φ l)) (bigOpL op₂ unit₂ (fun i x => f (Φ i x)) l) := by
  induction l generalizing Φ with
  | nil => simp only [nil]; exact hom.map_unit
  | cons x xs ih =>
    simp only [cons]
    have hhom := hom.homomorphism (Φ 0 x) (bigOpL op₁ unit₁ (fun n => Φ (n + 1)) xs)
    have hih := ih (fun n => Φ (n + 1))
    exact hom.rel_trans hhom (hom.op_proper (hom.rel_refl _) hih)

/-- Weak monoid homomorphisms distribute over non-empty big ops. -/
theorem commute_weak {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : WeakMonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : Nat → B → M₁) (l : List B) (hne : l ≠ []) :
    R (f (bigOpL op₁ unit₁ Φ l)) (bigOpL op₂ unit₂ (fun i x => f (Φ i x)) l) := by
  induction l generalizing Φ with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    simp only [cons]
    cases xs with
    | nil =>
      simp only [nil]
      -- Goal: R (f (op₁ (Φ 0 x) unit₁)) (op₂ (f (Φ 0 x)) unit₂)
      -- We have: op₁ (Φ 0 x) unit₁ ≡ Φ 0 x and op₂ (f (Φ 0 x)) unit₂ ≡ f (Φ 0 x)
      -- So we use rel_proper to reduce to R (f (Φ 0 x)) (f (Φ 0 x)) which is rel_refl
      haveI : NonExpansive f := hom.f_ne
      have hlhs : f (op₁ (Φ 0 x) unit₁) ≡ f (Φ 0 x) :=
        NonExpansive.eqv (Monoid.op_right_id (Φ 0 x))
      have hrhs : op₂ (f (Φ 0 x)) unit₂ ≡ f (Φ 0 x) :=
        Monoid.op_right_id (f (Φ 0 x))
      exact hom.rel_proper hlhs hrhs |>.mpr (hom.rel_refl _)
    | cons y ys =>
      have hhom := hom.homomorphism (Φ 0 x) (bigOpL op₁ unit₁ (fun n => Φ (n + 1)) (y :: ys))
      have hih := ih (fun n => Φ (n + 1)) (List.cons_ne_nil y ys)
      exact hom.rel_trans hhom (hom.op_proper (hom.rel_refl _) hih)

end BigOpL

end Iris.Algebra
