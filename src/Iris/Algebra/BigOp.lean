/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Algebra.Monoid
import Iris.Std.FiniteMap

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

variable {M : Type _} {A : Type _} [OFE M] {op : M → M → M} {unit : M} [Monoid M op unit]

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

namespace BigOpM

open Iris.Std

variable {M : Type u} [OFE M] {op : M → M → M} {unit : M} [Monoid M op unit]
variable {M' : Type _ → Type _} {K : Type _} {V : Type _}
variable [DecidableEq K] [DecidableEq V] [FiniteMap K M'] [FiniteMapLaws K M']

/-- Big operator over finite maps. Corresponds to Rocq's `big_opM`.
    Definition: `big_opM o u f m := big_opL o u (λ _, uncurry f) (map_to_list m)` -/
def bigOpM (Φ : K → V → M) (m : M' V) : M :=
  bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList m)

omit [OFE M] [Monoid M op unit] [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_empty`.
    Rocq proof: `by rewrite big_opM_unseal /big_opM_def map_to_list_empty.` -/
@[simp] theorem empty (Φ : K → V → M) :
    bigOpM (op := op) (unit := unit) Φ (∅ : M' V) = unit := by
  simp only [bigOpM, FiniteMapLaws.map_to_list_empty, BigOpL.nil]

/-- Corresponds to Rocq's `big_opM_insert`.
    Rocq proof: `intros ?. by rewrite big_opM_unseal /big_opM_def map_to_list_insert.` -/
theorem insert (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    FiniteMap.get? m i = none →
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.insert m i x) ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ m) := by
  intro hi
  simp only [bigOpM]
  have hperm := FiniteMapLaws.map_to_list_insert m i x hi
  have heq : bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList (FiniteMap.insert m i x)) ≡
             bigOpL op unit (fun _ kv => Φ kv.1 kv.2) ((i, x) :: FiniteMap.toList m) :=
    BigOpL.perm _ hperm
  simp only [BigOpL.cons] at heq
  exact heq

/-- Corresponds to Rocq's `big_opM_delete`.
    Rocq proof:
    ```
    intros. rewrite -big_opM_insert ?lookup_delete_eq //.
    by rewrite insert_delete_id.
    ``` -/
theorem delete (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    FiniteMap.get? m i = some x →
    bigOpM (op := op) (unit := unit) Φ m ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ (FiniteMap.delete m i)) := by
  intro hi
  -- Follows Rocq proof: rewrite -big_opM_insert ?lookup_delete_eq // and insert_delete_id
  have heq := FiniteMapLaws.insert_delete_id m i x hi
  -- bigOpM Φ m = bigOpM Φ (insert (delete m i) i x)
  have : bigOpM (op := op) (unit := unit) Φ m = bigOpM (op := op) (unit := unit) Φ (FiniteMap.insert (FiniteMap.delete m i) i x) := by
    rw [heq]
  rw [this]
  -- Now apply big_opM_insert with lookup_delete_eq
  have hdelete := FiniteMapLaws.lookup_delete_eq m i
  exact insert Φ (FiniteMap.delete m i) i x hdelete

variable {A : Type w} [DecidableEq A]

/-- Corresponds to Rocq's `big_opM_gen_proper_2`. -/
theorem gen_proper_2 {B : Type w} [DecidableEq B] (R : M → M → Prop)
    (Φ : K → A → M) (Ψ : K → B → M) (m1 : M' A) (m2 : M' B)
    (hR_sub : ∀ x y, x ≡ y → R x y)
    (hR_equiv : Equivalence R)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hfg : ∀ k,
      match FiniteMap.get? m1 k, FiniteMap.get? m2 k with
      | some y1, some y2 => R (Φ k y1) (Ψ k y2)
      | none, none => True
      | _, _ => False) :
    R (bigOpM (op := op) (unit := unit) Φ m1) (bigOpM (op := op) (unit := unit) Ψ m2) := by
  refine FiniteMapLaws.map_ind
    (P := fun (m1' : M' A) => ∀ (m2' : M' B) (Φ' : K → A → M) (Ψ' : K → B → M),
      (∀ k, match FiniteMap.get? m1' k, FiniteMap.get? m2' k with
        | some y1, some y2 => R (Φ' k y1) (Ψ' k y2)
        | none, none => True
        | _, _ => False) →
      R (bigOpM (op := op) (unit := unit) Φ' m1') (bigOpM (op := op) (unit := unit) Ψ' m2'))
    ?hemp ?hins m1 m2 Φ Ψ hfg
  case hemp =>
    intro m2' Φ' Ψ' hfg'
    refine FiniteMapLaws.map_ind
      (P := fun (m2'' : M' B) => ∀ (Φ'' : K → A → M) (Ψ'' : K → B → M),
        (∀ k, match FiniteMap.get? (∅ : M' A) k, FiniteMap.get? m2'' k with
          | some y1, some y2 => R (Φ'' k y1) (Ψ'' k y2)
          | none, none => True
          | _, _ => False) →
        R (bigOpM (op := op) (unit := unit) Φ'' (∅ : M' A)) (bigOpM (op := op) (unit := unit) Ψ'' m2''))
      ?hemp2 ?hins2 m2' Φ' Ψ' hfg'
    case hemp2 =>
      intro Φ'' Ψ'' _
      rw [empty, empty]
      exact hR_sub unit unit Equiv.rfl
    case hins2 =>
      intro k x2 m2'' hm2''k _ Φ'' Ψ'' hfg''
      have := hfg'' k
      rw [FiniteMapLaws.lookup_empty, FiniteMapLaws.lookup_insert_eq] at this
      cases this
  case hins =>
    intro k x1 m1' hm1'k IH m2' Φ' Ψ' hfg'
    have hfg_k := hfg' k
    rw [FiniteMapLaws.lookup_insert_eq] at hfg_k
    cases hm2k : FiniteMap.get? m2' k with
    | none =>
      rw [hm2k] at hfg_k
      cases hfg_k
    | some x2 =>
      rw [hm2k] at hfg_k
      have h_ins : bigOpM (op := op) (unit := unit) Φ' (FiniteMap.insert m1' k x1) ≡
                   op (Φ' k x1) (bigOpM (op := op) (unit := unit) Φ' m1') :=
        insert Φ' m1' k x1 hm1'k
      have h_del : op (Ψ' k x2) (bigOpM (op := op) (unit := unit) Ψ' (FiniteMap.delete m2' k)) ≡
                   bigOpM (op := op) (unit := unit) Ψ' m2' :=
        Equiv.symm (delete (op := op) (unit := unit) Ψ' m2' k x2 hm2k)
      have h_op : R (op (Φ' k x1) (bigOpM (op := op) (unit := unit) Φ' m1'))
                    (op (Ψ' k x2) (bigOpM (op := op) (unit := unit) Ψ' (FiniteMap.delete m2' k))) := by
        apply hR_op
        · exact hfg_k
        · apply IH
          intro k'
          by_cases hkk' : k = k'
          · subst hkk'
            rw [FiniteMapLaws.lookup_delete_eq, hm1'k]
            trivial
          · have h1 := FiniteMapLaws.lookup_insert_ne m1' k k' x1 hkk'
            have h2 := FiniteMapLaws.lookup_delete_ne m2' k k' hkk'
            rw [← h1, h2]
            exact hfg' k'
      exact hR_equiv.trans (hR_sub _ _ h_ins) (hR_equiv.trans h_op (hR_sub _ _ h_del))

omit [Monoid M op unit] [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_gen_proper`. -/
theorem gen_proper {M : Type u} {op : M → M → M} {unit : M} (R : M → M → Prop)
    (Φ Ψ : K → V → M) (m : M' V)
    (hR_refl : ∀ x, R x x)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ k x, FiniteMap.get? m k = some x → R (Φ k x) (Ψ k x)) :
    R (bigOpM (op := op) (unit := unit) Φ m) (bigOpM (op := op) (unit := unit) Ψ m) := by
  simp only [bigOpM]
  apply BigOpL.gen_proper_2 (op := op) (unit := unit) R
  · exact hR_refl unit
  · exact hR_op
  · rfl
  · intro i x y hx hy
    rw [hx] at hy
    cases hy
    have : (x.1, x.2) ∈ FiniteMap.toList m := by
      rw [List.mem_iff_getElem?]
      exact ⟨i, hx⟩
    have := FiniteMapLaws.elem_of_map_to_list m x.1 x.2 |>.mp this
    exact hf x.1 x.2 this

omit [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_ext`. -/
theorem ext {M : Type u} (op : M → M → M) (unit : M) (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, FiniteMap.get? m k = some x → Φ k x = Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m = bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· = ·))
  · intro _; rfl
  · intros _ _ _ _ ha hb; rw [ha, hb]
  · exact hf

omit [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_ne`. -/
theorem ne (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, FiniteMap.get? m k = some x → Φ k x ≡{n}≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡{n}≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· ≡{n}≡ ·))
  · intro _; exact Dist.rfl
  · intros a a' b b' ha hb; exact Monoid.op_ne_dist ha hb
  · exact hf

omit [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_proper`. -/
theorem proper (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, FiniteMap.get? m k = some x → Φ k x ≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· ≡ ·))
  · intro _; exact Equiv.rfl
  · intros a a' b b' ha hb; exact Monoid.op_proper ha hb
  · exact hf

omit [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_ne'` instance. -/
theorem ne_pointwise (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, Φ k x ≡{n}≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡{n}≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply ne
  intros k x _
  exact hf k x

omit [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_proper'` instance. -/
theorem proper_pointwise (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, Φ k x ≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply proper
  intros k x _
  exact hf k x

omit [Monoid M op unit] [DecidableEq K] [DecidableEq V] [FiniteMapLaws K M'] in
/-- Corresponds to Rocq's `big_opM_map_to_list`. -/
theorem map_to_list (Φ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ m ≡
    bigOpL op unit (fun _ kx => Φ kx.1 kx.2) (FiniteMap.toList m) := by
  simp only [bigOpM]
  rfl

/-- Corresponds to Rocq's `big_opM_list_to_map`. -/
theorem list_to_map (Φ : K → V → M) (l : List (K × V))
    (hnodup : (l.map Prod.fst).Nodup) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.ofList l : M' V) ≡
    bigOpL op unit (fun _ kx => Φ kx.1 kx.2) l := by
  have h1 := map_to_list (op := op) (unit := unit) Φ (FiniteMap.ofList l : M' V)
  apply Equiv.trans h1
  apply BigOpL.perm
  exact FiniteMapLaws.map_to_list_to_map l hnodup

/-- Corresponds to Rocq's `big_opM_singleton`. -/
theorem singleton (Φ : K → V → M) (i : K) (x : V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.insert (∅ : M' V) i x) ≡ Φ i x := by
  have : FiniteMap.get? (∅ : M' V) i = none := FiniteMapLaws.lookup_empty i
  have := insert (op := op) (unit := unit) Φ (∅ : M' V) i x this
  rw [empty] at this
  exact Equiv.trans this (Monoid.op_right_id (Φ i x))

/-- Corresponds to Rocq's `big_opM_unit`. -/
theorem unit_const (m : M' V) :
    bigOpM (op := op) (unit := unit) (fun _ _ => unit) m ≡ unit := by
  refine FiniteMapLaws.map_ind
    (P := fun (m' : M' V) => bigOpM (op := op) (unit := unit) (fun _ _ => unit) m' ≡ unit)
    ?hemp ?hins m
  case hemp =>
    show bigOpM (op := op) (unit := unit) (fun _ _ => unit) ∅ ≡ unit
    rw [empty]
  case hins =>
    intro i x m' hm' IH
    show bigOpM (op := op) (unit := unit) (fun _ _ => unit) (FiniteMap.insert m' i x) ≡ unit
    have h_ins := insert (op := op) (unit := unit) (fun _ _ => unit) m' i x hm'
    exact Equiv.trans h_ins (Equiv.trans (Monoid.op_proper Equiv.rfl IH) (Monoid.op_left_id unit))

omit [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_fmap`. -/
theorem fmap {B : Type w} [DecidableEq B] (h : V → B) (Φ : K → B → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.map h m) ≡
    bigOpM (op := op) (unit := unit) (fun k v => Φ k (h v)) m := by
  simp only [bigOpM]
  have h1 : bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList (FiniteMap.map h m)) ≡
            bigOpL op unit (fun _ kv => Φ kv.1 kv.2) ((FiniteMap.toList m).map (fun kv => (kv.1, h kv.2))) := by
    apply BigOpL.perm
    exact FiniteMapLaws.toList_map m h
  apply Equiv.trans h1
  -- Now use BigOpL.fmap to transform the mapped list
  exact BigOpL.fmap (op := op) (unit := unit) (fun kv => (kv.1, h kv.2)) (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList m)

omit [DecidableEq V] [DecidableEq K] [FiniteMapLaws K M'] in
/-- Corresponds to Rocq's `big_opM_op`. -/
theorem op_distr (Φ Ψ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) (fun k x => op (Φ k x) (Ψ k x)) m ≡
    op (bigOpM (op := op) (unit := unit) Φ m) (bigOpM (op := op) (unit := unit) Ψ m) := by
  simp only [bigOpM]
  have h := BigOpL.op_distr (op := op) (unit := unit)
    (fun _ kv => Φ kv.1 kv.2) (fun _ kv => Ψ kv.1 kv.2) (FiniteMap.toList m)
  exact h

/-- Corresponds to Rocq's `big_opM_closed`. -/
private theorem closed_aux (P : M → Prop) (Φ : K → V → M)
    (hproper : ∀ x y, x ≡ y → (P x ↔ P y))
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y)) :
    ∀ (m' : M' V), (∀ k' x', FiniteMap.get? m' k' = some x' → P (Φ k' x')) →
        P (bigOpM (op := op) (unit := unit) Φ m') := by
  intro m' hf'
  refine FiniteMapLaws.map_ind
    (P := fun m'' => (∀ k x, FiniteMap.get? m'' k = some x → P (Φ k x)) →
                     P (bigOpM (op := op) (unit := unit) Φ m''))
    ?hemp ?hins m' hf'
  case hemp =>
    intro _
    simp only [empty]
    exact hunit
  case hins =>
    intro k x m'' hm'' IH hf''
    have h_ins := insert (op := op) (unit := unit) Φ m'' k x hm''
    apply (hproper _ _ h_ins) |>.mpr
    apply hop
    · apply hf''
      exact FiniteMapLaws.lookup_insert_eq m'' k x
    · apply IH
      intro k' x' hget'
      apply hf''
      rw [FiniteMapLaws.lookup_insert_ne m'' k k' x]
      · exact hget'
      · intro heq
        subst heq
        rw [hget'] at hm''
        exact Option.noConfusion hm''

theorem closed (P : M → Prop) (Φ : K → V → M) (m : M' V)
    (hproper : ∀ x y, x ≡ y → (P x ↔ P y))
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ k x, FiniteMap.get? m k = some x → P (Φ k x)) :
    P (bigOpM (op := op) (unit := unit) Φ m) :=
  closed_aux P Φ hproper hunit hop m hf

omit [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_kmap`. -/
theorem kmap {M'' : Type _ → Type _} {K' : Type _} [DecidableEq K'] [FiniteMap K' M'']
    [FiniteMapLaws K' M''] [FiniteMapKmapLaws K K' M' M'']
    (h : K → K') (hinj : ∀ {x y}, h x = h y → x = y) (Φ : K' → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.kmap (M' := M'') h m : M'' V) ≡
    bigOpM (op := op) (unit := unit) (fun k v => Φ (h k) v) m := by
  simp only [bigOpM]
  have h1 : bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList (FiniteMap.kmap (M' := M'') h m : M'' V)) ≡
            bigOpL op unit (fun _ kv => Φ kv.1 kv.2) ((FiniteMap.toList m).map (fun kv => (h kv.1, kv.2))) := by
    apply BigOpL.perm
    exact FiniteMapKmapLaws.toList_kmap h m hinj
  apply Equiv.trans h1
  exact BigOpL.fmap (op := op) (unit := unit) (fun kv => (h kv.1, kv.2)) (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList m)

omit [DecidableEq V] in
/-- Corresponds to Rocq's `big_opM_map_seq`. -/
theorem map_seq {M'' : Type w → Type _} [FiniteMap Nat M''] [FiniteMapLaws Nat M'']
    [FiniteMapSeqLaws M'']
    (Φ : Nat → V → M) (start : Nat) (l : List V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.map_seq (M := M'') start l : M'' V) ≡
    bigOpL op unit (fun i x => Φ (start + i) x) l := by
  simp only [bigOpM]
  have h1 : bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList (FiniteMap.map_seq (M := M'') start l : M'' V)) ≡
            bigOpL op unit (fun _ kv => Φ kv.1 kv.2) ((List.range' start l.length).zip l) := by
    apply BigOpL.perm
    exact FiniteMapSeqLaws.toList_map_seq start l
  apply Equiv.trans h1
  exact BigOpL.zip_seq (op := op) (unit := unit) (fun kv => Φ kv.1 kv.2) start l

/-- Corresponds to Rocq's `big_opM_sep_zip_with`. -/
theorem sep_zip_with {A : Type _} {B : Type _} {C : Type _}
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (h1 : K → A → M) (h2 : K → B → M) (m1 : M' A) (m2 : M' B)
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hdom : ∀ k, (FiniteMap.get? m1 k).isSome ↔ (FiniteMap.get? m2 k).isSome) :
    bigOpM (op := op) (unit := unit) (fun k xy => op (h1 k (g1 xy)) (h2 k (g2 xy)))
      (FiniteMap.zipWith f m1 m2) ≡
    op (bigOpM (op := op) (unit := unit) h1 m1) (bigOpM (op := op) (unit := unit) h2 m2) := by
  -- Use op_distr to split the combined operation
  have h_op := op_distr (op := op) (unit := unit)
    (fun k xy => h1 k (g1 xy)) (fun k xy => h2 k (g2 xy)) (FiniteMap.zipWith f m1 m2)
  apply Equiv.trans h_op
  -- Now we need to show that:
  -- bigOpM (h1 k (g1 xy)) (zipWith f m1 m2) ≡ bigOpM h1 m1
  -- bigOpM (h2 k (g2 xy)) (zipWith f m1 m2) ≡ bigOpM h2 m2
  apply Monoid.op_proper
  · -- Use fmap to relate zipWith composed with g1 to m1
    have h1_fmap := fmap (op := op) (unit := unit) g1 h1 (FiniteMap.zipWith f m1 m2)
    apply Equiv.trans (Equiv.symm h1_fmap)
    -- Use map_fmap_zipWith_r to show: map g1 (zipWith f m1 m2) = m1
    have heq := FiniteMapLaws.map_fmap_zipWith_r f g1 m1 m2 hg1 hdom
    rw [heq]
  · -- Similarly for g2
    have h2_fmap := fmap (op := op) (unit := unit) g2 h2 (FiniteMap.zipWith f m1 m2)
    apply Equiv.trans (Equiv.symm h2_fmap)
    -- Use map_fmap_zipWith_l to show: map g2 (zipWith f m1 m2) = m2
    have heq := FiniteMapLaws.map_fmap_zipWith_l f g2 m1 m2 hg2 hdom
    rw [heq]

/-- Corresponds to Rocq's `big_opM_sep_zip`. -/
theorem sep_zip {A : Type _} {B : Type _}
    [DecidableEq A] [DecidableEq B]
    (h1 : K → A → M) (h2 : K → B → M) (m1 : M' A) (m2 : M' B)
    (hdom : ∀ k, (FiniteMap.get? m1 k).isSome ↔ (FiniteMap.get? m2 k).isSome) :
    bigOpM (op := op) (unit := unit) (fun k xy => op (h1 k xy.1) (h2 k xy.2))
      (FiniteMap.zip m1 m2) ≡
    op (bigOpM (op := op) (unit := unit) h1 m1) (bigOpM (op := op) (unit := unit) h2 m2) := by
  simp only [FiniteMap.zip]
  exact sep_zip_with (op := op) (unit := unit) Prod.mk Prod.fst Prod.snd h1 h2 m1 m2
    (fun _ _ => rfl) (fun _ _ => rfl) hdom

end BigOpM

end Iris.Algebra
