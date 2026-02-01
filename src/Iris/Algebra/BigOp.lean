/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Algebra.Monoid
import Iris.Std.List
import Iris.Std.FiniteMap

namespace Iris.Algebra

/-! # Big Operators

This file defines big operators (fold operations) at the abstract OFE level.
These are parameterized by a monoid operation and include theorems about their properties.
-/

open OFE

/-- Corresponds to Rocq's `big_opL`. -/
def bigOpL {M : Type u} {A : Type v} (op : M → M → M) (unit : M)
    (Φ : Nat → A → M) (l : List A) : M :=
  match l with
  | [] => unit
  | x :: xs => op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs)

namespace BigOpL

variable {M : Type _} {A : Type _} {op : M → M → M} {unit : M}

/-- Corresponds to Rocq's `big_opL_nil`. -/
@[simp] theorem nil (Φ : Nat → A → M) :
    bigOpL op unit Φ ([] : List A) = unit := rfl

/-- Corresponds to Rocq's `big_opL_cons`. -/
@[simp] theorem cons (Φ : Nat → A → M) (x : A) (xs : List A) :
    bigOpL op unit Φ (x :: xs) = op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs) := rfl

section

variable [OFE M] [Monoid M op unit]

/-- Corresponds to Rocq's `big_opL_singleton`. -/
@[simp] theorem singleton (Φ : Nat → A → M) (x : A) :
    bigOpL op unit Φ [x] ≡ Φ 0 x := by
  simp only [cons, nil]
  exact Monoid.op_right_id _

/-- Corresponds to Rocq's `big_opL_proper`. -/
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

/-- Corresponds to Rocq's `big_opL_ne`. -/
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

/-- Congruence when the functions are equivalent on all indices. -/
theorem congr' {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, Φ i x ≡ Ψ i x) :
    bigOpL op unit Φ l ≡ bigOpL op unit Ψ l :=
  congr (fun i x _ => h i x)

/-- Corresponds to Rocq's `big_opL_app`. -/
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

/-- Corresponds to Rocq's `big_opL_snoc`. -/
theorem snoc (Φ : Nat → A → M) (l : List A) (x : A) :
    bigOpL op unit Φ (l ++ [x]) ≡ op (bigOpL op unit Φ l) (Φ l.length x) := by
  have h := append (M := M) (A := A) (op := op) (unit := unit) (Φ := Φ) l [x]
  simp only [cons, nil, Nat.zero_add] at h
  have hr : op (Φ l.length x) unit ≡ Φ l.length x := Monoid.op_right_id (Φ l.length x)
  exact Monoid.op_congr_r hr |> Equiv.trans h

/-- Corresponds to Rocq's `big_opL_unit`. -/
theorem unit_const (l : List A) :
    bigOpL op unit (fun _ _ => unit) l ≡ unit := by
  induction l with
  | nil => exact Equiv.rfl
  | cons _ _ ih => simp only [cons]; exact Equiv.trans (Monoid.op_left_id _) ih

/-- Corresponds to Rocq's `big_opL_op`. -/
theorem op_distr (Φ Ψ : Nat → A → M) (l : List A) :
    bigOpL op unit (fun i x => op (Φ i x) (Ψ i x)) l ≡
      op (bigOpL op unit Φ l) (bigOpL op unit Ψ l) := by
  induction l generalizing Φ Ψ with
  | nil => simp only [nil]; exact Equiv.symm (Monoid.op_left_id _)
  | cons x xs ih =>
    simp only [cons]
    exact Equiv.trans (Monoid.op_congr_r (ih _ _)) Monoid.op_op_swap

/-- Corresponds to Rocq's `big_opL_fmap`. -/
theorem map {B : Type v} (h : A → B) (Φ : Nat → B → M) (l : List A) :
    bigOpL op unit Φ (l.map h) ≡ bigOpL op unit (fun i x => Φ i (h x)) l := by
  induction l generalizing Φ with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, cons]
    exact Monoid.op_proper Equiv.rfl (ih (fun n => Φ (n + 1)))

/-- Corresponds to Rocq's `big_opL_permutation`. -/
theorem perm (Φ : A → M) {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    bigOpL op unit (fun _ => Φ) l₁ ≡ bigOpL op unit (fun _ => Φ) l₂ := by
  induction hp with
  | nil => exact Equiv.rfl
  | cons _ _ ih => simp only [cons]; exact Monoid.op_congr_r ih
  | swap _ _ _ => simp only [cons]; exact Monoid.op_swap_inner (unit := unit)
  | trans _ _ ih1 ih2 => exact Equiv.trans ih1 ih2

/-- Corresponds to Rocq's `big_opL_take_drop`. -/
theorem take_drop (Φ : Nat → A → M) (l : List A) (n : Nat) :
    bigOpL op unit Φ l ≡
      op (bigOpL op unit Φ (l.take n)) (bigOpL op unit (fun k => Φ (n + k)) (l.drop n)) := by
  by_cases hn : n ≤ l.length
  · have h := append (M := M) (A := A) (op := op) (unit := unit) (Φ := Φ)
      (l.take n) (l.drop n)
    simp only [List.take_append_drop, List.length_take_of_le hn, Nat.add_comm] at h
    exact h
  · simp only [Nat.not_le] at hn
    simp only [List.drop_eq_nil_of_le (Nat.le_of_lt hn), List.take_of_length_le (Nat.le_of_lt hn), nil]
    exact Equiv.symm (Monoid.op_right_id _)

/-- Corresponds to Rocq's `big_opL_omap`. -/
theorem filter_map {B : Type v} (h : A → Option B) (Φ : B → M) (l : List A) :
    bigOpL op unit (fun _ => Φ) (l.filterMap h) ≡
      bigOpL op unit (fun _ x => (h x).elim unit Φ) l := by
  induction l with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    cases hx : h x <;> simp only [hx, Option.elim, cons]
    · exact Equiv.trans ih (Equiv.symm (Monoid.op_left_id _))
    · exact Monoid.op_congr_r ih

/-- Corresponds to Rocq's `big_opL_bind`. -/
theorem bind {B : Type v} (h : A → List B) (Φ : B → M) (l : List A) :
    bigOpL op unit (fun _ => Φ) (l.flatMap h) ≡
      bigOpL op unit (fun _ x => bigOpL op unit (fun _ => Φ) (h x)) l := by
  induction l with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, cons]
    exact Equiv.trans (append _ _ _) (Monoid.op_congr_r ih)

end

/-- Corresponds to Rocq's `big_opL_closed`. -/
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

/-- Corresponds to Rocq's `big_opL_gen_proper_2`. -/
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

/-- Corresponds to Rocq's `big_opL_gen_proper`. -/
theorem gen_proper (R : M → M → Prop)
    (Φ Ψ : Nat → A → M) (l : List A)
    (hR_refl : ∀ x, R x x)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ k y, l[k]? = some y → R (Φ k y) (Ψ k y)) :
    R (bigOpL op unit Φ l) (bigOpL op unit Ψ l) := by
  apply gen_proper_2 (op := op) (unit := unit) R Φ Ψ l l
  · exact hR_refl unit
  · exact hR_op
  · rfl
  · intro k x y hx hy
    cases hget : l[k]? with
    | none =>
      rw [hget] at hx
      cases hx
    | some z =>
      have hxz : x = z := by rw [hget] at hx; cases hx; rfl
      have hyz : y = z := by rw [hget] at hy; cases hy; rfl
      rw [hxz, hyz]
      exact hf k z hget

/-- Corresponds to Rocq's `big_opL_ext`. -/
theorem ext {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x = Ψ i x) :
    bigOpL op unit Φ l = bigOpL op unit Ψ l := by
    apply gen_proper
    · intro _
      rfl
    · intros _ _ _ _ ha hb
      rw [ha, hb]
    · apply h

/-- Corresponds to Rocq's `big_opL_consZ_l`. -/
theorem cons_int_l (Φ : Int → A → M) (x : A) (l : List A) :
    bigOpL op unit (fun k => Φ k) (x :: l) =
    op (Φ 0 x) (bigOpL op unit (fun k y => Φ (1 + (k : Int)) y) l) := by
  simp only [cons]
  apply congrArg
  apply ext
  intro i y hy
  congr 1
  omega

/-- Corresponds to Rocq's `big_opL_consZ_r`. -/
theorem cons_int_r (Φ : Int → A → M) (x : A) (l : List A) :
    bigOpL op unit (fun k => Φ k) (x :: l) =
    op (Φ 0 x) (bigOpL op unit (fun k y => Φ ((k : Int) + 1) y) l) := by
  simp only [cons]
  rfl

section

variable [OFE M] [Monoid M op unit]

/-- Corresponds to Rocq's `big_opL_proper_2`. -/
theorem proper_2 [OFE A] (Φ Ψ : Nat → A → M) (l₁ l₂ : List A)
    (hlen : l₁.length = l₂.length)
    (hf : ∀ (k : Nat) (y₁ y₂ : A), l₁[k]? = some y₁ → l₂[k]? = some y₂ → Φ k y₁ ≡ Ψ k y₂) :
    bigOpL op unit Φ l₁ ≡ bigOpL op unit Ψ l₂ := by
  apply gen_proper_2 (op := op) (unit := unit) (· ≡ ·) Φ Ψ l₁ l₂
  · exact Equiv.rfl
  · intros a a' b b' ha hb; exact Monoid.op_proper ha hb
  · exact hlen
  · intro k x y hx hy
    cases hget1 : l₁[k]? with
    | none =>
      rw [hget1] at hx
      cases hx
    | some z₁ =>
      cases hget2 : l₂[k]? with
      | none =>
        have h1 : k < l₁.length := by
          cases h : l₁[k]? <;> simp_all
        rw [hlen] at h1
        have h2 : k < l₂.length := h1
        have : l₂[k]? ≠ none := by
          intro h
          have : l₂[k]? = some l₂[k] := List.getElem?_eq_getElem h2
          simp [h] at this
        contradiction
      | some z₂ =>
        have hxz1 : x = z₁ := by rw [hget1] at hx; cases hx; rfl
        have hyz2 : y = z₂ := by rw [hget2] at hy; cases hy; rfl
        rw [hxz1, hyz2]
        exact hf k z₁ z₂ hget1 hget2

/-- Corresponds to Rocq's `big_opL_zip_seq`. -/
theorem zip_idx (Φ : A × Nat → M) (n : Nat) (l : List A) :
    bigOpL op unit (fun _ => Φ) (l.zipIdx n) ≡
      bigOpL op unit (fun i x => Φ (x, n + i)) l := by
  induction l generalizing n with
  | nil => simp only [nil]; exact Equiv.rfl
  | cons x xs ih =>
    simp only [cons, Nat.add_zero]
    refine Monoid.op_proper Equiv.rfl (Equiv.trans (ih (n + 1)) (congr' fun i _ => ?_))
    simp only [Nat.add_assoc, Nat.add_comm 1 i]; exact Equiv.rfl

/-- Corresponds to Rocq's `big_opL_zip_seqZ`. -/
theorem zip_idx_int (Φ : A × Int → M) (n : Int) (l : List A) :
    bigOpL op unit (fun _ => Φ) (Std.List.zipIdxInt l n) ≡
      bigOpL op unit (fun i x => Φ (x, n + (i : Int))) l := by
  unfold Std.List.zipIdxInt
  suffices ∀ m, bigOpL op unit (fun _ => Φ) (l.mapIdx (fun i v => (v, (i : Int) + m))) ≡
                bigOpL op unit (fun i x => Φ (x, m + (i : Int))) l by exact this n
  intro m
  induction l generalizing m with
  | nil => simp only [List.mapIdx, nil]; exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.mapIdx_cons, cons]
    apply Monoid.op_proper
    · show Φ (x, (0 : Int) + m) ≡ Φ (x, m + (0 : Int))
      rw [Int.zero_add, Int.add_zero]
    · have h_shift : ∀ i, ((i + 1 : Nat) : Int) + m = (i : Int) + (m + 1) := by
        intro i; omega
      have list_eq : (List.mapIdx (fun i v => (v, ↑(i + 1) + m)) xs) =
                     (List.mapIdx (fun i v => (v, ↑i + (m + 1))) xs) := by
        apply List.ext_getElem
        · simp only [List.length_mapIdx]
        · intro n hn1 hn2
          simp only [List.getElem_mapIdx]
          congr 1
          exact h_shift n
      rw [list_eq]
      have h_ih := ih (m + 1)
      refine Equiv.trans h_ih (congr' fun i _ => ?_)
      have : m + 1 + (i : Int) = m + ((i + 1 : Nat) : Int) := by omega
      rw [this]

/-- Corresponds to Rocq's `big_opL_sep_zip_with`. -/
theorem sep_zip_with {B C : Type _}
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

/-- Big op over zipped list with separated functions. -/
theorem sep_zip {B : Type v} (Φ : Nat → A → M) (Ψ : Nat → B → M) (l₁ : List A) (l₂ : List B)
    (hlen : l₁.length = l₂.length) :
    bigOpL op unit (fun i xy => op (Φ i xy.1) (Ψ i xy.2)) (l₁.zip l₂) ≡
      op (bigOpL op unit Φ l₁) (bigOpL op unit Ψ l₂) := by
  simp [List.zip]
  apply sep_zip_with (op := op)
  · intro _ _
    trivial
  · intro _ _
    trivial
  · apply hlen

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

end

end BigOpL

namespace BigOpM

open Iris.Std

variable {M : Type u} {op : M → M → M} {unit : M}
variable {M' : Type _ → Type _} {K : Type _} {V : Type _}

section
variable [FiniteMap K M']

/-- Corresponds to Rocq's `big_opM`. -/
def bigOpM (Φ : K → V → M) (m : M' V) : M :=
  bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList m)

end

section
variable [OFE M] [FiniteMap K M']

/-- Corresponds to Rocq's `big_opM_map_to_list`. -/
theorem to_list (Φ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ m ≡
    bigOpL op unit (fun _ kx => Φ kx.1 kx.2) (FiniteMap.toList m) := by
  simp only [bigOpM]
  rfl

end

section
variable [FiniteMap K M'] [OFE M] [Monoid M op unit]

/-- Corresponds to Rocq's `big_opM_op`. -/
theorem op_distr (Φ Ψ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) (fun k x => op (Φ k x) (Ψ k x)) m ≡
    op (bigOpM (op := op) (unit := unit) Φ m) (bigOpM (op := op) (unit := unit) Ψ m) := by
  simp only [bigOpM]
  have h := BigOpL.op_distr (op := op) (unit := unit)
    (fun _ kv => Φ kv.1 kv.2) (fun _ kv => Ψ kv.1 kv.2) (FiniteMap.toList m)
  exact h

end

section
variable [OFE M] [Monoid M op unit]

private theorem filter_list_aux (Φ : K × V → M) (φ : K → V → Bool) (l : List (K × V)) :
    bigOpL op unit (fun _ kv => Φ kv) (l.filter (fun kv => φ kv.1 kv.2)) ≡
    bigOpL op unit (fun _ kv => if φ kv.1 kv.2 then Φ kv else unit) l := by
  induction l with
  | nil => simp only [List.filter, BigOpL.nil]; exact Equiv.rfl
  | cons kv kvs ih =>
    simp only [List.filter]
    cases hp : φ kv.1 kv.2 with
    | false =>
      simp only [BigOpL.cons, hp]
      exact Equiv.trans ih (Equiv.symm (Monoid.op_left_id _))
    | true =>
      simp only [BigOpL.cons, hp]
      exact Monoid.op_congr_r ih

end

section
variable [DecidableEq K] [FiniteMap K M'] [FiniteMapLaws K M']

/-- Corresponds to Rocq's `big_opM_empty`. -/
@[simp] theorem empty (Φ : K → V → M) :
    bigOpM (op := op) (unit := unit) Φ (∅ : M' V) = unit := by
  simp only [bigOpM, FiniteMapLaws.toList_empty, BigOpL.nil]

section
variable [OFE M] [Monoid M op unit]

/-- Corresponds to Rocq's `big_opM_insert`. -/
theorem insert [DecidableEq V] (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    FiniteMap.get? m i = none →
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.insert m i x) ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ m) := by
  intro hi
  simp only [bigOpM]
  have hperm := FiniteMapLaws.toList_insert m i x hi
  have heq : bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList (FiniteMap.insert m i x)) ≡
             bigOpL op unit (fun _ kv => Φ kv.1 kv.2) ((i, x) :: FiniteMap.toList m) :=
    BigOpL.perm _ hperm
  simp only [BigOpL.cons] at heq
  exact heq

/-- Corresponds to Rocq's `big_opM_delete`. -/
theorem delete [DecidableEq V] (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    FiniteMap.get? m i = some x →
    bigOpM (op := op) (unit := unit) Φ m ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ (FiniteMap.delete m i)) := by
  intro hi
  have heq := FiniteMapLaws.insert_delete_cancel m i x hi
  have : bigOpM (op := op) (unit := unit) Φ m = bigOpM (op := op) (unit := unit) Φ (FiniteMap.insert (FiniteMap.delete m i) i x) := by
    rw [heq]
  rw [this]
  have hdelete := FiniteMapLaws.get?_delete_same m i
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
  refine FiniteMapLaws.induction_on (P := fun m1' => ∀ m2' Φ' Ψ',
      (∀ k, match FiniteMap.get? m1' k, FiniteMap.get? m2' k with
        | some y1, some y2 => R (Φ' k y1) (Ψ' k y2)
        | none, none => True
        | _, _ => False) →
      R (bigOpM (op := op) (unit := unit) Φ' m1') (bigOpM (op := op) (unit := unit) Ψ' m2'))
    ?hemp ?hins m1 m2 Φ Ψ hfg
  case hemp =>
    intro m2' Φ' Ψ' hfg'
    refine FiniteMapLaws.induction_on (P := fun m2'' => ∀ Φ'' Ψ'',
        (∀ k, match FiniteMap.get? (∅ : M' A) k, FiniteMap.get? m2'' k with
          | some y1, some y2 => R (Φ'' k y1) (Ψ'' k y2)
          | none, none => True
          | _, _ => False) →
        R (bigOpM (op := op) (unit := unit) Φ'' (∅ : M' A)) (bigOpM (op := op) (unit := unit) Ψ'' m2''))
      ?hemp2 ?hins2 m2' Φ' Ψ' hfg'
    case hemp2 => intro _ _ _; rw [empty, empty]; exact hR_sub unit unit Equiv.rfl
    case hins2 =>
      intro k x2 _ _ _ _ _ hfg''
      have := hfg'' k
      rw [FiniteMapLaws.get?_empty, FiniteMapLaws.get?_insert_same] at this
      cases this
  case hins =>
    intro k x1 m1' hm1'k IH m2' Φ' Ψ' hfg'
    have hfg_k := hfg' k
    rw [FiniteMapLaws.get?_insert_same] at hfg_k
    cases hm2k : FiniteMap.get? m2' k with
    | none => rw [hm2k] at hfg_k; cases hfg_k
    | some x2 =>
      rw [hm2k] at hfg_k
      have h_IH : R (bigOpM (op := op) (unit := unit) Φ' m1')
                    (bigOpM (op := op) (unit := unit) Ψ' (FiniteMap.delete m2' k)) := by
        refine IH _ _ _ fun k' => ?_
        by_cases hkk' : k = k'
        · subst hkk'; rw [FiniteMapLaws.get?_delete_same, hm1'k]; trivial
        · have h1 := FiniteMapLaws.get?_insert_ne m1' k k' x1 hkk'
          have h2 := FiniteMapLaws.get?_delete_ne m2' k k' hkk'
          rw [← h1, h2]; exact hfg' k'
      exact hR_equiv.trans (hR_sub _ _ (insert Φ' m1' k x1 hm1'k))
        (hR_equiv.trans (hR_op _ _ _ _ hfg_k h_IH) (hR_sub _ _ (Equiv.symm (delete Ψ' m2' k x2 hm2k))))

end

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
    have := FiniteMapLaws.mem_toList m x.1 x.2 |>.mp this
    exact hf x.1 x.2 this

/-- Corresponds to Rocq's `big_opM_ext`. -/
theorem ext {M : Type u} (op : M → M → M) (unit : M) (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, FiniteMap.get? m k = some x → Φ k x = Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m = bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· = ·))
  · intro _; rfl
  · intros _ _ _ _ ha hb; rw [ha, hb]
  · exact hf

section
variable [OFE M] [Monoid M op unit]

/-- Corresponds to Rocq's `big_opM_ne`. -/
theorem ne (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, FiniteMap.get? m k = some x → Φ k x ≡{n}≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡{n}≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· ≡{n}≡ ·))
  · intro _; exact Dist.rfl
  · intros a a' b b' ha hb; exact Monoid.op_ne_dist ha hb
  · exact hf

/-- Corresponds to Rocq's `big_opM_proper`. -/
theorem proper (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, FiniteMap.get? m k = some x → Φ k x ≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· ≡ ·))
  · intro _; exact Equiv.rfl
  · intros a a' b b' ha hb; exact Monoid.op_proper ha hb
  · exact hf

/-- Corresponds to Rocq's `big_opM_proper_2`. -/
theorem proper_2 [OFE A] [DecidableEq A] (Φ : K → A → M) (Ψ : K → A → M) (m1 m2 : M' A)
    (hm : ∀ k, FiniteMap.get? m1 k = FiniteMap.get? m2 k)
    (hf : ∀ k y1 y2,
      FiniteMap.get? m1 k = some y1 →
      FiniteMap.get? m2 k = some y2 →
      y1 ≡ y2 →
      Φ k y1 ≡ Ψ k y2) :
    bigOpM (op := op) (unit := unit) Φ m1 ≡ bigOpM (op := op) (unit := unit) Ψ m2 := by
  apply gen_proper_2 (R := (· ≡ ·))
  · intros _ _ h; exact h
  · exact equiv_eqv
  · intros a a' b b' ha hb; exact Monoid.op_proper ha hb
  · intro k
    have hlk := hm k
    cases hm1k : FiniteMap.get? m1 k with
    | none =>
      rw [hm1k] at hlk
      rw [← hlk]
      trivial
    | some y1 =>
      rw [hm1k] at hlk
      cases hm2k : FiniteMap.get? m2 k with
      | none => rw [hm2k] at hlk; cases hlk
      | some y2 =>
        rw [hm2k] at hlk
        cases hlk
        exact hf k y1 y1 hm1k hm2k Equiv.rfl

/-- Corresponds to Rocq's `big_opM_ne'` instance. -/
theorem ne_pointwise (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, Φ k x ≡{n}≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡{n}≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply ne
  intros k x _
  exact hf k x

/-- Corresponds to Rocq's `big_opM_proper'` instance. -/
theorem proper_pointwise (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, Φ k x ≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply proper
  intros k x _
  exact hf k x

/-- Corresponds to Rocq's `big_opM_list_to_map`. -/
theorem of_list [DecidableEq V] (Φ : K → V → M) (l : List (K × V))
    (hnodup : (l.map Prod.fst).Nodup) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.ofList l : M' V) ≡
    bigOpL op unit (fun _ kx => Φ kx.1 kx.2) l := by
  have h1 := to_list (op := op) (unit := unit) Φ (FiniteMap.ofList l : M' V)
  apply Equiv.trans h1
  apply BigOpL.perm
  exact FiniteMapLaws.toList_ofList l hnodup

/-- Corresponds to Rocq's `big_opM_singleton`. -/
theorem singleton [DecidableEq V] (Φ : K → V → M) (i : K) (x : V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.singleton (M := M') i x) ≡ Φ i x := by
  have : FiniteMap.get? (∅ : M' V) i = none := FiniteMapLaws.get?_empty i
  have := insert (op := op) (unit := unit) Φ (∅ : M' V) i x this
  rw [empty] at this
  exact Equiv.trans this (Monoid.op_right_id (Φ i x))

/-- Corresponds to Rocq's `big_opM_unit`. -/
theorem unit_const [DecidableEq V] (m : M' V) :
    bigOpM (op := op) (unit := unit) (fun _ _ => unit) m ≡ unit := by
  refine FiniteMapLaws.induction_on
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

/-- Corresponds to Rocq's `big_opM_fmap`. -/
theorem map {B : Type w} [DecidableEq B] (h : V → B) (Φ : K → B → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.map h m) ≡
    bigOpM (op := op) (unit := unit) (fun k v => Φ k (h v)) m := by
  simp only [bigOpM]
  have h1 : bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList (FiniteMap.map h m)) ≡
            bigOpL op unit (fun _ kv => Φ kv.1 kv.2) ((FiniteMap.toList m).map (fun kv => (kv.1, h kv.2))) := by
    apply BigOpL.perm
    exact FiniteMapLaws.toList_map m h
  apply Equiv.trans h1
  exact BigOpL.map (op := op) (unit := unit) (fun kv => (kv.1, h kv.2)) (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList m)

/-- Corresponds to Rocq's `big_opM_omap`. -/
theorem filter_map [FiniteMapLawsSelf K M'] (h : V → Option V) (Φ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.filterMap h m) ≡
    bigOpM (op := op) (unit := unit) (fun k v => (h v).elim unit (Φ k)) m := by
  simp only [bigOpM, FiniteMap.filterMap]
  -- Use toList_filterMap to relate toList of filterMap to filterMap of toList
  have h1 : bigOpL op unit (fun _ kv => Φ kv.1 kv.2)
              (FiniteMap.toList (FiniteMap.ofList ((FiniteMap.toList m).filterMap (fun (k, v) => (h v).map (k, ·))) : M' V)) ≡
            bigOpL op unit (fun _ kv => Φ kv.1 kv.2)
              ((FiniteMap.toList m).filterMap (fun (k, v) => (h v).map (k, ·))) := by
    apply BigOpL.perm
    have hperm := toList_filterMap m h
    exact hperm
  refine Equiv.trans h1 ?_
  -- Now use BigOpL.filter_map
  have h2 : bigOpL op unit (fun _ kv => Φ kv.1 kv.2)
              ((FiniteMap.toList m).filterMap (fun (k, v) => (h v).map (k, ·))) ≡
            bigOpL op unit (fun _ kv => ((h kv.2).map (kv.1, ·)).elim unit (fun kv' => Φ kv'.1 kv'.2))
              (FiniteMap.toList m) := by
    exact BigOpL.filter_map (op := op) (unit := unit) (fun kv => (h kv.2).map (kv.1, ·)) (fun kv => Φ kv.1 kv.2) (FiniteMap.toList m)
  refine Equiv.trans h2 ?_
  -- Simplify the function
  apply BigOpL.congr'
  intro i kv
  cases hkv : h kv.2 <;> simp [Option.elim, Option.map]

/-- Corresponds to Rocq's `big_opM_insert_delete`. -/
theorem insert_delete [DecidableEq V] (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.insert m i x) ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ (FiniteMap.delete m i)) := by
  rw [← FiniteMapLaws.insert_delete m i x]
  exact insert Φ (FiniteMap.delete m i) i x (FiniteMapLaws.get?_delete_same m i)

/-- Corresponds to Rocq's `big_opM_insert_override`. -/
theorem insert_override [DecidableEq A] (Φ : K → A → M) (m : M' A) (i : K) (x x' : A) :
    FiniteMap.get? m i = some x → Φ i x ≡ Φ i x' →
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.insert m i x') ≡
      bigOpM (op := op) (unit := unit) Φ m := by
  intro hi hΦ
  rw [← FiniteMapLaws.insert_delete m i x']
  refine Equiv.trans (insert Φ (FiniteMap.delete m i) i x' (FiniteMapLaws.get?_delete_same m i)) ?_
  refine Equiv.trans (Monoid.op_proper (Equiv.symm hΦ) Equiv.rfl) ?_
  exact Equiv.symm (delete Φ m i x hi)

/-- Corresponds to Rocq's `big_opM_fn_insert`. -/
theorem fn_insert [DecidableEq V] {B : Type w} [DecidableEq B] (g : K → V → B → M) (f : K → B) (m : M' V)
    (i : K) (x : V) (b : B) (hi : FiniteMap.get? m i = none) :
    bigOpM (op := op) (unit := unit) (fun k y => g k y (if k = i then b else f k))
      (FiniteMap.insert m i x) ≡
    op (g i x b) (bigOpM (op := op) (unit := unit) (fun k y => g k y (f k)) m) := by
  have h1 := insert (op := op) (unit := unit) (fun k y => g k y (if k = i then b else f k)) m i x hi
  refine Equiv.trans h1 ?_
  apply Monoid.op_proper
  · simp
  · apply proper (op := op) (unit := unit)
    intros k y hk
    have hne : k ≠ i := fun heq => by rw [heq] at hk; rw [hi] at hk; cases hk
    simp [hne]

/-- Corresponds to Rocq's `big_opM_fn_insert'`. -/
theorem fn_insert' [DecidableEq V] (f : K → M) (m : M' V) (i : K) (x : V) (P : M)
    (hi : FiniteMap.get? m i = none) :
    bigOpM (op := op) (unit := unit) (fun k _ => if k = i then P else f k)
      (FiniteMap.insert m i x) ≡
    op P (bigOpM (op := op) (unit := unit) (fun k _ => f k) m) := by
  have h1 := insert (op := op) (unit := unit) (fun k _ => if k = i then P else f k) m i x hi
  refine Equiv.trans h1 ?_
  apply Monoid.op_proper
  · simp
  · apply proper (op := op) (unit := unit)
    intros k y hk
    have hne : k ≠ i := fun heq => by rw [heq] at hk; rw [hi] at hk; cases hk
    simp [hne]


/-- Corresponds to Rocq's `big_opM_filter'`. -/
theorem filter' [FiniteMapLawsSelf K M'] (φ : K → V → Bool) (Φ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.filter φ m) ≡
    bigOpM (op := op) (unit := unit) (fun k x => if φ k x then Φ k x else unit) m := by
  unfold bigOpM
  have hperm := toList_filter m φ
  have heq : bigOpL op unit (fun _ kv => Φ kv.1 kv.2)
               (FiniteMap.toList (FiniteMap.filter φ m)) ≡
             bigOpL op unit (fun _ kv => Φ kv.1 kv.2)
               ((FiniteMap.toList m).filter (fun kv => φ kv.1 kv.2)) :=
    BigOpL.perm _ hperm
  refine Equiv.trans heq ?_
  exact filter_list_aux (fun kv => Φ kv.1 kv.2) φ (FiniteMap.toList m)

/-- Corresponds to Rocq's `big_opM_union`. -/
theorem union [DecidableEq V] (Φ : K → V → M) (m1 m2 : M' V) (hdisj : m1 ##ₘ m2) :
    bigOpM (op := op) (unit := unit) Φ (m1 ∪ m2) ≡
    op (bigOpM (op := op) (unit := unit) Φ m1) (bigOpM (op := op) (unit := unit) Φ m2) := by
  apply FiniteMapLaws.induction_on (P := fun m1 =>
    m1 ##ₘ m2 →
    bigOpM (op := op) (unit := unit) Φ (m1 ∪ m2) ≡
    op (bigOpM (op := op) (unit := unit) Φ m1) (bigOpM (op := op) (unit := unit) Φ m2))
  · intro _
    rw [FiniteMapLaws.ext (∅ ∪ m2) m2 fun k => by simp [FiniteMapLaws.get?_union, FiniteMapLaws.get?_empty], empty]
    exact (Monoid.op_left_id _).symm
  · intro i x m hi_none IH hdisj'
    have hi_m2 : get? m2 i = none := by simpa [FiniteMapLaws.get?_insert_same] using FiniteMapLaws.disjoint_iff (Std.insert m i x) m2 |>.mp hdisj' i
    have hm_disj : m ##ₘ m2 := fun k ⟨hk1, hk2⟩ => hdisj' k ⟨by
      by_cases h : i = k <;> simp [FiniteMapLaws.get?_insert_same, FiniteMapLaws.get?_insert_ne, *], hk2⟩
    rw [← FiniteMapLaws.ext (Std.insert (m ∪ m2) i x) (Std.insert m i x ∪ m2) fun k => congrFun (FiniteMapLaws.union_insert_left m m2 i x) k]
    refine (insert Φ (m ∪ m2) i x (by simp [FiniteMapLaws.get?_union_none, hi_none, hi_m2])).trans ?_
    refine (Monoid.op_congr_r (IH hm_disj)).trans ?_
    refine (Monoid.op_assoc _ _ _).symm.trans ?_
    exact Monoid.op_congr_l (insert Φ m i x hi_none).symm
  · exact hdisj

private theorem closed_aux [DecidableEq V] (P : M → Prop) (Φ : K → V → M)
    (hproper : ∀ x y, x ≡ y → (P x ↔ P y))
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y)) :
    ∀ (m' : M' V), (∀ k' x', FiniteMap.get? m' k' = some x' → P (Φ k' x')) →
        P (bigOpM (op := op) (unit := unit) Φ m') := by
  intro m' hf'
  refine FiniteMapLaws.induction_on
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
      exact FiniteMapLaws.get?_insert_same m'' k x
    · apply IH
      intro k' x' hget'
      apply hf''
      rw [FiniteMapLaws.get?_insert_ne m'' k k' x]
      · exact hget'
      · intro heq
        subst heq
        rw [hget'] at hm''
        exact Option.noConfusion hm''

/-- Corresponds to Rocq's `big_opM_closed`. -/
theorem closed [DecidableEq V] (P : M → Prop) (Φ : K → V → M) (m : M' V)
    (hproper : ∀ x y, x ≡ y → (P x ↔ P y))
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ k x, FiniteMap.get? m k = some x → P (Φ k x)) :
    P (bigOpM (op := op) (unit := unit) Φ m) :=
  closed_aux P Φ hproper hunit hop m hf

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
  exact BigOpL.map (op := op) (unit := unit) (fun kv => (h kv.1, kv.2)) (fun _ kv => Φ kv.1 kv.2) (FiniteMap.toList m)

/-- Corresponds to Rocq's `big_opM_map_seq`. -/
theorem map_seq {M'' : Type w → Type _} [FiniteMap Nat M''] [FiniteMapLaws Nat M'']
    [FiniteMapSeqLaws M'']
    (Φ : Nat → V → M) (start : Nat) (l : List V) :
    bigOpM (op := op) (unit := unit) Φ (FiniteMap.map_seq (M := M'') start l : M'' V) ≡
    bigOpL op unit (fun i x => Φ (start + i) x) l := by
  simp only [bigOpM]
  refine Equiv.trans (BigOpL.perm _ (FiniteMapSeqLaws.toList_map_seq start l)) ?_
  induction l generalizing start with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapIdx_cons, BigOpL.cons, Nat.zero_add, Nat.add_zero]
    have : xs.mapIdx (fun i v => (i + 1 + start, v)) = xs.mapIdx (fun i v => (i + (start + 1), v)) := by
      congr 1; funext i v; rw [Nat.add_assoc, Nat.add_comm 1 start]
    rw [this]
    exact Monoid.op_proper Equiv.rfl (Equiv.trans (ih (start + 1)) (BigOpL.congr' fun i _ => by simp [Nat.add_assoc, Nat.add_comm 1]))

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
  have h_op := op_distr (op := op) (unit := unit)
    (fun k xy => h1 k (g1 xy)) (fun k xy => h2 k (g2 xy)) (FiniteMap.zipWith f m1 m2)
  apply Equiv.trans h_op
  apply Monoid.op_proper
  · have h1_fmap := map (op := op) (unit := unit) g1 h1 (FiniteMap.zipWith f m1 m2)
    apply Equiv.trans (Equiv.symm h1_fmap)
    have heq := FiniteMapLaws.map_zipWith_right f g1 m1 m2 hg1 hdom
    rw [heq]
  · have h2_fmap := map (op := op) (unit := unit) g2 h2 (FiniteMap.zipWith f m1 m2)
    apply Equiv.trans (Equiv.symm h2_fmap)
    have heq := FiniteMapLaws.map_zipWith_left f g2 m1 m2 hg2 hdom
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

end

end

end BigOpM

end Iris.Algebra
