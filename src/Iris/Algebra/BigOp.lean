/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Algebra.Monoid
import Iris.Std.List
import Iris.Std.PartialMap

namespace Iris.Algebra

/-! # Big Operators

This file defines big operators (fold operations) at the abstract OFE level.
These are parameterized by a monoid operation and include theorems about their properties.
-/

open OFE

def bigOpL {M : Type u} {A : Type v} (op : M → M → M) (unit : M)
    (Φ : Nat → A → M) (l : List A) : M :=
  match l with
  | [] => unit
  | x :: xs => op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs)

namespace BigOpL

variable {M : Type _} {A : Type _} [OFE M] {op : M → M → M} {unit : M} [Monoid M op unit]

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

theorem congr {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x ≡ Ψ i x) :
    bigOpL op unit Φ l ≡ bigOpL op unit Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => exact Equiv.rfl
  | cons y ys ih =>
    simp only [cons]
    exact Monoid.op_proper (h 0 y rfl) (ih fun i x hget => h (i + 1) x hget)

theorem congr_ne {Φ Ψ : Nat → A → M} {l : List A} {n : Nat}
    (h : ∀ i x, l[i]? = some x → Φ i x ≡{n}≡ Ψ i x) :
    bigOpL op unit Φ l ≡{n}≡ bigOpL op unit Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => exact Dist.rfl
  | cons y ys ih =>
    simp only [cons]
    exact Monoid.op_ne_dist (h 0 y rfl) (ih fun i x hget => h (i + 1) x hget)

/-- Congruence when the functions are equivalent on all indices. -/
theorem congr' {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, Φ i x ≡ Ψ i x) :
    bigOpL op unit Φ l ≡ bigOpL op unit Ψ l :=
  congr (fun i x _ => h i x)

theorem append (Φ : Nat → A → M) (l₁ l₂ : List A) :
    bigOpL op unit Φ (l₁ ++ l₂) ≡
      op (bigOpL op unit Φ l₁) (bigOpL op unit (fun n => Φ (n + l₁.length)) l₂) := by
  induction l₁ generalizing Φ with
  | nil => simp only [nil]; exact Equiv.symm (Monoid.op_left_id _)
  | cons x xs ih =>
    simp only [List.cons_append, cons, List.length_cons]
    have ih' := ih (fun n => Φ (n + 1))
    calc op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) (xs ++ l₂))
        _ ≡ op (Φ 0 x) (op (bigOpL op unit (fun n => Φ (n + 1)) xs)
              (bigOpL op unit (fun n => Φ (n + xs.length + 1)) l₂)) :=
            Monoid.op_congr_r ih'
        _ ≡ op (op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs))
              (bigOpL op unit (fun n => Φ (n + xs.length + 1)) l₂) :=
            Equiv.symm (Monoid.op_assoc _ _ _)
        _ ≡ op (op (Φ 0 x) (bigOpL op unit (fun n => Φ (n + 1)) xs))
              (bigOpL op unit (fun n => Φ (n + (xs.length + 1))) l₂) := by
            simp only [show ∀ n, n + xs.length + 1 = n + (xs.length + 1) from by omega]; exact Equiv.rfl

theorem snoc (Φ : Nat → A → M) (l : List A) (x : A) :
    bigOpL op unit Φ (l ++ [x]) ≡ op (bigOpL op unit Φ l) (Φ l.length x) := by
  have h := @append M A _ op unit _ Φ l [x]
  simp only [cons, nil, Nat.zero_add] at h
  exact h.trans (Monoid.op_congr_r (Monoid.op_right_id _))

theorem unit_const (l : List A) :
    bigOpL op unit (fun _ _ => unit) l ≡ unit := by
  induction l with
  | nil => exact Equiv.rfl
  | cons _ _ ih => simp only [cons]; exact Equiv.trans (Monoid.op_left_id _) ih

theorem op_distr (Φ Ψ : Nat → A → M) (l : List A) :
    bigOpL op unit (fun i x => op (Φ i x) (Ψ i x)) l ≡
      op (bigOpL op unit Φ l) (bigOpL op unit Ψ l) := by
  induction l generalizing Φ Ψ with
  | nil => simp only [nil]; exact Equiv.symm (Monoid.op_left_id _)
  | cons x xs ih =>
    simp only [cons]
    exact Equiv.trans (Monoid.op_congr_r (ih _ _)) Monoid.op_op_swap

theorem map {B : Type v} (h : A → B) (Φ : Nat → B → M) (l : List A) :
    bigOpL op unit Φ (l.map h) ≡ bigOpL op unit (fun i x => Φ i (h x)) l := by
  induction l generalizing Φ with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, cons]
    exact Monoid.op_proper Equiv.rfl (ih (fun n => Φ (n + 1)))

omit [OFE M] [Monoid M op unit] in
theorem closed (P : M → Prop) (Φ : Nat → A → M) (l : List A)
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ i x, l[i]? = some x → P (Φ i x)) :
    P (bigOpL op unit Φ l) := by
  induction l generalizing Φ with
  | nil => exact hunit
  | cons y ys ih =>
    simp only [cons]
    exact hop _ _ (hf 0 y rfl) (ih _ fun i x hget => hf (i + 1) x hget)

theorem perm (Φ : A → M) {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    bigOpL op unit (fun _ => Φ) l₁ ≡ bigOpL op unit (fun _ => Φ) l₂ := by
  induction hp with
  | nil => exact Equiv.rfl
  | cons _ _ ih => simp only [cons]; exact Monoid.op_congr_r ih
  | swap _ _ _ => simp only [cons]; exact Monoid.op_swap_inner (unit := unit)
  | trans _ _ ih1 ih2 => exact Equiv.trans ih1 ih2

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

theorem bind {B : Type v} (h : A → List B) (Φ : B → M) (l : List A) :
    bigOpL op unit (fun _ => Φ) (l.flatMap h) ≡
      bigOpL op unit (fun _ x => bigOpL op unit (fun _ => Φ) (h x)) l := by
  induction l with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, cons]
    exact Equiv.trans (append _ _ _) (Monoid.op_congr_r ih)

omit [OFE M] [Monoid M op unit] in
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

omit [OFE M] [Monoid M op unit] in
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
    rw [hx] at hy; cases hy
    exact hf k x hx

omit [OFE M] [Monoid M op unit] in
theorem ext {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x = Ψ i x) :
    bigOpL op unit Φ l = bigOpL op unit Ψ l := by
  apply gen_proper
  · intro _; rfl
  · intros _ _ _ _ ha hb; rw [ha, hb]
  · exact h

omit [OFE M] [Monoid M op unit] in
theorem cons_int_l (Φ : Int → A → M) (x : A) (l : List A) :
    bigOpL op unit (fun k => Φ k) (x :: l) =
    op (Φ 0 x) (bigOpL op unit (fun k y => Φ (1 + (k : Int)) y) l) := by
  simp only [cons]
  apply congrArg
  apply ext
  intro i y hy
  congr 1
  omega

omit [OFE M] [Monoid M op unit] in
theorem cons_int_r (Φ : Int → A → M) (x : A) (l : List A) :
    bigOpL op unit (fun k => Φ k) (x :: l) =
    op (Φ 0 x) (bigOpL op unit (fun k y => Φ ((k : Int) + 1) y) l) := by
  rfl

theorem proper_2 [OFE A] (Φ Ψ : Nat → A → M) (l₁ l₂ : List A)
    (hlen : l₁.length = l₂.length)
    (hf : ∀ (k : Nat) (y₁ y₂ : A), l₁[k]? = some y₁ → l₂[k]? = some y₂ → Φ k y₁ ≡ Ψ k y₂) :
    bigOpL op unit Φ l₁ ≡ bigOpL op unit Ψ l₂ := by
  apply gen_proper_2 (op := op) (unit := unit) (· ≡ ·) Φ Ψ l₁ l₂
  · exact Equiv.rfl
  · intros a a' b b' ha hb; exact Monoid.op_proper ha hb
  · exact hlen
  · intro k x y hx hy
    exact hf k x y hx hy

theorem zip_idx (Φ : A × Nat → M) (n : Nat) (l : List A) :
    bigOpL op unit (fun _ => Φ) (l.zipIdx n) ≡
      bigOpL op unit (fun i x => Φ (x, n + i)) l := by
  induction l generalizing n with
  | nil => simp only [nil]; exact Equiv.rfl
  | cons x xs ih =>
    simp only [cons, Nat.add_zero]
    refine Monoid.op_proper Equiv.rfl (Equiv.trans (ih (n + 1)) (congr' fun i _ => ?_))
    simp only [Nat.add_assoc, Nat.add_comm 1 i]; exact Equiv.rfl

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
    · have list_eq : (List.mapIdx (fun i v => (v, ↑(i + 1) + m)) xs) =
                     (List.mapIdx (fun i v => (v, ↑i + (m + 1))) xs) := by
        apply List.ext_getElem (by simp only [List.length_mapIdx])
        intro n hn1 hn2
        simp only [List.getElem_mapIdx]; congr 1; omega
      rw [list_eq]
      exact (ih (m + 1)).trans (congr' fun i _ => by rw [show m + 1 + (i : Int) = m + ((i + 1 : Nat) : Int) from by omega])

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
  exact sep_zip_with (op := op) _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) hlen

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
    exact hom.rel_trans (hom.homomorphism _ _) (hom.op_proper (hom.rel_refl _) (ih _))

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
      exact (hom.rel_proper (NonExpansive.eqv (Monoid.op_right_id _))
        (Monoid.op_right_id _)).mpr (hom.rel_refl _)
    | cons y ys =>
      exact hom.rel_trans (hom.homomorphism _ _)
        (hom.op_proper (hom.rel_refl _) (ih _ (List.cons_ne_nil y ys)))

end BigOpL

namespace BigOpM

open Iris.Std

variable {M : Type u} [OFE M] {op : M → M → M} {unit : M} [Monoid M op unit]
variable {M' : Type _ → Type _} {K : Type _} {V : Type _}
variable [LawfulFiniteMap M' K]

def bigOpM (Φ : K → V → M) (m : M' V) : M :=
  bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (toList (K := K) m)

theorem bigOpM_equiv (Φ : K → V → M) (m₁ m₂ : M' V)
    (h : PartialMap.equiv m₁ m₂) :
    bigOpM (op := op) (unit := unit) Φ m₁ ≡ bigOpM (op := op) (unit := unit) Φ m₂ := by
  simp only [bigOpM]
  exact BigOpL.perm _ (LawfulFiniteMap.toList_perm_of_get?_eq h)

omit [OFE M] [Monoid M op unit] in
@[simp] theorem empty (Φ : K → V → M) :
    bigOpM (op := op) (unit := unit) Φ (∅ : M' V) = unit := by
  show bigOpL op unit _ (toList (∅ : M' V)) = unit
  rw [show toList (K := K) (∅ : M' V) = [] from toList_empty]; rfl

theorem insert (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    get? m i = none →
    bigOpM (op := op) (unit := unit) Φ (Iris.Std.insert m i x) ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ m) := by
  intro hi
  simp only [bigOpM]
  exact BigOpL.perm _ (LawfulFiniteMap.toList_insert (v := x) hi)

theorem delete (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    get? m i = some x →
    bigOpM (op := op) (unit := unit) Φ m ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ (Iris.Std.delete m i)) := by
  intro hi
  exact (bigOpM_equiv Φ m _ (fun k => (LawfulPartialMap.insert_delete_cancel hi k).symm)).trans
    (insert Φ (Iris.Std.delete m i) i x (get?_delete_eq rfl))

variable {A : Type w}

theorem gen_proper_2 [DecidableEq K] {B : Type w} (R : M → M → Prop)
    (Φ : K → A → M) (Ψ : K → B → M) (m1 : M' A) (m2 : M' B)
    (hR_sub : ∀ x y, x ≡ y → R x y)
    (hR_equiv : Equivalence R)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hfg : ∀ k,
      match get? m1 k, get? m2 k with
      | some y1, some y2 => R (Φ k y1) (Ψ k y2)
      | none, none => True
      | _, _ => False) :
    R (bigOpM (op := op) (unit := unit) Φ m1) (bigOpM (op := op) (unit := unit) Ψ m2) := by
  let P1 : M' A → Prop := fun m1' => ∀ (m2' : M' B) (Φ' : K → A → M) (Ψ' : K → B → M),
      (∀ k, match get? m1' k, get? m2' k with
        | some y1, some y2 => R (Φ' k y1) (Ψ' k y2)
        | none, none => True
        | _, _ => False) →
      R (bigOpM (op := op) (unit := unit) Φ' m1') (bigOpM (op := op) (unit := unit) Ψ' m2')
  suffices h : P1 m1 from h m2 Φ Ψ hfg
  have hequiv1 : ∀ (m₁ m₂ : M' A), PartialMap.equiv m₁ m₂ → P1 m₁ → P1 m₂ :=
    fun m₁ m₂ heq hP m2' Φ' Ψ' hfg' =>
      hR_equiv.trans (hR_sub _ _ (bigOpM_equiv Φ' m₁ m₂ heq).symm)
        (hP m2' Φ' Ψ' (fun k => by rw [show get? m₁ k = get? m₂ k from heq k]; exact hfg' k))
  have hemp1 : P1 (∅ : M' A) := by
    intro m2' Φ' Ψ' hfg'
    let P2 : M' B → Prop := fun m2'' => ∀ (Φ'' : K → A → M) (Ψ'' : K → B → M),
        (∀ k, match get? (∅ : M' A) k, get? m2'' k with
          | some y1, some y2 => R (Φ'' k y1) (Ψ'' k y2)
          | none, none => True
          | _, _ => False) →
        R (bigOpM (op := op) (unit := unit) Φ'' (∅ : M' A)) (bigOpM (op := op) (unit := unit) Ψ'' m2'')
    suffices h2 : P2 m2' from h2 Φ' Ψ' hfg'
    exact LawfulFiniteMap.induction_on (K := K) (P := P2)
      (fun m₁ m₂ heq hP Φ'' Ψ'' hfg'' =>
        hR_equiv.trans (hP Φ'' Ψ'' (fun k => by rw [show get? m₁ k = get? m₂ k from heq k]; exact hfg'' k))
          (hR_sub _ _ (bigOpM_equiv Ψ'' m₁ m₂ heq)))
      (fun _ _ _ => by
        show R (bigOpM (op := op) (unit := unit) _ (∅ : M' A))
             (bigOpM (op := op) (unit := unit) _ (∅ : M' B))
        rw [empty, empty]; exact hR_sub unit unit Equiv.rfl)
      (fun k _ _ _ _ Φ'' Ψ'' hfg'' => by
        have := hfg'' k; simp only [show get? (∅ : M' A) k = none from get?_empty k, get?_insert_eq rfl] at this)
      m2'
  have hins1 : ∀ (i : K) (x : A) (m : M' A), get? m i = none → P1 m → P1 (Iris.Std.insert m i x) := by
    intro k x1 m1' hm1'k IH m2' Φ' Ψ' hfg'
    have hfg_k := hfg' k
    rw [get?_insert_eq rfl] at hfg_k
    cases hm2k : get? m2' k with
    | none => rw [hm2k] at hfg_k; cases hfg_k
    | some x2 =>
      rw [hm2k] at hfg_k
      exact hR_equiv.trans (hR_sub _ _ (insert Φ' m1' k x1 hm1'k))
        (hR_equiv.trans (hR_op _ _ _ _ hfg_k (IH _ _ _ fun k' => by
          by_cases hkk' : k = k'
          · subst hkk'; rw [get?_delete_eq rfl, hm1'k]; trivial
          · have := hfg' k'; rw [get?_insert_ne hkk'] at this; rwa [get?_delete_ne hkk']))
          (hR_sub _ _ (Equiv.symm (delete Ψ' m2' k x2 hm2k))))
  exact LawfulFiniteMap.induction_on (K := K) (P := P1) hequiv1 hemp1 hins1 m1

omit [Monoid M op unit] in
theorem gen_proper {M : Type u} {op : M → M → M} {unit : M} (R : M → M → Prop)
    (Φ Ψ : K → V → M) (m : M' V)
    (hR_refl : ∀ x, R x x)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ k x, get? m k = some x → R (Φ k x) (Ψ k x)) :
    R (bigOpM (op := op) (unit := unit) Φ m) (bigOpM (op := op) (unit := unit) Ψ m) := by
  simp only [bigOpM]
  apply BigOpL.gen_proper_2 (op := op) (unit := unit) R
  · exact hR_refl unit
  · exact hR_op
  · rfl
  · intro i x y hx hy
    rw [hx] at hy; cases hy
    exact hf x.1 x.2 (toList_get.mp (List.mem_iff_getElem?.mpr ⟨i, hx⟩))

theorem ext {M : Type u} (op : M → M → M) (unit : M) (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, get? m k = some x → Φ k x = Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m = bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· = ·))
  · intro _; rfl
  · intros _ _ _ _ ha hb; rw [ha, hb]
  · exact hf

theorem ne (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, get? m k = some x → Φ k x ≡{n}≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡{n}≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· ≡{n}≡ ·))
  · intro _; exact Dist.rfl
  · intros a a' b b' ha hb; exact Monoid.op_ne_dist ha hb
  · exact hf

theorem proper (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, get? m k = some x → Φ k x ≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡ bigOpM (op := op) (unit := unit) Ψ m := by
  apply gen_proper (R := (· ≡ ·))
  · intro _; exact Equiv.rfl
  · intros a a' b b' ha hb; exact Monoid.op_proper ha hb
  · exact hf

theorem proper_2 [DecidableEq K] [OFE A] (Φ : K → A → M) (Ψ : K → A → M) (m1 m2 : M' A)
    (hm : ∀ k, get? m1 k = get? m2 k)
    (hf : ∀ k y1 y2,
      get? m1 k = some y1 →
      get? m2 k = some y2 →
      y1 ≡ y2 →
      Φ k y1 ≡ Ψ k y2) :
    bigOpM (op := op) (unit := unit) Φ m1 ≡ bigOpM (op := op) (unit := unit) Ψ m2 := by
  apply gen_proper_2 (R := (· ≡ ·))
  · intros _ _ h; exact h
  · exact equiv_eqv
  · intros a a' b b' ha hb; exact Monoid.op_proper ha hb
  · intro k
    have hlk := hm k
    cases hm1k : get? m1 k with
    | none =>
      rw [hm1k] at hlk
      rw [← hlk]
      trivial
    | some y1 =>
      rw [hm1k] at hlk
      cases hm2k : get? m2 k with
      | none => rw [hm2k] at hlk; cases hlk
      | some y2 =>
        rw [hm2k] at hlk
        cases hlk
        exact hf k y1 y1 hm1k hm2k Equiv.rfl

theorem ne_pointwise (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, Φ k x ≡{n}≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡{n}≡ bigOpM (op := op) (unit := unit) Ψ m :=
  ne _ _ _ _ fun k x _ => hf k x

theorem proper_pointwise (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, Φ k x ≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡ bigOpM (op := op) (unit := unit) Ψ m :=
  proper _ _ _ fun k x _ => hf k x

omit [Monoid M op unit] in
theorem to_list (Φ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ m ≡
    bigOpL op unit (fun _ kx => Φ kx.1 kx.2) (toList (K := K) m) := by
  rfl

theorem of_list [DecidableEq K] (Φ : K → V → M) (l : List (K × V))
    (hnodup : NoDupKeys l) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.ofList l : M' V) ≡
    bigOpL op unit (fun _ kx => Φ kx.1 kx.2) l := by
  simp only [bigOpM]
  apply BigOpL.perm
  exact LawfulFiniteMap.toList_ofList hnodup

theorem singleton (Φ : K → V → M) (i : K) (x : V) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.singleton (M := M') i x) ≡ Φ i x := by
  have h := insert (op := op) (unit := unit) Φ (∅ : M' V) i x (get?_empty i)
  rw [empty] at h
  exact h.trans (Monoid.op_right_id _)

theorem unit_const [DecidableEq K] (m : M' V) :
    bigOpM (op := op) (unit := unit) (fun (_ : K) (_ : V) => unit) m ≡ unit := by
  let P : M' V → Prop := fun m' => bigOpM (op := op) (unit := unit) (fun (_ : K) (_ : V) => unit) m' ≡ unit
  have hequiv : ∀ m₁ m₂ : M' V, PartialMap.equiv m₁ m₂ → P m₁ → P m₂ :=
    fun m₁ m₂ heq h => Equiv.trans (bigOpM_equiv _ m₁ m₂ heq).symm h
  have hemp : P (∅ : M' V) := by show _ ≡ _; rw [empty]
  have hins : ∀ i x m, get? m i = none → P m → P (Iris.Std.insert m i x) :=
    fun i x m' hm' IH =>
      let h_ins := insert (op := op) (unit := unit) (fun (_ : K) (_ : V) => unit) m' i x hm'
      Equiv.trans h_ins (Equiv.trans (Monoid.op_proper Equiv.rfl IH) (Monoid.op_left_id unit))
  show P m
  exact LawfulFiniteMap.induction_on (K := K) (P := P) hequiv hemp hins m

theorem map (h : V → B) (Φ : K → B → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.map h m) ≡
    bigOpM (op := op) (unit := unit) (fun k v => Φ k (h v)) m := by
  simp only [bigOpM]
  exact (BigOpL.perm _ LawfulFiniteMap.toList_map).trans
    (BigOpL.map (op := op) (unit := unit) (fun kv => (kv.1, h kv.2)) (fun _ kv => Φ kv.1 kv.2) (toList (K := K) m))

theorem filter_map (h : V → Option V) (Φ : K → V → M) (m : M' V)
    (hinj : Function.Injective h) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.filterMap h m) ≡
    bigOpM (op := op) (unit := unit) (fun k v => (h v).elim unit (Φ k)) m := by
  simp only [bigOpM]
  refine (BigOpL.perm _ (LawfulFiniteMap.toList_filterMap hinj)).trans ?_
  refine (BigOpL.filter_map (op := op) (unit := unit) (fun kv => (h kv.2).map (kv.1, ·))
    (fun kv => Φ kv.1 kv.2) (toList (K := K) m)).trans ?_
  exact BigOpL.congr' fun _ kv => by cases hkv : h kv.2 <;> simp [Option.elim, Option.map]

theorem insert_delete (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    bigOpM (op := op) (unit := unit) Φ (Iris.Std.insert m i x) ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ (Iris.Std.delete m i)) :=
  (bigOpM_equiv Φ _ _ (fun k => (LawfulPartialMap.insert_delete (i := i) (x := x) (m := m) k).symm)).trans
    (insert Φ (Iris.Std.delete m i) i x (get?_delete_eq rfl))

theorem insert_override (Φ : K → A → M) (m : M' A) (i : K) (x x' : A) :
    get? m i = some x → Φ i x ≡ Φ i x' →
    bigOpM (op := op) (unit := unit) Φ (Iris.Std.insert m i x') ≡
      bigOpM (op := op) (unit := unit) Φ m := by
  intro hi hΦ
  exact (insert_delete Φ m i x').trans
    ((Monoid.op_proper hΦ.symm Equiv.rfl).trans (delete Φ m i x hi).symm)

theorem fn_insert [DecidableEq K] {B : Type w} (g : K → V → B → M) (f : K → B) (m : M' V)
    (i : K) (x : V) (b : B) (hi : get? m i = none) :
    bigOpM (op := op) (unit := unit) (fun k y => g k y (if k = i then b else f k))
      (Iris.Std.insert m i x) ≡
    op (g i x b) (bigOpM (op := op) (unit := unit) (fun k y => g k y (f k)) m) := by
  refine (insert _ m i x hi).trans (Monoid.op_proper (by simp) (proper _ _ _ fun k y hk => ?_))
  simp [show k ≠ i from fun heq => by subst heq; rw [hi] at hk; cases hk]

theorem fn_insert' [DecidableEq K] (f : K → M) (m : M' V) (i : K) (x : V) (P : M)
    (hi : get? m i = none) :
    bigOpM (op := op) (unit := unit) (fun k _ => if k = i then P else f k)
      (Iris.Std.insert m i x) ≡
    op P (bigOpM (op := op) (unit := unit) (fun k _ => f k) m) := by
  refine (insert _ m i x hi).trans (Monoid.op_proper (by simp) (proper _ _ _ fun k _ hk => ?_))
  simp [show k ≠ i from fun heq => by subst heq; rw [hi] at hk; cases hk]

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

theorem filter' (φ : K → V → Bool) (Φ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.filter φ m) ≡
    bigOpM (op := op) (unit := unit) (fun k x => if φ k x then Φ k x else unit) m := by
  unfold bigOpM
  have hperm := LawfulFiniteMap.toList_filter (M := M') (K := K) (V := V) (φ := φ) (m := m)
  have heq : bigOpL op unit (fun _ kv => Φ kv.1 kv.2)
               (toList (K := K) (PartialMap.filter φ m)) ≡
             bigOpL op unit (fun _ kv => Φ kv.1 kv.2)
               ((toList (K := K) m).filter (fun kv => φ kv.1 kv.2)) :=
    BigOpL.perm _ hperm
  refine Equiv.trans heq ?_
  exact filter_list_aux (fun kv => Φ kv.1 kv.2) φ (toList (K := K) m)

theorem union [DecidableEq K] (Φ : K → V → M) (m1 m2 : M' V) (hdisj : PartialMap.disjoint m1 m2) :
    bigOpM (op := op) (unit := unit) Φ (m1 ∪ m2) ≡
    op (bigOpM (op := op) (unit := unit) Φ m1) (bigOpM (op := op) (unit := unit) Φ m2) := by
  let P : M' V → Prop := fun m1 =>
    PartialMap.disjoint m1 m2 →
    bigOpM (op := op) (unit := unit) Φ (PartialMap.union m1 m2) ≡
    op (bigOpM (op := op) (unit := unit) Φ m1) (bigOpM (op := op) (unit := unit) Φ m2)
  have hequiv : ∀ m₁ m₂', PartialMap.equiv m₁ m₂' → P m₁ → P m₂' := by
    intro m₁ m₂' heq hP hdisj'
    have hunion : PartialMap.equiv (PartialMap.union m₁ m2) (PartialMap.union m₂' m2) :=
      fun k => by show get? _ k = get? _ k; rw [LawfulPartialMap.get?_union, LawfulPartialMap.get?_union, heq k]
    exact (bigOpM_equiv Φ _ _ hunion).symm.trans
      ((hP fun k hk => hdisj' k ⟨(heq k).symm ▸ hk.1, hk.2⟩).trans
        (Monoid.op_proper (bigOpM_equiv Φ m₁ m₂' heq) Equiv.rfl))
  suffices h : P m1 from h hdisj
  have hemp : P (∅ : M' V) := fun _ => by
    rw [empty]
    exact (bigOpM_equiv Φ _ _ (fun k => by
      show get? (PartialMap.union (∅ : M' V) m2) k = get? m2 k
      rw [LawfulPartialMap.get?_union, show get? (∅ : M' V) k = none from get?_empty k]; simp)).trans
      (Monoid.op_left_id _).symm
  have hins : ∀ (i : K) (x : V) (m : M' V), get? m i = none → P m → P (Iris.Std.insert m i x) := by
    intro i x m hi_none IH hdisj'
    have hi_m2 : get? m2 i = none := by
      have := (PartialMap.disjoint_iff _ m2).mp hdisj' i
      cases this with
      | inl h => rw [get?_insert_eq rfl] at h; cases h
      | inr h => exact h
    have hm_disj : PartialMap.disjoint m m2 := fun k ⟨hk1, hk2⟩ => hdisj' k ⟨by
      by_cases h : i = k
      · subst h; rw [hi_none] at hk1; cases hk1
      · rwa [get?_insert_ne h], hk2⟩
    have h_none : get? (m ∪ m2) i = none := by
      show get? (PartialMap.union m m2) i = none
      rw [LawfulPartialMap.get?_union_none]; exact ⟨hi_none, hi_m2⟩
    exact (bigOpM_equiv Φ _ _ (fun k => (LawfulPartialMap.union_insert_left (i := i) (x := x) (m₁ := m) (m₂ := m2) k).symm)).trans
      ((insert Φ (m ∪ m2) i x h_none).trans
        ((Monoid.op_congr_r (IH hm_disj)).trans
          ((Monoid.op_assoc _ _ _).symm.trans
            (Monoid.op_congr_l (insert Φ m i x hi_none).symm))))
  exact LawfulFiniteMap.induction_on (K := K) (P := P) hequiv hemp hins m1

theorem op_distr (Φ Ψ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) (fun k x => op (Φ k x) (Ψ k x)) m ≡
    op (bigOpM (op := op) (unit := unit) Φ m) (bigOpM (op := op) (unit := unit) Ψ m) := by
  simp only [bigOpM]
  exact BigOpL.op_distr (op := op) (unit := unit)
    (fun _ kv => Φ kv.1 kv.2) (fun _ kv => Ψ kv.1 kv.2) (toList (K := K) m)

private theorem closed_aux [DecidableEq K] (P : M → Prop) (Φ : K → V → M)
    (hproper : ∀ x y, x ≡ y → (P x ↔ P y))
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y)) :
    ∀ (m' : M' V), (∀ k' x', get? m' k' = some x' → P (Φ k' x')) →
        P (bigOpM (op := op) (unit := unit) Φ m') := by
  intro m' hf'
  let Q : M' V → Prop := fun m'' => (∀ k x, get? m'' k = some x → P (Φ k x)) →
                     P (bigOpM (op := op) (unit := unit) Φ m'')
  have hequiv_Q : ∀ m₁ m₂, PartialMap.equiv m₁ m₂ → Q m₁ → Q m₂ :=
    fun m₁ m₂ heq hQ hf => (hproper _ _ (bigOpM_equiv Φ m₁ m₂ heq)).mp
      (hQ fun k x hget => hf k x ((heq k) ▸ hget))
  have hemp_Q : Q (∅ : M' V) := fun _ => by
    show P (bigOpM (op := op) (unit := unit) Φ (∅ : M' V)); rw [empty]; exact hunit
  have hins_Q : ∀ i x m, get? m i = none → Q m → Q (Iris.Std.insert m i x) := by
    intro k x m'' hm'' IH hf''
    exact (hproper _ _ (insert (op := op) (unit := unit) Φ m'' k x hm'')).mpr
      (hop _ _ (hf'' _ _ (get?_insert_eq rfl)) (IH fun k' x' hget' => by
        by_cases heq : k = k'
        · subst heq; rw [hget'] at hm''; cases hm''
        · exact hf'' k' x' (by rw [get?_insert_ne heq]; exact hget')))
  exact (LawfulFiniteMap.induction_on (K := K) (P := Q) hequiv_Q hemp_Q hins_Q m') hf'

theorem closed [DecidableEq K] (P : M → Prop) (Φ : K → V → M) (m : M' V)
    (hproper : ∀ x y, x ≡ y → (P x ↔ P y))
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ k x, get? m k = some x → P (Φ k x)) :
    P (bigOpM (op := op) (unit := unit) Φ m) :=
  closed_aux P Φ hproper hunit hop m hf

-- TODO: kmap and map_seq are skipped for now

theorem sep_zip_with {A : Type _} {B : Type _} {C : Type _}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (h1 : K → A → M) (h2 : K → B → M) (m1 : M' A) (m2 : M' B)
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    bigOpM (op := op) (unit := unit) (fun k xy => op (h1 k (g1 xy)) (h2 k (g2 xy)))
      (PartialMap.zipWith f m1 m2) ≡
    op (bigOpM (op := op) (unit := unit) h1 m1) (bigOpM (op := op) (unit := unit) h2 m2) := by
  have h_op := @op_distr _ _ op unit _ _ _ _ _
    (fun k xy => h1 k (g1 xy)) (fun k xy => h2 k (g2 xy)) (PartialMap.zipWith f m1 m2)
  apply Equiv.trans h_op
  have map_g1_eq : PartialMap.equiv (PartialMap.map g1 (PartialMap.zipWith f m1 m2)) m1 := by
    intro k
    simp only [LawfulPartialMap.get?_map, LawfulPartialMap.get?_zipWith]
    cases h1k : get? m1 k with
    | none => simp [Option.bind]
    | some a =>
      have := (hdom k).mp (by rw [h1k]; simp)
      cases h2k : get? m2 k with
      | none => rw [h2k] at this; simp at this
      | some b => simp [Option.bind, Option.map, hg1]
  have map_g2_eq : PartialMap.equiv (PartialMap.map g2 (PartialMap.zipWith f m1 m2)) m2 := by
    intro k
    simp only [LawfulPartialMap.get?_map, LawfulPartialMap.get?_zipWith]
    cases h1k : get? m1 k with
    | none =>
      simp [Option.bind]
      cases h2k : get? m2 k with
      | none => rfl
      | some b =>
        have := (hdom k).mpr (by rw [h2k]; simp)
        rw [h1k] at this; simp at this
    | some a =>
      cases h2k : get? m2 k with
      | none =>
        have := (hdom k).mp (by rw [h1k]; simp)
        rw [h2k] at this; simp at this
      | some b => simp [Option.bind, Option.map, hg2]
  apply Monoid.op_proper
  · have h1_fmap := map (op := op) (unit := unit) g1 h1 (PartialMap.zipWith f m1 m2)
    exact Equiv.trans (Equiv.symm h1_fmap) (bigOpM_equiv h1 _ _ map_g1_eq)
  · have h2_fmap := map (op := op) (unit := unit) g2 h2 (PartialMap.zipWith f m1 m2)
    exact Equiv.trans (Equiv.symm h2_fmap) (bigOpM_equiv h2 _ _ map_g2_eq)

theorem sep_zip {A : Type _} {B : Type _}
    (h1 : K → A → M) (h2 : K → B → M) (m1 : M' A) (m2 : M' B)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    bigOpM (op := op) (unit := unit) (fun k xy => op (h1 k xy.1) (h2 k xy.2))
      (PartialMap.zip m1 m2) ≡
    op (bigOpM (op := op) (unit := unit) h1 m1) (bigOpM (op := op) (unit := unit) h2 m2) := by
  simp only [PartialMap.zip]
  exact sep_zip_with (op := op) (unit := unit) Prod.mk Prod.fst Prod.snd h1 h2 m1 m2
    (fun _ _ => rfl) (fun _ _ => rfl) hdom

end BigOpM

end Iris.Algebra
