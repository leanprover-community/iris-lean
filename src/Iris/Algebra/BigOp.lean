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
  simp only [cons, nil]; exact Monoid.op_right_id _

theorem congr {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x ≡ Ψ i x) :
    bigOpL op unit Φ l ≡ bigOpL op unit Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => exact Equiv.rfl
  | cons y ys ih =>
    simp only [cons]
    apply Monoid.op_proper (h 0 y rfl)
    exact ih fun i x hget => h (i + 1) x hget

theorem congr_dist {Φ Ψ : Nat → A → M} {l : List A} {n : Nat}
    (h : ∀ i x, l[i]? = some x → Φ i x ≡{n}≡ Ψ i x) :
    bigOpL op unit Φ l ≡{n}≡ bigOpL op unit Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => exact Dist.rfl
  | cons y ys ih =>
    simp only [cons]
    apply Monoid.op_ne_dist (h 0 y rfl)
    exact ih fun i x hget => h (i + 1) x hget

/-- Congruence when the functions are equivalent on all indices. -/
theorem congr_forall {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, Φ i x ≡ Ψ i x) :
    bigOpL op unit Φ l ≡ bigOpL op unit Ψ l :=
  congr (fun i x _ => h i x)

theorem append (Φ : Nat → A → M) (l₁ l₂ : List A) :
    bigOpL op unit Φ (l₁ ++ l₂) ≡
      op (bigOpL op unit Φ l₁) (bigOpL op unit (fun n => Φ (n + l₁.length)) l₂) := by
  induction l₁ generalizing Φ with
  | nil => simp only [nil]; exact (Monoid.op_left_id _).symm
  | cons x xs ih =>
    simp only [List.cons_append, cons, List.length_cons]
    apply (Monoid.op_congr_r (ih _)).trans
    simp only [show ∀ n, n + xs.length + 1 = n + (xs.length + 1) from by omega]
    exact (Monoid.op_assoc _ _ _).symm

theorem snoc (Φ : Nat → A → M) (l : List A) (x : A) :
    bigOpL op unit Φ (l ++ [x]) ≡ op (bigOpL op unit Φ l) (Φ l.length x) := by
  have := @append _ _ _ op unit _ Φ l [x]
  simp only [cons, nil, Nat.zero_add] at this
  exact this.trans (Monoid.op_congr_r (Monoid.op_right_id _))

theorem const_unit (l : List A) :
    bigOpL op unit (fun _ _ => unit) l ≡ unit := by
  induction l with
  | nil => exact Equiv.rfl
  | cons _ _ ih =>
    simp only [cons]
    exact (Monoid.op_left_id _).trans ih

theorem op_distrib (Φ Ψ : Nat → A → M) (l : List A) :
    bigOpL op unit (fun i x => op (Φ i x) (Ψ i x)) l ≡
      op (bigOpL op unit Φ l) (bigOpL op unit Ψ l) := by
  induction l generalizing Φ Ψ with
  | nil => simp only [nil]; exact Equiv.symm (Monoid.op_left_id _)
  | cons x xs ih =>
    simp only [cons]
    exact (Monoid.op_congr_r (ih _ _)).trans Monoid.op_op_swap

theorem map {B : Type v} (h : A → B) (Φ : Nat → B → M) (l : List A) :
    bigOpL op unit Φ (l.map h) ≡ bigOpL op unit (fun i x => Φ i (h x)) l := by
  induction l generalizing Φ with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, cons]
    exact Monoid.op_proper Equiv.rfl (ih _)

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
  · have := @append M A _ op unit _ Φ (l.take n) (l.drop n)
    simp only [List.take_append_drop, List.length_take_of_le hn, Nat.add_comm] at this
    exact this
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
    exact (append _ _ _).trans (Monoid.op_congr_r ih)

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
      exact hop _ _ _ _ (hf 0 x y rfl rfl)
        (ih _ _ _ hlen fun i a b ha hb => hf (i + 1) a b ha hb)

omit [OFE M] [Monoid M op unit] in
theorem gen_proper (R : M → M → Prop)
    (Φ Ψ : Nat → A → M) (l : List A)
    (hR_refl : ∀ x, R x x)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ k y, l[k]? = some y → R (Φ k y) (Ψ k y)) :
    R (bigOpL op unit Φ l) (bigOpL op unit Ψ l) := by
  apply gen_proper_2 (op := op) (unit := unit) R Φ Ψ l l (hR_refl unit) hR_op rfl
  intro k x y hx hy; rw [hx] at hy; cases hy; exact hf k x hx

omit [OFE M] [Monoid M op unit] in
theorem ext {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x = Ψ i x) :
    bigOpL op unit Φ l = bigOpL op unit Ψ l :=
  gen_proper (· = ·) _ _ _ (fun _ => rfl) (fun _ _ _ _ ha hb => ha ▸ hb ▸ rfl) h

theorem proper_2 [OFE A] (Φ Ψ : Nat → A → M) (l₁ l₂ : List A)
    (hlen : l₁.length = l₂.length)
    (hf : ∀ (k : Nat) (y₁ y₂ : A), l₁[k]? = some y₁ → l₂[k]? = some y₂ → Φ k y₁ ≡ Ψ k y₂) :
    bigOpL op unit Φ l₁ ≡ bigOpL op unit Ψ l₂ := by
  exact gen_proper_2 (op := op) (unit := unit) (· ≡ ·) Φ Ψ l₁ l₂ Equiv.rfl
    (fun _ _ _ _ => Monoid.op_proper) hlen hf

theorem zipIdx (Φ : A × Nat → M) (n : Nat) (l : List A) :
    bigOpL op unit (fun _ => Φ) (l.zipIdx n) ≡
      bigOpL op unit (fun i x => Φ (x, n + i)) l := by
  induction l generalizing n with
  | nil => simp only [nil]; exact Equiv.rfl
  | cons x xs ih =>
    simp only [cons, Nat.add_zero]
    exact Monoid.op_proper Equiv.rfl
      ((ih (n + 1)).trans (congr_forall fun i _ => by simp [Nat.add_assoc, Nat.add_comm 1 i]))

theorem zipIdxInt (Φ : A × Int → M) (n : Int) (l : List A) :
    bigOpL op unit (fun _ => Φ) (Std.List.zipIdxInt l n) ≡
      bigOpL op unit (fun i x => Φ (x, n + (i : Int))) l := by
  unfold Std.List.zipIdxInt
  suffices ∀ m, bigOpL op unit (fun _ => Φ) (l.mapIdx (fun i v => (v, (i : Int) + m))) ≡
                bigOpL op unit (fun i x => Φ (x, m + (i : Int))) l from this n
  intro m
  induction l generalizing m with
  | nil => simp only [List.mapIdx, nil]; exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.mapIdx_cons, cons]
    apply Monoid.op_proper
    · show Φ (x, (0 : Int) + m) ≡ Φ (x, m + (0 : Int))
      rw [Int.zero_add, Int.add_zero]
    · rw [show (List.mapIdx (fun i v => (v, ↑(i + 1) + m)) xs) =
              (List.mapIdx (fun i v => (v, ↑i + (m + 1))) xs) from by
        apply List.ext_getElem (by simp only [List.length_mapIdx])
        intro n hn1 hn2
        simp only [List.getElem_mapIdx]; congr 1; omega]
      apply (ih (m + 1)).trans
      apply congr_forall fun i _ => ?_
      rw [show m + 1 + (i : Int) = m + ((i + 1 : Nat) : Int) from by omega]

theorem op_zipWith {B C : Type _}
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
      exact (Monoid.op_congr_r (ih _ _ _ hlen)).trans Monoid.op_op_swap

/-- Big op over zipped list with separated functions. -/
theorem op_zip {B : Type v} (Φ : Nat → A → M) (Ψ : Nat → B → M) (l₁ : List A) (l₂ : List B)
    (hlen : l₁.length = l₂.length) :
    bigOpL op unit (fun i xy => op (Φ i xy.1) (Ψ i xy.2)) (l₁.zip l₂) ≡
      op (bigOpL op unit Φ l₁) (bigOpL op unit Ψ l₂) := by
  simp only [List.zip]
  exact op_zipWith (op := op) _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) hlen

variable {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
variable {op₁ : M₁ → M₁ → M₁} {op₂ : M₂ → M₂ → M₂} {unit₁ : M₁} {unit₂ : M₂}
variable [Monoid M₁ op₁ unit₁] [Monoid M₂ op₂ unit₂]
variable {B : Type w}

/-- Monoid homomorphisms distribute over big ops. -/
theorem hom {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : MonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : Nat → B → M₁) (l : List B) :
    R (f (bigOpL op₁ unit₁ Φ l)) (bigOpL op₂ unit₂ (fun i x => f (Φ i x)) l) := by
  induction l generalizing Φ with
  | nil => simp only [nil]; exact hom.map_unit
  | cons x xs ih =>
    simp only [cons]
    apply hom.rel_trans (hom.homomorphism _ _)
    exact hom.op_proper (hom.rel_refl _) (ih _)

/-- Weak monoid homomorphisms distribute over non-empty big ops. -/
theorem hom_weak {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
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
      apply (hom.rel_proper (NonExpansive.eqv (Monoid.op_right_id _))
        (Monoid.op_right_id _)).mpr
      exact hom.rel_refl _
    | cons y ys =>
      apply hom.rel_trans (hom.homomorphism _ _)
      exact hom.op_proper (hom.rel_refl _) (ih _ (List.cons_ne_nil y ys))

end BigOpL

namespace BigOpM

open Iris.Std

variable {M : Type u} [OFE M] {op : M → M → M} {unit : M} [Monoid M op unit]
variable {M' : Type _ → Type _} {K : Type _} {V : Type _}
variable [LawfulFiniteMap M' K]

def bigOpM (Φ : K → V → M) (m : M' V) : M :=
  bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (toList (K := K) m)

theorem equiv (Φ : K → V → M) (m₁ m₂ : M' V)
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
  apply (BigOpM.equiv Φ m _ (fun k => (LawfulPartialMap.insert_delete_cancel hi k).symm)).trans
  exact insert Φ (Iris.Std.delete m i) _ _ (get?_delete_eq rfl)

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
  apply LawfulFiniteMap.induction_on (K := K) (P := P1)
  · intro m₁ m₂ heq hP m2' Φ' Ψ' hfg'
    apply hR_equiv.trans (hR_sub _ _ (BigOpM.equiv Φ' m₁ m₂ heq).symm)
    exact hP m2' Φ' Ψ' (fun k => by rw [heq k]; exact hfg' k)
  · show P1 (∅ : M' A)
    intro m2' Φ' Ψ' hfg'
    let P2 : M' B → Prop := fun m2'' => ∀ (Φ'' : K → A → M) (Ψ'' : K → B → M),
        (∀ k, match get? (∅ : M' A) k, get? m2'' k with
          | some y1, some y2 => R (Φ'' k y1) (Ψ'' k y2)
          | none, none => True
          | _, _ => False) →
        R (bigOpM (op := op) (unit := unit) Φ'' (∅ : M' A)) (bigOpM (op := op) (unit := unit) Ψ'' m2'')
    suffices h2 : P2 m2' from h2 Φ' Ψ' hfg'
    apply LawfulFiniteMap.induction_on (K := K) (P := P2)
    · intro m₁ m₂ heq hP Φ'' Ψ'' hfg''
      apply hR_equiv.trans (hP Φ'' Ψ'' (fun k => by rw [heq k]; exact hfg'' k))
      exact hR_sub _ _ (BigOpM.equiv Ψ'' m₁ m₂ heq)
    · show P2 (∅ : M' B)
      intro _ _ _
      show R (bigOpM (op := op) _ (∅ : M' A)) (bigOpM (op := op)  _ (∅ : M' B))
      rw [empty, empty]; exact hR_sub unit unit Equiv.rfl
    · intro k _ _ _ _ Φ'' Ψ'' hfg''
      have := hfg'' k
      rw [show get? (∅ : M' A) k = none from get?_empty k, get?_insert_eq rfl] at this
      exact this.elim
  · intro k x1 m1' hm1'k IH m2' Φ' Ψ' hfg'
    have hfg_k := hfg' k
    rw [get?_insert_eq rfl] at hfg_k
    cases hm2k : get? m2' k with
    | none => rw [hm2k] at hfg_k; cases hfg_k
    | some x2 =>
      rw [hm2k] at hfg_k
      refine hR_equiv.trans (hR_sub _ _ (insert Φ' m1' k x1 hm1'k)) ?_
      apply hR_equiv.trans _ (hR_sub _ _ (Equiv.symm (delete Ψ' m2' k x2 hm2k)))
      apply hR_op _ _ _ _ hfg_k
      apply IH
      intro k'
      by_cases hkk' : k = k'
      · subst hkk'; rw [get?_delete_eq rfl, hm1'k]; trivial
      · have := hfg' k'; rw [get?_insert_ne hkk'] at this; rwa [get?_delete_ne hkk']

omit [Monoid M op unit] in
theorem gen_proper {M : Type u} {op : M → M → M} {unit : M} (R : M → M → Prop)
    (Φ Ψ : K → V → M) (m : M' V)
    (hR_refl : ∀ x, R x x)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ k x, get? m k = some x → R (Φ k x) (Ψ k x)) :
    R (bigOpM (op := op) (unit := unit) Φ m) (bigOpM (op := op) (unit := unit) Ψ m) := by
  simp only [bigOpM]
  apply BigOpL.gen_proper_2 (op := op) (unit := unit) R _ _ _ _ (hR_refl unit) hR_op rfl
  intro i x y hx hy; rw [hx] at hy; cases hy
  exact hf x.1 x.2 (toList_get.mp (List.mem_iff_getElem?.mpr ⟨i, hx⟩))

theorem ext {M : Type u} (op : M → M → M) (unit : M) (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, get? m k = some x → Φ k x = Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m = bigOpM (op := op) (unit := unit) Ψ m :=
  gen_proper (R := (· = ·)) _ _ _ (fun _ => rfl) (fun _ _ _ _ ha hb => ha ▸ hb ▸ rfl) hf

theorem dist (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, get? m k = some x → Φ k x ≡{n}≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡{n}≡ bigOpM (op := op) (unit := unit) Ψ m :=
  gen_proper (R := (· ≡{n}≡ ·)) _ _ _ (fun _ => Dist.rfl) (fun _ _ _ _ => Monoid.op_ne_dist) hf

theorem proper (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, get? m k = some x → Φ k x ≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡ bigOpM (op := op) (unit := unit) Ψ m :=
  gen_proper (R := (· ≡ ·)) _ _ _ (fun _ => Equiv.rfl) (fun _ _ _ _ => Monoid.op_proper) hf

theorem proper_2 [DecidableEq K] [OFE A] (Φ : K → A → M) (Ψ : K → A → M) (m1 m2 : M' A)
    (hm : ∀ k, get? m1 k = get? m2 k)
    (hf : ∀ k y1 y2,
      get? m1 k = some y1 →
      get? m2 k = some y2 →
      y1 ≡ y2 →
      Φ k y1 ≡ Ψ k y2) :
    bigOpM (op := op) (unit := unit) Φ m1 ≡ bigOpM (op := op) (unit := unit) Ψ m2 := by
  apply gen_proper_2 (R := (· ≡ ·)) _ _ _ _ (fun _ _ h => h) equiv_eqv (fun _ _ _ _ => Monoid.op_proper)
  intro k
  have hlk := hm k
  cases hm1k : get? m1 k with
  | none => rw [hm1k] at hlk; rw [← hlk]; trivial
  | some y1 =>
    rw [hm1k] at hlk
    cases hm2k : get? m2 k with
    | none => rw [hm2k] at hlk; cases hlk
    | some y2 => rw [hm2k] at hlk; cases hlk; exact hf k y1 y1 hm1k hm2k Equiv.rfl

theorem dist_pointwise (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, Φ k x ≡{n}≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡{n}≡ bigOpM (op := op) (unit := unit) Ψ m :=
  dist _ _ _ _ fun k x _ => hf k x

theorem proper_pointwise (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, Φ k x ≡ Ψ k x) :
    bigOpM (op := op) (unit := unit) Φ m ≡ bigOpM (op := op) (unit := unit) Ψ m :=
  proper _ _ _ fun k x _ => hf k x

omit [Monoid M op unit] in
theorem to_list (Φ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ m ≡
    bigOpL op unit (fun _ kx => Φ kx.1 kx.2) (toList (K := K) m) := by rfl

theorem of_list [DecidableEq K] (Φ : K → V → M) (l : List (K × V))
    (hnodup : NoDupKeys l) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.ofList l : M' V) ≡
    bigOpL op unit (fun _ kx => Φ kx.1 kx.2) l := by
  simp only [bigOpM]; exact BigOpL.perm _ (LawfulFiniteMap.toList_ofList hnodup)

theorem singleton (Φ : K → V → M) (i : K) (x : V) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.singleton (M := M') i x) ≡ Φ i x := by
  rw [show PartialMap.singleton (M := M') i x = Iris.Std.insert (∅ : M' V) i x from rfl]
  apply (insert Φ (∅ : M' V) i x (get?_empty i)).trans
  rw [empty]; exact Monoid.op_right_id _

theorem const_unit [DecidableEq K] (m : M' V) :
    bigOpM (op := op) (unit := unit) (fun (_ : K) (_ : V) => unit) m ≡ unit := by
  let P : M' V → Prop := fun m' => bigOpM (op := op) (unit := unit) (fun (_ : K) (_ : V) => unit) m' ≡ unit
  show P m; apply LawfulFiniteMap.induction_on (K := K) (P := P)
  · intro m₁ m₂ heq h; exact (BigOpM.equiv _ _ _ heq).symm.trans h
  · show P (∅ : M' V); show _ ≡ _; rw [empty]
  · intro i x m' hm' IH
    exact (insert _ _ _ _ hm').trans ((Monoid.op_proper Equiv.rfl IH).trans (Monoid.op_left_id _))

theorem map (h : V → B) (Φ : K → B → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.map h m) ≡
    bigOpM (op := op) (unit := unit) (fun k v => Φ k (h v)) m := by
  simp only [bigOpM]
  exact (BigOpL.perm _ LawfulFiniteMap.toList_map).trans
    (BigOpL.map (op := op) _ _ (toList (K := K) m))

theorem filter_map (h : V → Option V) (Φ : K → V → M) (m : M' V)
    (hinj : Function.Injective h) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.filterMap h m) ≡
    bigOpM (op := op) (unit := unit) (fun k v => (h v).elim unit (Φ k)) m := by
  simp only [bigOpM]
  exact (BigOpL.perm _ (LawfulFiniteMap.toList_filterMap hinj)).trans
    ((BigOpL.filter_map (op := op) _ _ _).trans
      (BigOpL.congr_forall fun _ kv => by cases hkv : h kv.2 <;> simp [Option.elim, Option.map]))

theorem insert_delete (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    bigOpM (op := op) (unit := unit) Φ (Iris.Std.insert m i x) ≡
      op (Φ i x) (bigOpM (op := op) (unit := unit) Φ (Iris.Std.delete m i)) := by
  exact (BigOpM.equiv _ _ _ fun k => (LawfulPartialMap.insert_delete k).symm).trans
    (insert _ _ _ _ (get?_delete_eq rfl))

theorem insert_override (Φ : K → A → M) (m : M' A) (i : K) (x x' : A) :
    get? m i = some x → Φ i x ≡ Φ i x' →
    bigOpM (op := op) (unit := unit) Φ (Iris.Std.insert m i x') ≡
      bigOpM (op := op) (unit := unit) Φ m := by
  intro hi hΦ
  apply (insert_delete Φ m i x').trans
  exact (Monoid.op_proper hΦ.symm Equiv.rfl).trans (delete Φ m i x hi).symm

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

theorem filter (φ : K → V → Bool) (Φ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) Φ (PartialMap.filter φ m) ≡
    bigOpM (op := op) (unit := unit) (fun k x => if φ k x then Φ k x else unit) m := by
  unfold bigOpM
  refine (BigOpL.perm _ LawfulFiniteMap.toList_filter).trans ?_
  suffices ∀ l : List (K × V),
      bigOpL op unit (fun _ kv => Φ kv.1 kv.2) (l.filter (fun kv => φ kv.1 kv.2)) ≡
      bigOpL op unit (fun _ kv => if φ kv.1 kv.2 then Φ kv.1 kv.2 else unit) l from this _
  intro l
  induction l with
  | nil => exact Equiv.rfl
  | cons kv kvs ih =>
    simp only [List.filter]
    cases hp : φ kv.1 kv.2 with
    | false =>
      simp only [BigOpL.cons, hp]
      exact Equiv.trans ih (Equiv.symm (Monoid.op_left_id _))
    | true =>
      simp only [BigOpL.cons, hp, ite_true]
      exact Monoid.op_congr_r ih

theorem union [DecidableEq K] (Φ : K → V → M) (m1 m2 : M' V) (hdisj : PartialMap.disjoint m1 m2) :
    bigOpM (op := op) (unit := unit) Φ (m1 ∪ m2) ≡
    op (bigOpM (op := op) (unit := unit) Φ m1) (bigOpM (op := op) (unit := unit) Φ m2) := by
  let P : M' V → Prop := fun m1 =>
    PartialMap.disjoint m1 m2 →
    bigOpM (op := op) (unit := unit) Φ (PartialMap.union m1 m2) ≡
    op (bigOpM (op := op) (unit := unit) Φ m1) (bigOpM (op := op) (unit := unit) Φ m2)
  suffices h : P m1 from h hdisj
  apply LawfulFiniteMap.induction_on (K := K) (P := P)
  · intro m₁ m₂' heq hP hdisj'
    refine Equiv.trans ?_ ((hP fun k hk => hdisj' k ⟨(heq k).symm ▸ hk.1, hk.2⟩).trans
      (Monoid.op_proper (BigOpM.equiv Φ m₁ m₂' heq) Equiv.rfl))
    apply Equiv.symm
    apply BigOpM.equiv Φ _ _ fun k => ?_
    show get? _ k = get? _ k
    rw [LawfulPartialMap.get?_union, LawfulPartialMap.get?_union, heq k]
  · show P (∅ : M' V)
    intro _; rw [empty]
    refine Equiv.trans ?_ (Monoid.op_left_id _).symm
    apply BigOpM.equiv Φ _ _
    intro k; show get? (PartialMap.union (∅ : M' V) m2) k = get? m2 k
    rw [LawfulPartialMap.get?_union, show get? (∅ : M' V) k = none from get?_empty k]; simp
  · intro i x m hi_none IH hdisj'
    apply (BigOpM.equiv Φ _ _ fun k => (LawfulPartialMap.union_insert_left k).symm).trans
    apply (insert Φ (m ∪ m2) i x (by
      show get? (PartialMap.union m m2) i = none
      rw [LawfulPartialMap.get?_union_none]
      refine ⟨hi_none, ?_⟩
      cases (PartialMap.disjoint_iff _ m2).mp hdisj' i with
      | inl h => rw [get?_insert_eq rfl] at h; cases h
      | inr h => exact h)).trans
    apply (Monoid.op_congr_r (IH fun k ⟨hk1, hk2⟩ => hdisj' k ⟨by
      by_cases h : i = k
      · subst h; rw [hi_none] at hk1; cases hk1
      · rwa [get?_insert_ne h], hk2⟩)).trans
    exact (Monoid.op_assoc _ _ _).symm.trans (Monoid.op_congr_l (insert Φ m i x hi_none).symm)

theorem op_distrib (Φ Ψ : K → V → M) (m : M' V) :
    bigOpM (op := op) (unit := unit) (fun k x => op (Φ k x) (Ψ k x)) m ≡
    op (bigOpM (op := op) (unit := unit) Φ m) (bigOpM (op := op) (unit := unit) Ψ m) := by
  simp only [bigOpM]; exact BigOpL.op_distrib _ _ _

theorem closed [DecidableEq K] (P : M → Prop) (Φ : K → V → M) (m : M' V)
    (hproper : ∀ x y, x ≡ y → (P x ↔ P y))
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ k x, get? m k = some x → P (Φ k x)) :
    P (bigOpM (op := op) (unit := unit) Φ m) := by
  let Q : M' V → Prop := fun m'' => (∀ k x, get? m'' k = some x → P (Φ k x)) →
                     P (bigOpM (op := op) (unit := unit) Φ m'')
  suffices h : Q m from h hf
  apply LawfulFiniteMap.induction_on (K := K) (P := Q)
  · intro m₁ m₂ heq hQ hf'
    apply (hproper _ _ (BigOpM.equiv Φ m₁ m₂ heq)).mp
    exact hQ fun k x hget => hf' k x ((heq k) ▸ hget)
  · show Q (∅ : M' V)
    intro _; show P (bigOpM Φ (∅ : M' V)); rw [empty]; exact hunit
  · intro k x m'' hm'' IH hf''
    apply (hproper _ _ (insert Φ m'' k x hm'')).mpr
    apply hop _ _ (hf'' _ _ (get?_insert_eq rfl))
    apply IH; intro k' x' hget'
    by_cases heq : k = k'
    · subst heq; rw [hget'] at hm''; cases hm''
    · apply hf'' k' x'
      rw [get?_insert_ne heq]; exact hget'

-- TODO: kmap and map_seq are skipped for now

theorem op_zipWith {A : Type _} {B : Type _} {C : Type _}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (h1 : K → A → M) (h2 : K → B → M) (m1 : M' A) (m2 : M' B)
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    bigOpM (op := op) (unit := unit) (fun k xy => op (h1 k (g1 xy)) (h2 k (g2 xy)))
      (PartialMap.zipWith f m1 m2) ≡
    op (bigOpM (op := op) (unit := unit) h1 m1) (bigOpM (op := op) (unit := unit) h2 m2) := by
  refine (op_distrib (fun k xy => h1 k (g1 xy)) (fun k xy => h2 k (g2 xy))
    (PartialMap.zipWith f m1 m2)).trans ?_
  apply Monoid.op_proper
  · refine (map g1 h1 (PartialMap.zipWith f m1 m2)).symm.trans ?_
    apply BigOpM.equiv h1 _ _
    intro k
    simp only [LawfulPartialMap.get?_map, LawfulPartialMap.get?_zipWith]
    cases h1k : get? m1 k with
    | none => simp [Option.bind]
    | some a =>
      have := (hdom k).mp (by rw [h1k]; simp)
      cases h2k : get? m2 k with
      | none => rw [h2k] at this; simp at this
      | some b => simp [Option.bind, Option.map, hg1]
  · refine (map g2 h2 (PartialMap.zipWith f m1 m2)).symm.trans ?_
    apply BigOpM.equiv h2 _ _
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

theorem op_zip {A : Type _} {B : Type _}
    (h1 : K → A → M) (h2 : K → B → M) (m1 : M' A) (m2 : M' B)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    bigOpM (op := op) (unit := unit) (fun k xy => op (h1 k xy.1) (h2 k xy.2))
      (PartialMap.zip m1 m2) ≡
    op (bigOpM (op := op) (unit := unit) h1 m1) (bigOpM (op := op) (unit := unit) h2 m2) := by
  simp only [PartialMap.zip]
  exact op_zipWith _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) hdom

end BigOpM

end Iris.Algebra
