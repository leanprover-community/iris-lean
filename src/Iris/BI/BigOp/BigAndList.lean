/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.DerivedLawsLater

namespace Iris.BI

open Iris.Algebra BigOpL
open BIBase

/-! # Big Conjunction over Lists -/

variable {PROP : Type _} [BI PROP] {A : Type _}

namespace BigAndL

@[simp]
theorem nil {Φ : Nat → A → PROP} :
    ([∧list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ iprop(True) := .rfl

theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∧list] k ↦ y ∈ (x :: xs), Φ k y) ⊣⊢ Φ 0 x ∧ [∧list] n ↦ y ∈ xs, Φ (n + 1) y := .rfl

theorem singleton {Φ : Nat → A → PROP} {x : A} :
    ([∧list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x := equiv_iff.mp (bigOpL_singleton_equiv Φ x)

theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∧list] k ↦ x ∈ (l₁ ++ l₂), Φ k x) ⊣⊢
      ([∧list] k ↦ x ∈ l₁, Φ k x) ∧ [∧list] n ↦ x ∈ l₂, Φ (n + l₁.length) x :=
  equiv_iff.mp (bigOpL_append_equiv Φ l₁ l₂)

theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∧list] k ↦ y ∈ (l ++ [x]), Φ k y) ⊣⊢ ([∧list] k ↦ y ∈ l, Φ k y) ∧ Φ l.length x :=
  equiv_iff.mp (bigOpL_snoc_equiv Φ l x)

theorem mono {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ⊢ [∧list] k ↦ x ∈ l, Ψ k x := by
  induction l generalizing Φ Ψ with
  | nil => exact Entails.rfl
  | cons y ys ih =>
    exact and_mono (h 0 y rfl) (ih fun k x hget => h (k + 1) x hget)

theorem proper {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡ [∧list] k ↦ x ∈ l, Ψ k x := bigOpL_equiv h

theorem congr {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Φ k x ≡ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡ [∧list] k ↦ x ∈ l, Ψ k x := bigOpL_equiv_of_forall_equiv h

instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∧list] k ↦ x ∈ l, Φ k x) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigOpL]
      exact persistently_true.2
    | cons x xs ih =>
      simp only [bigOpL]
      exact (and_mono Persistent.persistent ih).trans persistently_and.2

instance affine {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    Affine ([∧list] k ↦ x ∈ l, Φ k x) where
  affine := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigOpL]
      exact true_emp.1
    | cons x xs ih =>
      simp only [bigOpL]
      exact and_elim_l.trans Affine.affine

theorem true_l {l : List A} :
    ([∧list] _x ∈ l, iprop(True : PROP)) ≡ iprop(True) := bigOpL_const_unit_equiv

theorem and' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, iprop(Φ k x ∧ Ψ k x)) ≡
      iprop(([∧list] k ↦ x ∈ l, Φ k x) ∧ [∧list] k ↦ x ∈ l, Ψ k x) := bigOpL_op_equiv Φ Ψ l

theorem and_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    iprop(([∧list] k ↦ x ∈ l, Φ k x) ∧ [∧list] k ↦ x ∈ l, Ψ k x) ≡
      [∧list] k ↦ x ∈ l, iprop(Φ k x ∧ Ψ k x) := and'.symm

theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡
      iprop(([∧list] k ↦ x ∈ (l.take n), Φ k x) ∧ [∧list] k ↦ x ∈ (l.drop n), Φ (n + k) x) :=
  bigOpL_take_drop_equiv Φ l n

theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∧list] k ↦ y ∈ (l.map f), Φ k y) ≡ [∧list] k ↦ x ∈ l, Φ k (f x) := bigOpL_map_equiv f Φ l

theorem lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    ([∧list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x := by
  induction l generalizing i Φ with
  | nil => simp at h
  | cons y ys ih =>
    simp only [bigOpL]
    cases i with
    | zero =>
      simp at h
      subst h
      exact and_elim_l
    | succ j =>
      simp at h
      exact and_elim_r.trans (ih h)

theorem intro {P : PROP} {Φ : Nat → A → PROP} {l : List A} (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ [∧list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigOpL]
    exact true_intro
  | cons y ys ih =>
    simp only [bigOpL]
    apply and_intro
    · exact h 0 y rfl
    · exact ih (fun k x hget => h (k + 1) x hget)

theorem forall' {Φ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) := by
  constructor
  · exact forall_intro fun k => forall_intro fun x =>
      imp_intro <| and_comm.1.trans <| pure_elim_l (lookup ·)
  · induction l generalizing Φ with
    | nil => exact true_intro
    | cons y ys ih =>
      simp only [bigOpL]
      exact and_intro
        ((forall_elim 0).trans <| (forall_elim y).trans <|
          (imp_congr_l (pure_true rfl)).1.trans true_imp.1)
        ((forall_intro fun k => forall_intro fun x => (forall_elim (k + 1)).trans (forall_elim x)).trans
          (ih (Φ := fun k x => Φ (k + 1) x)))

theorem impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, Φ k x) ∧ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢
      [∧list] k ↦ x ∈ l, Ψ k x :=
  intro fun k x hget =>
    (and_mono (lookup hget) ((forall_elim k).trans (forall_elim x))).trans <|
      (and_mono .rfl ((and_intro (pure_intro hget) .rfl).trans imp_elim_r)).trans imp_elim_r

theorem persistently {Φ : Nat → A → PROP} {l : List A} :
    (<pers> [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, <pers> Φ k x :=
  equiv_iff.mp <| bigOpL_hom (H := {
    rel_refl := .rfl
    rel_trans := .trans
    rel_proper := fun ha hb => ⟨fun h => ha.symm.trans (h.trans hb), fun h => ha.trans (h.trans hb.symm)⟩
    op_proper := fun ha hb => MonoidOps.op_proper ha hb
    map_ne := persistently_ne
    map_op := equiv_iff.mpr persistently_and
    map_unit := equiv_iff.mpr persistently_true
  }) Φ l

theorem pure_1 {φ : Nat → A → Prop} {l : List A} :
    ([∧list] k ↦ x ∈ l, (⌜φ k x⌝ : PROP)) ⊢ ⌜∀ k x, l[k]? = some x → φ k x⌝ :=
  forall'.1.trans <| (forall_mono fun _ => forall_mono fun _ => pure_imp.1).trans <|
    (forall_mono fun _ => pure_forall.1).trans pure_forall.1

theorem pure_2 {φ : Nat → A → Prop} {l : List A} :
    (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) ⊢ [∧list] k ↦ x ∈ l, ⌜φ k x⌝ :=
  pure_forall_2.trans <| (forall_mono fun _ => pure_forall_2).trans <|
    (forall_mono fun _ => forall_mono fun _ => pure_imp_2).trans forall'.2

theorem pure {φ : Nat → A → Prop} {l : List A} :
    ([∧list] k ↦ x ∈ l, (⌜φ k x⌝ : PROP)) ⊣⊢ ⌜∀ k x, l[k]? = some x → φ k x⌝ := ⟨pure_1, pure_2⟩

theorem elem_of {Φ : A → PROP} {l : List A} {x : A} (h : x ∈ l) :
    ([∧list] y ∈ l, Φ y) ⊢ Φ x := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  exact lookup (List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩)

theorem zip_seq {Φ : A × Nat → PROP} {n : Nat} {l : List A} :
    ([∧list] xy ∈ l.zipIdx n, Φ xy) ≡ [∧list] i ↦ x ∈ l, Φ (x, n + i) :=
  bigOpL_zipIdx_equiv Φ n l

theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∧list] y ∈ (l.flatMap f), Φ y) ⊣⊢ [∧list] x ∈ l, [∧list] y ∈ (f x), Φ y := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigOpL]
    exact app.trans (and_congr .rfl ih)

theorem later {Φ : Nat → A → PROP} {l : List A} :
    (▷ [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, (▷ Φ k x) :=
  equiv_iff.mp <| bigOpL_hom (H := {
    rel_refl := .rfl
    rel_trans := .trans
    rel_proper := fun ha hb => ⟨fun h => ha.symm.trans (h.trans hb), fun h => ha.trans (h.trans hb.symm)⟩
    op_proper := fun ha hb => MonoidOps.op_proper ha hb
    map_ne := later_ne
    map_op := equiv_iff.mpr later_and
    map_unit := equiv_iff.mpr later_true
  }) Φ l

theorem laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    (▷^[n] [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, ▷^[n] Φ k x := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact (later_congr ih).trans later

theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∧list] x ∈ l₁, Φ x) ≡ [∧list] x ∈ l₂, Φ x := bigOpL_equiv_of_perm Φ hp

end BigAndL

end Iris.BI
