/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp

namespace Iris.BI

open Iris.Algebra
open BIBase

/-! # Big Conjunction over Lists -/

variable {PROP : Type _} [BI PROP] {A : Type _}

namespace BigAndL

/-- Corresponds to `big_andL_nil` in Rocq Iris. -/
@[simp]
theorem nil {Φ : Nat → A → PROP} :
    ([∧list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ iprop(True) := by
  simp only [bigAndL, bigOpL]
  exact .rfl

/-- Corresponds to `big_andL_nil'` in Rocq Iris. -/
theorem nil' {Φ : Nat → A → PROP} {l : List A} (h : l = []) :
    ([∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ iprop(True) := by
  subst h; exact nil

/-- Corresponds to `big_andL_cons` in Rocq Iris. -/
theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∧list] k ↦ y ∈ (x :: xs), Φ k y) ⊣⊢ Φ 0 x ∧ [∧list] n ↦ y ∈ xs, Φ (n + 1) y := by
  simp only [bigAndL, bigOpL]
  exact .rfl

/-- Corresponds to `big_andL_singleton` in Rocq Iris. -/
theorem singleton {Φ : Nat → A → PROP} {x : A} :
    ([∧list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x :=
  equiv_iff.mp (BigOpL.singleton Φ x)

/-- Corresponds to `big_andL_app` in Rocq Iris. -/
theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∧list] k ↦ x ∈ (l₁ ++ l₂), Φ k x) ⊣⊢
      ([∧list] k ↦ x ∈ l₁, Φ k x) ∧ [∧list] n ↦ x ∈ l₂, Φ (n + l₁.length) x :=
  equiv_iff.mp (BigOpL.append Φ l₁ l₂)

/-- Corresponds to `big_andL_snoc` in Rocq Iris. -/
theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∧list] k ↦ y ∈ (l ++ [x]), Φ k y) ⊣⊢ ([∧list] k ↦ y ∈ l, Φ k y) ∧ Φ l.length x :=
  equiv_iff.mp (BigOpL.snoc Φ l x)

/-- Corresponds to `big_andL_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ⊢ [∧list] k ↦ x ∈ l, Ψ k x := by
  induction l generalizing Φ Ψ with
  | nil => exact Entails.rfl
  | cons y ys ih =>
    simp only [bigAndL, bigOpL]
    apply and_mono
    · exact h 0 y rfl
    · apply ih
      intro k x hget
      exact h (k + 1) x hget

/-- Corresponds to `big_andL_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡ [∧list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr h

/-- Unconditional version of proper. No direct Rocq equivalent. -/
theorem congr {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ≡ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡ [∧list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr' h

/-- Corresponds to `big_andL_persistent'` in Rocq Iris. -/
instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∧list] k ↦ x ∈ l, Φ k x) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigAndL, bigOpL]
      exact persistently_true.2
    | cons x xs ih =>
      simp only [bigAndL, bigOpL]
      have h1 : Φ 0 x ⊢ <pers> Φ 0 x := Persistent.persistent
      have h2 : ([∧list] n ↦ y ∈ xs, Φ (n + 1) y) ⊢ <pers> [∧list] n ↦ y ∈ xs, Φ (n + 1) y := ih
      exact (and_mono h1 h2).trans persistently_and.2

/-- No direct Rocq equivalent; BIAffine version for affine contexts. -/
instance affine {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    Affine ([∧list] k ↦ x ∈ l, Φ k x) where
  affine := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigAndL, bigOpL]
      exact true_emp.1
    | cons x xs ih =>
      simp only [bigAndL, bigOpL]
      exact and_elim_l.trans Affine.affine

/-- Corresponds to `big_andL_emp` in Rocq Iris. -/
theorem true_l {l : List A} :
    ([∧list] _x ∈ l, iprop(True : PROP)) ≡ iprop(True) :=
  BigOpL.unit_const l

/-- Corresponds to `big_andL_and` in Rocq Iris. -/
theorem and' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, iprop(Φ k x ∧ Ψ k x)) ≡
      iprop(([∧list] k ↦ x ∈ l, Φ k x) ∧ [∧list] k ↦ x ∈ l, Ψ k x) :=
  BigOpL.op_distr Φ Ψ l

/-- No direct Rocq equivalent; reverse direction of `and'`. -/
theorem and_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    iprop(([∧list] k ↦ x ∈ l, Φ k x) ∧ [∧list] k ↦ x ∈ l, Ψ k x) ≡
      [∧list] k ↦ x ∈ l, iprop(Φ k x ∧ Ψ k x) :=
  and'.symm

/-- Corresponds to `big_andL_take_drop` in Rocq Iris. -/
theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡
      iprop(([∧list] k ↦ x ∈ (l.take n), Φ k x) ∧ [∧list] k ↦ x ∈ (l.drop n), Φ (n + k) x) :=
  BigOpL.take_drop Φ l n

/-- Corresponds to `big_andL_fmap` in Rocq Iris. -/
theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∧list] k ↦ y ∈ (l.map f), Φ k y) ≡ [∧list] k ↦ x ∈ l, Φ k (f x) := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigAndL, bigOpL]
    exact Monoid.op_proper OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_andL_lookup` in Rocq Iris. -/
theorem lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∧list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x := by
  induction l generalizing i Φ with
  | nil => simp at h
  | cons y ys ih =>
    simp only [bigAndL, bigOpL]
    cases i with
    | zero =>
      simp at h
      subst h
      exact and_elim_l
    | succ j =>
      simp at h
      exact and_elim_r.trans (ih h)

/-- Corresponds to `big_andL_intro` in Rocq Iris. -/
theorem intro {P : PROP} {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ [∧list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigAndL, bigOpL]
    exact true_intro
  | cons y ys ih =>
    simp only [bigAndL, bigOpL]
    apply and_intro
    · exact h 0 y rfl
    · exact ih (fun k x hget => h (k + 1) x hget)

/-- Corresponds to `big_andL_forall` in Rocq Iris. -/
theorem forall' {Φ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) := by
  constructor
  · apply forall_intro; intro k
    apply forall_intro; intro x
    refine imp_intro <| and_comm.1.trans <| pure_elim_l (lookup ·)
  · induction l generalizing Φ with
    | nil => exact true_intro
    | cons y ys ih =>
      simp only [bigAndL, bigOpL]
      apply and_intro
      · exact (forall_elim 0).trans <| (forall_elim y).trans <|
          (imp_congr_l (pure_true rfl)).1.trans true_imp.1
      · refine Entails.trans ?_ (ih (Φ := fun k x => Φ (k + 1) x))
        exact forall_intro fun k => forall_intro fun x => (forall_elim (k + 1)).trans (forall_elim x)

/-- Corresponds to `big_andL_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, Φ k x) ∧ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x)) ⊢
      [∧list] k ↦ x ∈ l, Ψ k x :=
  intro fun k x hget =>
    (and_mono (lookup hget) ((forall_elim k).trans (forall_elim x))).trans <|
      (and_mono .rfl ((and_intro (pure_intro hget) .rfl).trans imp_elim_r)).trans imp_elim_r

/-- Corresponds to `big_andL_persistently` in Rocq Iris. -/
theorem persistently {Φ : Nat → A → PROP} {l : List A} :
    iprop(<pers> [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, iprop(<pers> Φ k x) :=
  equiv_iff.mp <| BigOpL.commute bi_persistently_and_homomorphism Φ l

/-- Corresponds to `big_andL_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : Nat → A → Prop} {l : List A} :
    ([∧list] k ↦ x ∈ l, iprop(⌜φ k x⌝ : PROP)) ⊢ iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  forall'.1.trans <| (forall_mono fun _ => forall_mono fun _ => pure_imp.1).trans <|
    (forall_mono fun _ => pure_forall.1).trans pure_forall.1

/-- Corresponds to `big_andL_pure_2` in Rocq Iris. -/
theorem pure_2 {φ : Nat → A → Prop} {l : List A} :
    iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) ⊢ [∧list] k ↦ x ∈ l, iprop(⌜φ k x⌝ : PROP) :=
  pure_forall_2.trans <| (forall_mono fun _ => pure_forall_2).trans <|
    (forall_mono fun _ => forall_mono fun _ => pure_imp_2).trans forall'.2

/-- Corresponds to `big_andL_pure` in Rocq Iris. -/
theorem pure {φ : Nat → A → Prop} {l : List A} :
    ([∧list] k ↦ x ∈ l, iprop(⌜φ k x⌝ : PROP)) ⊣⊢ iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  ⟨pure_1, pure_2⟩

/-- Corresponds to `big_andL_elem_of` in Rocq Iris. -/
theorem elem_of {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    ([∧list] y ∈ l, Φ y) ⊢ Φ x := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  exact lookup hlookup

/-- Corresponds to `big_andL_zip_seq` in Rocq Iris. -/
theorem zip_seq {Φ : Nat × A → PROP} {n : Nat} {l : List A} :
    ([∧list] ky ∈ ((List.range' n l.length).zip l), Φ ky) ≡
      [∧list] i ↦ x ∈ l, Φ (n + i, x) :=
  BigOpL.zip_seq (op := and) (unit := iprop(True)) Φ n l

/-- Corresponds to `big_andL_bind` in Rocq Iris (uses flatMap). -/
theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∧list] y ∈ (l.flatMap f), Φ y) ⊣⊢
      [∧list] x ∈ l, [∧list] y ∈ (f x), Φ y := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigAndL, bigOpL]
    exact app.trans (and_congr .rfl ih)

/-- Corresponds to `big_andL_later` in Rocq Iris. -/
theorem later {Φ : Nat → A → PROP} {l : List A} :
    iprop(▷ [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, iprop(▷ Φ k x) :=
  equiv_iff.mp <| BigOpL.commute bi_later_and_homomorphism Φ l

/-- Corresponds to `big_andL_laterN` in Rocq Iris. -/
theorem laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    iprop(▷^[n] [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, iprop(▷^[n] Φ k x) := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact (later_congr ih).trans later

/-- Corresponds to `big_andL_Permutation` in Rocq Iris (via BigOpL.perm). -/
theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∧list] x ∈ l₁, Φ x) ≡ [∧list] x ∈ l₂, Φ x :=
  BigOpL.perm Φ hp

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not ported:
- `big_andL_submseteq`: Uses stdpp's `⊆+` relation
- `big_andL_ne`: OFE-level non-expansiveness (handled at algebra layer)
- `big_andL_mono'`, `big_andL_id_mono'`: Convenience wrappers (use `mono` directly)
- `big_andL_absorbing`, `big_andL_absorbing'`: Absorbing typeclass (not implemented)
- `big_andL_timeless`, `big_andL_timeless'`: Requires `and_timeless` infrastructure
-/

end BigAndL

end Iris.BI
