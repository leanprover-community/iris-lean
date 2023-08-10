/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Classes
import Iris.BI.Extensions
import Iris.BI.BI
import Iris.Std.Classes
import Iris.Std.Rewrite
import Iris.Std.TC

namespace Iris.BI
open Iris.Std
open BI

-- Entails
instance entails_anti_symm [BI PROP] : AntiSymm (α := PROP) (· ⊣⊢ ·) (· ⊢ ·) where
  anti_symm := by
    intro _ _ H1 H2
    rw' [equiv_entails]
    exact And.intro H1 H2

-- Logic
theorem and_elim_l' [BI PROP] {P Q R : PROP} : (P ⊢ R) → P ∧ Q ⊢ R := by
  intro H
  rw' [and_elim_l, H]

theorem and_elim_r' [BI PROP] {P Q R : PROP} : (Q ⊢ R) → P ∧ Q ⊢ R := by
  intro H
  rw' [and_elim_r, H]

theorem or_intro_l' [BI PROP] {P Q R : PROP} : (P ⊢ Q) → P ⊢ Q ∨ R := by
  intro H
  rw' [H, ← or_intro_l]

theorem or_intro_r' [BI PROP] {P Q R : PROP} : (P ⊢ R) → P ⊢ Q ∨ R := by
  intro H
  rw' [H, ← or_intro_r]

theorem imp_intro_l [BI PROP] {P Q R : PROP} : (Q ∧ P ⊢ R) → P ⊢ Q → R := by
  intro H
  apply imp_intro
  rw' [← H]
  apply and_intro
  · exact and_elim_r
  · exact and_elim_l

theorem mp [BI PROP] {P Q R : PROP} : (P ⊢ Q → R) → (P ⊢ Q) → P ⊢ R := by
  intro H1 H2
  rw' [← imp_elim H1]
  apply and_intro
  · simp
  · exact H2

theorem imp_elim_r' [BI PROP] {P Q R : PROP} : (Q ⊢ P → R) → P ∧ Q ⊢ R := by
  intros H
  apply mp (Q := P)
  · rw' [and_elim_r, H]
  · rw' [and_elim_l]

theorem imp_elim_l [BI PROP] {P Q : PROP} : (P → Q) ∧ P ⊢ Q := by
  apply imp_elim
  simp

theorem imp_elim_r [BI PROP] {P Q : PROP} : P ∧ (P → Q) ⊢ Q := by
  apply imp_elim_r'
  simp

theorem False_elim [BI PROP] {P : PROP} : False ⊢ P := by
  apply pure_elim'
  simp

theorem True_intro [BI PROP] {P : PROP} : P ⊢ True := by
  apply pure_intro
  simp

@[rw_mono_rule]
theorem and_mono [BI PROP] {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∧ P' ⊢ Q ∧ Q' := by
  intro H1 H2
  apply and_intro
  · rw' [← H1, and_elim_l]
  · rw' [← H2, and_elim_r]

@[rw_mono_rule]
theorem or_mono [BI PROP] {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∨ P' ⊢ Q ∨ Q' := by
  intro H1 H2
  apply or_elim
  · apply or_intro_l'
    exact H1
  · apply or_intro_r'
    exact H2

@[rw_mono_rule]
theorem imp_mono [BI PROP] {P P' Q Q' : PROP} : (Q ⊢ P) → (P' ⊢ Q') → (P → P') ⊢ Q → Q' := by
  intro HP HQ
  apply imp_intro
  rw' [HP, ← HQ]
  apply imp_elim
  simp

@[rw_mono_rule]
theorem forall_mono [BI PROP] {Φ Ψ : α → PROP} :
  (∀ a, Φ a ⊢ Ψ a) → (∀ a, Φ a) ⊢ ∀ a, Ψ a
:= by
  intro Hφ
  apply forall_intro
  intro a
  rw' [← Hφ a, ← forall_elim _]

@[rw_mono_rule]
theorem exists_mono [BI PROP] {Φ Ψ : α → PROP} :
  (∀ a, Φ a ⊢ Ψ a) → (∃ a, Φ a) ⊢ ∃ a, Ψ a
:= by
  intro Hφ
  apply exists_elim
  intro a
  rw' [Hφ a, exists_intro _]

instance and_idem [BI PROP] : Idemp (α := PROP) (· ⊣⊢ ·) (iprop(· ∧ ·)) where
  idem := by
    intro _
    apply anti_symm
    · exact and_elim_l
    · apply and_intro
      <;> simp

instance or_idem [BI PROP] : Idemp (α := PROP) (· ⊣⊢ ·) (iprop(· ∨ ·)) where
  idem := by
    intro _
    apply anti_symm
    · apply or_elim
      <;> simp
    · exact or_intro_l

instance and_comm [BI PROP] : Comm (α := PROP) (· ⊣⊢ ·) (iprop(· ∧ ·)) where
  comm := by
    intros
    apply anti_symm
    case left =>
      apply and_intro
      · exact and_elim_r
      · exact and_elim_l
    case right =>
      apply and_intro
      · exact and_elim_r
      · exact and_elim_l

instance True_and [BI PROP] : LeftId (α := PROP) (· ⊣⊢ ·) iprop(True) (iprop(· ∧ ·)) where
  left_id := by
    intros
    apply anti_symm
    case left =>
      exact and_elim_r
    case right =>
      apply and_intro ?_ reflexivity
      apply pure_intro
      simp

instance and_True [BI PROP] : RightId (α := PROP) (· ⊣⊢ ·) iprop(True) (iprop(· ∧ ·)) where
  right_id := by
    intros
    apply anti_symm
    case left =>
      exact and_elim_l
    case right =>
      apply and_intro reflexivity ?_
      apply pure_intro
      simp

instance and_assoc [BI PROP] : Assoc (α := PROP) (· ⊣⊢ ·) (iprop(· ∧ ·)) where
  assoc := by
    intro _ _ _
    apply anti_symm
    <;> apply and_intro
    <;> try apply and_intro
    all_goals
      simp [and_elim_l, and_elim_r]
      try { apply and_elim_l' ; simp [and_elim_l, and_elim_r] }
      try { apply and_elim_r' ; simp [and_elim_l, and_elim_r] }

theorem and_or_l [BI PROP] {P Q R : PROP} : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R := by
  apply anti_symm
  case left =>
    apply imp_elim_r'
    apply or_elim
    <;> apply imp_intro_l
    · exact or_intro_l
    · exact or_intro_r
  case right =>
    apply and_intro
    · apply or_elim
      <;> apply and_elim_l'
      <;> simp
    · apply or_elim
      <;> apply and_elim_r'
      · exact or_intro_l
      · exact or_intro_r

theorem and_exists_l [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a := by
  apply anti_symm
  case left =>
    apply imp_elim_r'
    apply exists_elim
    intro a
    apply imp_intro_l
    rw' [← exists_intro a]
  case right =>
    apply exists_elim
    intro a
    apply and_intro
    · rw' [and_elim_l]
    · rw' [← exists_intro a, and_elim_r]

theorem or_alt [BI PROP] {P Q : PROP} : P ∨ Q ⊣⊢ ∃ (b : Bool), if b then P else Q := by
  apply anti_symm
  case left =>
    apply or_elim
    · rw' [← exists_intro true]
    · rw' [← exists_intro false]
  case right =>
    apply exists_elim
    intro b
    cases b
    · rw' [← or_intro_r]
    · rw' [← or_intro_l]

-- BI
@[rw_mono_rule]
theorem wand_mono [BI PROP] {P P' Q Q' : PROP} : (Q ⊢ P) → (P' ⊢ Q') → (P -∗ P') ⊢ Q -∗ Q' := by
  intro HP HQ
  apply wand_intro
  rw' [HP, ← HQ]
  apply wand_elim
  simp

instance sep_comm [BI PROP] : Comm (α := PROP) (· ⊣⊢ ·) (iprop(· ∗ ·)) where
  comm := by
    intros
    apply anti_symm
    <;> exact sep_symm

instance sep_assoc [BI PROP] : Assoc (α := PROP) (· ⊣⊢ ·) (iprop(· ∗ ·)) where
  assoc := by
    intros P Q R
    apply anti_symm
    case left =>
      rw' [
        (comm : P ∗ (Q ∗ R) ⊣⊢ _),
        (comm : P ∗ Q ⊣⊢ _),
        (comm : Q ∗ R ⊣⊢ _),
        (comm : (Q ∗ P) ∗ R ⊣⊢ _),
        sep_assoc_l]
    case right =>
      exact sep_assoc_l

instance emp_sep [BI PROP] : LeftId (α := PROP) (· ⊣⊢ ·) iprop(emp) (iprop(· ∗ ·)) where
  left_id := by
    intros
    apply anti_symm
    · exact emp_sep_1
    · exact emp_sep_2

instance sep_emp [BI PROP] : RightId (α := PROP) (· ⊣⊢ ·) iprop(emp) (iprop(· ∗ ·)) where
  right_id := by
    intro x
    rw' [(comm : iprop(x ∗ emp) ⊣⊢ _), (left_id : emp ∗ x ⊣⊢ _)]

theorem True_sep_2 [BI PROP] {P : PROP} : P ⊢ True ∗ P := by
  rw' [emp_sep_2]
  apply sep_mono ?_ reflexivity
  apply pure_intro
  simp

theorem wand_intro_l [BI PROP] {P Q R : PROP} : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R := by
  rw' [(comm : Q ∗ P ⊣⊢ _)]
  exact wand_intro

theorem wand_elim_l [BI PROP] {P Q : PROP} : (P -∗ Q) ∗ P ⊢ Q := by
  apply wand_elim
  simp

theorem wand_elim_r [BI PROP] {P Q : PROP} : P ∗ (P -∗ Q) ⊢ Q := by
  rw' [sep_symm, wand_elim_l]

theorem wand_elim_r' [BI PROP] {P Q R : PROP} : (Q ⊢ P -∗ R) → P ∗ Q ⊢ R := by
  intro H
  rw' [H, wand_elim_r]

theorem sep_or_l [BI PROP] {P Q R : PROP} : P ∗ (Q ∨ R) ⊣⊢ (P ∗ Q) ∨ (P ∗ R) := by
  apply anti_symm
  case left =>
    apply wand_elim_r'
    apply or_elim
    <;> apply wand_intro_l
    · exact or_intro_l
    · exact or_intro_r
  case right =>
    apply or_elim
    · rw' [← or_intro_l]
    · rw' [← or_intro_r]

theorem sep_or_r [BI PROP] {P Q R : PROP} : (P ∨ Q) ∗ R ⊣⊢ (P ∗ R) ∨ (Q ∗ R) := by
  rw' [!(comm : _ ∗ R ⊣⊢ _), sep_or_l]

theorem sep_exists_l [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a := by
  apply anti_symm
  case left =>
    apply wand_elim_r'
    apply exists_elim
    intro a
    apply wand_intro_l
    rw' [← exists_intro a]
  case right =>
    apply exists_elim
    intro a
    rw' [(exists_intro _ : Ψ a ⊢ _)]

theorem sep_exists_r [BI PROP] {Φ : α → PROP} {Q : PROP} : (∃ a, Φ a) ∗ Q ⊣⊢ ∃ a, Φ a ∗ Q := by
  apply anti_symm
  all_goals
    rw' [(comm : _ ∗ Q ⊣⊢ _), sep_exists_l]
    apply exists_mono
    intro _
    rw' [(comm : Q ∗ _ ⊣⊢ _)]

theorem wand_iff_refl [BI PROP] {P : PROP} : ⊢ P ∗-∗ P := by
  apply and_intro
  <;> apply wand_intro_l
  <;> rw' [(right_id : P ∗ emp ⊣⊢ _)]

theorem wand_entails [BI PROP] {P Q : PROP} : (⊢ P -∗ Q) → P ⊢ Q := by
  intro H
  rw' [← (left_id : emp ∗ P ⊣⊢ _), H]
  exact wand_elim_l

theorem entails_wand [BI PROP] {P Q : PROP} : (P ⊢ Q) → ⊢ P -∗ Q := by
  intro H
  rw' [← H]
  apply wand_intro
  rw' [(left_id : emp ∗ Q ⊣⊢ _)]

theorem equiv_wand_iff [BI PROP] {P Q : PROP} : (P ⊣⊢ Q) → ⊢ P ∗-∗ Q := by
  intro H
  rw' [H]
  exact wand_iff_refl

theorem wand_iff_equiv [BI PROP] {P Q : PROP} : (⊢ P ∗-∗ Q) → (P ⊣⊢ Q) := by
  intro HPQ
  apply anti_symm
  <;> apply wand_entails
  <;> rw' [HPQ]
  <;> simp [wandIff, and_elim_l, and_elim_r]

-- Pure
theorem pure_elim (φ : Prop) [BI PROP] {Q R : PROP} : (Q ⊢ ⌜φ⌝) → (φ → Q ⊢ R) → Q ⊢ R := by
  intro HQ HQR
  rw' [← (idem : Q ∧ Q ⊣⊢ _), HQ]
  apply imp_elim
  apply pure_elim'
  intro Hφ
  apply imp_intro_l
  rw' [and_elim_l]
  exact HQR Hφ

theorem pure_mono {φ1 φ2 : Prop} [BI PROP] : (φ1 → φ2) → ⌜φ1⌝ ⊢ (⌜φ2⌝ : PROP) := by
  intro H12
  apply pure_elim'
  intro H1
  apply pure_intro
  exact H12 H1

theorem pure_elim_l {φ : Prop} [BI PROP] {Q R : PROP} : (φ → Q ⊢ R) → ⌜φ⌝ ∧ Q ⊢ R := by
  intro H
  apply pure_elim φ
  · exact and_elim_l
  · intro Hφ
    rw' [H Hφ]
    exact and_elim_r

theorem pure_True {φ : Prop} [BI PROP] : φ → ⌜φ⌝ ⊣⊢ (True : PROP) := by
  intro Hφ
  apply anti_symm
  case left =>
    apply pure_intro
    exact True.intro
  case right =>
    apply pure_intro
    exact Hφ

theorem pure_and {φ1 φ2 : Prop} [BI PROP] : ⌜φ1 ∧ φ2⌝ ⊣⊢ ⌜φ1⌝ ∧ (⌜φ2⌝ : PROP) := by
  apply anti_symm
  case left =>
    apply and_intro
    <;> apply pure_mono
    <;> simp_all
  case right =>
    apply pure_elim φ1
    · exact and_elim_l
    intro _
    rw' [and_elim_r]
    apply pure_mono
    simp_all

theorem pure_or {φ1 φ2 : Prop} [BI PROP] : ⌜φ1 ∨ φ2⌝ ⊣⊢ ⌜φ1⌝ ∨ (⌜φ2⌝ : PROP) := by
  apply anti_symm
  case left =>
    apply pure_elim (φ1 ∨ φ2)
    · simp
    intro H
    cases H
    · apply or_intro_l'
      apply pure_mono
      simp_all
    · apply or_intro_r'
      apply pure_mono
      simp_all
  case right =>
    apply or_elim
    <;> apply pure_mono
    <;> simp_all

theorem pure_imp_1 {φ1 φ2 : Prop} [BI PROP] : ⌜φ1 → φ2⌝ ⊢ (⌜φ1⌝ → ⌜φ2⌝ : PROP) := by
  apply imp_intro_l
  rw' [← pure_and]
  apply pure_mono
  simp_all

theorem pure_forall_1 {φ : α → Prop} [BI PROP] : ⌜∀ x, φ x⌝ ⊢ ∀ x, (⌜φ x⌝ : PROP) := by
  apply forall_intro
  intro x
  apply pure_mono
  simp_all

theorem pure_exists [inst : BI PROP] {φ : α → Prop} : ⌜∃ x, φ x⌝ ⊣⊢ (∃ x, ⌜φ x⌝ : PROP) := by
  apply anti_symm
  case left =>
    apply pure_elim'
    intro ⟨x, H⟩
    rw' [← exists_intro x]
    apply pure_mono
    intro _
    exact H
  case right =>
    apply exists_elim
    intro a
    apply pure_mono
    intro H
    exact ⟨a, H⟩

-- Affine
theorem affinely_elim_emp [BI PROP] {P : PROP} : <affine> P ⊢ emp := by
  simp [affinely, and_elim_l]

theorem affinely_elim [BI PROP] {P : PROP} : <affine> P ⊢ P := by
  simp [affinely, and_elim_r]

@[rw_mono_rule]
theorem affinely_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <affine> P ⊢ <affine> Q := by
  intro H
  simp only [affinely]
  rw' [H]

theorem affinely_idem [BI PROP] {P : PROP} : <affine> <affine> P ⊣⊢ <affine> P := by
  simp only [affinely]
  rw' [
    (assoc : emp ∧ emp ∧ _ ⊣⊢ _),
    (idem : emp ∧ emp ⊣⊢ _)]

theorem affinely_emp [BI PROP] : <affine> emp ⊣⊢ (emp : PROP) := by
  simp only [affinely]
  exact idem

theorem affinely_or [BI PROP] {P Q : PROP} : <affine> (P ∨ Q) ⊣⊢ <affine> P ∨ <affine> Q := by
  exact and_or_l

theorem affinely_and [BI PROP] {P Q : PROP} : <affine> (P ∧ Q) ⊣⊢ <affine> P ∧ <affine> Q := by
  rw' [
    !affinely,
    (comm : emp ∧ P ⊣⊢ _),
    (assoc : (P ∧ emp) ∧ _ ⊣⊢ _),
    ← (assoc : _ ⊣⊢ (P ∧ emp) ∧ _),
    ← (assoc : _ ⊣⊢ (P ∧ emp ∧ emp) ∧ _),
    (idem : emp ∧ emp ⊣⊢ _),
    (assoc : P ∧ emp ∧ _ ⊣⊢ _),
    (assoc : emp ∧ P ∧ _ ⊣⊢ _),
    (comm : emp ∧ P ⊣⊢ _)]

theorem affinely_sep_2 [BI PROP] {P Q : PROP} : <affine> P ∗ <affine> Q ⊢ <affine> (P ∗ Q) := by
  simp only [affinely]
  apply and_intro
  · rw' [!and_elim_l, (right_id : emp ∗ emp ⊣⊢ _)]
  · rw' [!and_elim_r]

theorem affinely_forall [BI PROP] {Φ : α → PROP} : <affine> (∀ a, Φ a) ⊢ ∀ a, <affine> (Φ a) := by
  apply forall_intro
  intro a
  rw' [forall_elim a]

theorem affinely_exists [BI PROP] {Φ : α → PROP} : <affine> (∃ a, Φ a) ⊣⊢ ∃ a, <affine> (Φ a) := by
  exact and_exists_l

theorem affinely_True_emp [BI PROP] : <affine> True ⊣⊢ <affine> (emp : PROP) := by
  apply anti_symm
  <;> simp only [affinely]
  · apply and_intro
    <;> exact and_elim_l
  · rw' [(right_id : _ ∧ True ⊣⊢ _)]
    exact and_elim_l

theorem affinely_and_l [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ <affine> (P ∧ Q) := by
  simp only [affinely]
  rw' [(assoc : emp ∧ P ∧ _ ⊣⊢ _)]

theorem affinely_and_r [BI PROP] {P Q : PROP} : P ∧ <affine> Q ⊣⊢ <affine> (P ∧ Q) := by
  simp only [affinely]
  rw' [
    (assoc : P ∧ emp ∧ _ ⊣⊢ _),
    (assoc : emp ∧ P ∧ _ ⊣⊢ _),
    (comm : P ∧ emp ⊣⊢ _)]

theorem affinely_and_lr [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ P ∧ <affine> Q := by
  rw' [affinely_and_l, affinely_and_r]

-- Absorbing
theorem absorbingly_intro [BI PROP] {P : PROP} : P ⊢ <absorb> P := by
  exact True_sep_2

@[rw_mono_rule]
theorem absorbingly_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <absorb> P ⊢ <absorb> Q := by
  intro H
  simp only [absorbingly]
  rw' [H]

theorem absorbingly_idem [BI PROP] {P : PROP} : <absorb> <absorb> P ⊣⊢ <absorb> P := by
  apply anti_symm
  case left =>
    simp only [absorbingly]
    rw' [(assoc : True ∗ True ∗ P ⊣⊢ _)]
    apply sep_mono ?_ reflexivity
    apply pure_intro
    simp
  case right =>
    rw' [← absorbingly_intro]

theorem absorbingly_pure {φ : Prop} [BI PROP] : <absorb> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  apply anti_symm
  case left =>
    apply wand_elim_r'
    apply pure_elim'
    intro Hφ
    apply wand_intro_l
    apply pure_intro
    exact Hφ
  case right =>
    exact absorbingly_intro

theorem absorbingly_or [BI PROP] {P Q : PROP} : <absorb> (P ∨ Q) ⊣⊢ <absorb> P ∨ <absorb> Q := by
  simp [absorbingly, sep_or_l]

theorem absorbingly_and_1 [BI PROP] {P Q : PROP} : <absorb> (P ∧ Q) ⊢ <absorb> P ∧ <absorb> Q := by
  apply and_intro
  · rw' [and_elim_l]
  · rw' [and_elim_r]

theorem absorbingly_forall [BI PROP] (Φ : α → PROP) : <absorb> (∀ a, Φ a) ⊢ ∀ a, <absorb> (Φ a) := by
  apply forall_intro
  intro a
  rw' [forall_elim a]

theorem absorbingly_exists [BI PROP] (Φ : α → PROP) : <absorb> (∃ a, Φ a) ⊣⊢ ∃ a, <absorb> (Φ a) := by
  simp [absorbingly, sep_exists_l]

theorem absorbingly_sep [BI PROP] {P Q : PROP} : <absorb> (P ∗ Q) ⊣⊢ <absorb> P ∗ <absorb> Q := by
  rw' [← absorbingly_idem]
  simp only [absorbingly]
  rw' [
    (assoc : True ∗ P ∗ Q ⊣⊢ _),
    (assoc : True ∗ (True ∗ P) ∗ Q ⊣⊢ _),
    (comm : True ∗ True ∗ P ⊣⊢ _),
    ← (assoc : _ ⊣⊢ ((True ∗ P) ∗ True) ∗ Q)]

theorem absorbingly_True_emp [BI PROP] : <absorb> True ⊣⊢ <absorb> (emp : PROP) := by
  rw' [absorbingly_pure]
  simp only [absorbingly]
  rw' [(right_id : True ∗ emp ⊣⊢ _)]

theorem absorbingly_wand [BI PROP] {P Q : PROP} : <absorb> (P -∗ Q) ⊢ <absorb> P -∗ <absorb> Q := by
  apply wand_intro_l
  rw' [← absorbingly_sep, wand_elim_r]

theorem absorbingly_sep_l [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ <absorb> (P ∗ Q) := by
  simp only [absorbingly]
  rw' [(assoc : True ∗ P ∗ Q ⊣⊢ _)]

theorem absorbingly_sep_r [BI PROP] {P Q : PROP} : P ∗ <absorb> Q ⊣⊢ <absorb> (P ∗ Q) := by
  simp only [absorbingly]
  rw' [!(assoc : _ ⊣⊢ _ ∗ Q), (comm : P ∗ True ⊣⊢ _)]

theorem absorbingly_sep_lr [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ P ∗ <absorb> Q := by
  rw' [absorbingly_sep_l, absorbingly_sep_r]

-- Affine / Absorbing Propositions
theorem affine_affinely [BI PROP] (P : PROP) [Affine P] : <affine> P ⊣⊢ P := by
  apply anti_symm
  <;> simp only [affinely]
  · exact and_elim_r
  · apply and_intro
    · exact affine
    · simp

theorem absorbing_absorbingly [BI PROP] {P : PROP} [Absorbing P] : <absorb> P ⊣⊢ P := by
  apply anti_symm
  · exact absorbing
  · rw' [absorbingly_intro]

theorem sep_elim_l [BI PROP] {P Q : PROP} [instQP : TCOr (Affine Q) (Absorbing P)] : P ∗ Q ⊢ P := by
  cases instQP
  case l =>
    rw' [affine, (right_id : P ∗ emp ⊣⊢ _)]
  case r =>
    rw' [
      (pure_intro True.intro : Q ⊢ _),
      (comm : P ∗ True ⊣⊢ _),
      absorbing]

theorem sep_elim_r [BI PROP] {P Q : PROP} [TCOr (Affine P) (Absorbing Q)] : P ∗ Q ⊢ Q := by
  rw' [(comm : P ∗ Q ⊣⊢ _), sep_elim_l]

theorem sep_and [BI PROP] {P Q : PROP} [inst1 : TCOr (Affine P) (Absorbing Q)] [inst2 : TCOr (Absorbing P) (Affine Q)] :
  P ∗ Q ⊢ P ∧ Q
:= by
  cases inst1
  <;> cases inst2
  <;> apply and_intro
  <;> first | exact sep_elim_l | exact sep_elim_r

-- Persistent
theorem absorbingly_elim_persistently [BI PROP] {P : PROP} : <absorb> <pers> P ⊣⊢ <pers> P := by
  apply anti_symm
  case left =>
    simp only [absorbingly]
    rw' [
      (comm : iprop(True ∗ <pers> P) ⊣⊢ _),
      persistently_absorb_l]
  case right =>
    exact absorbingly_intro

theorem persistently_forall_1 [BI PROP] {Ψ : α → PROP} : <pers> (∀ a, Ψ a) ⊢ ∀ a, <pers> (Ψ a) := by
  apply forall_intro
  intro x
  rw' [forall_elim x]

theorem persistently_exists [BI PROP] {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊣⊢ ∃ a, <pers> (Ψ a) := by
  apply anti_symm
  case left =>
    exact persistently_exists_1
  case right =>
    apply exists_elim
    intro a
    rw' [exists_intro a]

theorem persistently_and [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊣⊢ <pers> P ∧ <pers> Q := by
  apply anti_symm
  case left =>
    apply and_intro
    · rw' [and_elim_l]
    · rw' [and_elim_r]
  case right =>
    exact persistently_and_2

theorem persistently_ite {p : Bool} [BI PROP] {P Q : PROP} :
  (<pers> if p then P else Q) ⊣⊢ if p then <pers> P else <pers> Q
:= by
  cases p
  <;> simp

theorem persistently_or [BI PROP] {P Q : PROP} : <pers> (P ∨ Q) ⊣⊢ <pers> P ∨ <pers> Q := by
  rw' [!or_alt, persistently_exists]
  apply anti_symm
  <;> apply exists_elim
  <;> intro a
  <;> rw' [← exists_intro a, persistently_ite]

theorem persistently_emp_intro [BI PROP] {P : PROP} : P ⊢ <pers> emp := by
  rw' [← persistently_absorb_l (Q := P)]
  conv =>
    lhs
    rw [← (left_id : emp ∗ P ⊣⊢ _)]
  rw' [persistently_emp_2]

theorem persistently_True_emp [BI PROP] : <pers> True ⊣⊢ <pers> (emp : PROP) := by
  apply anti_symm
  case left =>
    exact persistently_emp_intro
  case right =>
    apply persistently_mono
    apply pure_intro
    simp

theorem persistently_True [BI PROP] : True ⊢ <pers> (True : PROP) := by
  rw' [persistently_True_emp, persistently_emp_intro]

theorem persistently_and_emp [BI PROP] {P : PROP} : <pers> P ⊣⊢ <pers> (emp ∧ P) := by
  apply anti_symm
  case left =>
    rw' [persistently_and]
    apply and_intro ?_ reflexivity
    exact persistently_emp_intro
  case right =>
    rw' [and_elim_r]

theorem persistently_and_sep_elim_emp [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ (emp ∧ P) ∗ Q := by
  rw' [persistently_and_emp, persistently_and_l]

theorem persistently_and_sep_assoc [BI PROP] {P Q R : PROP} : <pers> P ∧ (Q ∗ R) ⊣⊢ (<pers> P ∧ Q) ∗ R := by
  apply anti_symm
  case left =>
    rw' [
      persistently_idem_2,
      persistently_and_sep_elim_emp,
      (assoc : (emp ∧ <pers> P) ∗ Q ∗ R ⊣⊢ _)]
    apply sep_mono ?_ reflexivity
    apply and_intro
    · rw' [and_elim_r, persistently_absorb_l]
    · rw' [and_elim_l, (left_id : emp ∗ Q ⊣⊢ _)]
  case right =>
    apply and_intro
    · rw' [and_elim_l, persistently_absorb_l]
    · rw' [and_elim_r]

theorem persistently_and_emp_elim [BI PROP] {P : PROP} : emp ∧ <pers> P ⊢ P := by
  rw' [
    (comm : emp ∧ <pers> P ⊣⊢ _),
    persistently_and_sep_elim_emp,
    (right_id : (emp ∧ P) ∗ emp ⊣⊢ _),
    and_elim_r]

theorem persistently_into_absorbingly [BI PROP] {P : PROP} : <pers> P ⊢ <absorb> P := by
  rw' [
    ← (right_id : <pers> P ∧ True ⊣⊢ _),
    ← (left_id : emp ∗ True ⊣⊢ _),
    persistently_and_sep_assoc,
    (comm : iprop(<pers> P ∧ emp) ⊣⊢ _),
    persistently_and_emp_elim,
    (comm : iprop(P ∗ True) ⊣⊢ _)]

theorem persistently_elim [BI PROP] {P : PROP} [Absorbing P] : <pers> P ⊢ P := by
  rw' [persistently_into_absorbingly, absorbing]

theorem persistently_idem [BI PROP] {P : PROP} : <pers> <pers> P ⊣⊢ <pers> P := by
  apply anti_symm
  · rw' [persistently_into_absorbingly, absorbingly_elim_persistently]
  · exact persistently_idem_2

theorem persistently_pure {φ : Prop} [BI PROP] : <pers> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  apply anti_symm
  case left =>
    rw' [persistently_into_absorbingly, absorbingly_pure]
  case right =>
    apply pure_elim'
    intro Hφ
    rw' [persistently_True]
    apply persistently_mono
    apply pure_intro
    exact Hφ

theorem persistently_and_sep_l_1 [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ <pers> P ∗ Q := by
  conv =>
    lhs
    rw [← (left_id : iprop(emp ∗ Q) ⊣⊢ _)]
  rw' [persistently_and_sep_assoc, and_elim_l]

theorem persistently_and_sep [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊢ <pers> (P ∗ Q) := by
  rw' [persistently_and, ← persistently_idem, ← persistently_and]
  conv =>
    lhs
    rw [← (left_id : emp ∗ Q ⊣⊢ _)]
  rw' [
    persistently_and_sep_assoc,
    (comm : <pers> P ∧ emp ⊣⊢ _),
    persistently_and_emp_elim]

theorem persistently_affinely_elim [BI PROP] {P : PROP} : <pers> <affine> P ⊣⊢ <pers> P := by
  simp only [affinely]
  rw' [
    persistently_and,
    ← persistently_True_emp,
    persistently_pure,
    (left_id : True ∧ <pers> P ⊣⊢ _)]

theorem and_sep_persistently [BI PROP] {P Q : PROP} : <pers> P ∧ <pers> Q ⊣⊢ <pers> P ∗ <pers> Q := by
  apply anti_symm
  case left =>
    exact persistently_and_sep_l_1
  case right =>
    apply and_intro
    · exact persistently_absorb_l
    · rw' [(comm : iprop(<pers> P ∗ <pers> Q ⊣⊢ _)), persistently_absorb_l]

theorem persistently_sep_2 [BI PROP] {P Q : PROP} : <pers> P ∗ <pers> Q ⊢ <pers> (P ∗ Q) := by
  rw' [← persistently_and_sep, persistently_and, ← and_sep_persistently]

-- Intuitionistic
theorem intuitionistically_elim [BI PROP] {P : PROP} : □ P ⊢ P := by
  exact persistently_and_emp_elim

theorem intuitionistically_emp [BI PROP] : □ emp ⊣⊢ (emp : PROP) := by
  simp only [intuitionistically]
  rw' [
    ← persistently_True_emp,
    persistently_pure,
    affinely_True_emp,
    affinely_emp]

theorem intuitionistically_True_emp [BI PROP] : □ True ⊣⊢ (emp : PROP) := by
  rw' [← intuitionistically_emp]
  simp only [intuitionistically]
  rw' [persistently_True_emp]

theorem intuitionistically_and [BI PROP] {P Q : PROP} : □ (P ∧ Q) ⊣⊢ □ P ∧ □ Q := by
  simp only [intuitionistically]
  rw' [persistently_and, affinely_and]

theorem intuitionistically_forall [BI PROP] {Φ : α → PROP} : □ (∀ x, Φ x) ⊢ ∀ x, □ Φ x := by
  simp only [intuitionistically]
  rw' [persistently_forall_1, affinely_forall]

theorem intuitionistically_or [BI PROP] {P Q : PROP} : □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q := by
  simp only [intuitionistically]
  rw' [persistently_or, affinely_or]

theorem intuitionistically_exists [BI PROP] {Φ : α → PROP} : □ (∃ x, Φ x) ⊣⊢ ∃ x, □ Φ x := by
  simp only [intuitionistically]
  rw' [persistently_exists, affinely_exists]

theorem intuitionistically_sep_2 [BI PROP] {P Q : PROP} : □ P ∗ □ Q ⊢ □ (P ∗ Q) := by
  rw' [affinely_sep_2, persistently_sep_2]

@[rw_mono_rule]
theorem intuitionistically_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → □ P ⊢ □ Q := by
  intro H
  simp only [intuitionistically]
  rw' [H]

theorem intuitionistically_idem [BI PROP] {P : PROP} : □ □ P ⊣⊢ □ P := by
  simp only [intuitionistically]
  rw' [persistently_affinely_elim, persistently_idem]

theorem intuitionistically_into_persistently_1 [BI PROP] {P : PROP} : □ P ⊢ <pers> P := by
  rw' [affinely_elim]

theorem intuitionistically_persistently_elim [BI PROP] {P : PROP} : □ <pers> P ⊣⊢ □ P := by
  simp only [intuitionistically]
  rw' [persistently_idem]

theorem intuitionistic_intuitionistically [BI PROP] {P : PROP} [Affine P] [Persistent P] : □ P ⊣⊢ P := by
  apply anti_symm
  · exact intuitionistically_elim
  conv =>
    lhs
    rw [← affine_affinely P]
  rw' [persistent]

theorem intuitionistically_affinely [BI PROP] {P : PROP} : □ P ⊢ <affine> P := by
  simp only [intuitionistically, affinely]
  apply and_intro
  · exact and_elim_l
  · exact persistently_and_emp_elim

theorem intuitionistically_affinely_elim [BI PROP] {P : PROP} : □ <affine> P ⊣⊢ □ P := by
  simp only [intuitionistically]
  rw' [persistently_affinely_elim]

theorem persistently_and_intuitionistically_sep_l [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊣⊢ □ P ∗ Q := by
  apply anti_symm
  case left =>
    simp only [intuitionistically, affinely]
    rw' [
      (comm : emp ∧ <pers> P ⊣⊢ _),
      ← persistently_and_sep_assoc,
      (left_id : emp ∗ Q ⊣⊢ _)]
  case right =>
    apply and_intro
    · rw' [affinely_elim, persistently_absorb_l]
    · rw' [affinely_elim_emp, (left_id : emp ∗ Q ⊣⊢ _)]

theorem persistently_and_intuitionistically_sep_r [BI PROP] {P Q : PROP} : P ∧ <pers> Q ⊣⊢ P ∗ □ Q := by
  rw' [(comm : P ∧ _ ⊣⊢ _), (comm : P ∗ _ ⊣⊢ _)]
  exact persistently_and_intuitionistically_sep_l

theorem and_sep_intuitionistically [BI PROP] {P Q : PROP} : □ P ∧ □ Q ⊣⊢ □ P ∗ □ Q := by
  rw' [← persistently_and_intuitionistically_sep_l]
  simp only [intuitionistically]
  rw'[← affinely_and, affinely_and_r]

theorem intuitionistically_sep_dup [BI PROP] {P : PROP} : □ P ⊣⊢ □ P ∗ □ P := by
  rw' [← persistently_and_intuitionistically_sep_l]
  simp only [intuitionistically]
  rw' [
    affinely_and_r,
    (idem : _ ∧ _ ⊣⊢ _)]

-- Intuitionistic BIAffine
theorem intuitionistically_into_persistently [BIAffine PROP] {P : PROP} : □ P ⊣⊢ <pers> P := by
  exact affine_affinely _

-- Conditional Affine
@[rw_mono_rule]
theorem affinelyIf_mono {p : Bool} [BI PROP] {P Q : PROP} : (P ⊢ Q) → <affine>?p P ⊢ <affine>?p Q := by
  intro H
  cases p
  <;> simp [affinelyIf, H]
  revert H
  exact affinely_mono

theorem affinelyIf_flag_mono {p q : Bool} [BI PROP] {P : PROP} : (q → p) → <affine>?p P ⊢ <affine>?q P := by
  cases p
  <;> cases q
  <;> simp [affinelyIf, affinely_elim]

theorem affinelyIf_elim {p : Bool} [BI PROP] {P : PROP} : <affine>?p P ⊢ P := by
  cases p
  <;> simp [affinelyIf, affinely_elim]

theorem affinely_affinelyIf {p : Bool} [BI PROP] {P : PROP} : <affine> P ⊢ <affine>?p P := by
  cases p
  <;> simp [affinelyIf, affinely_elim]

theorem affinelyIf_and {p : Bool} [BI PROP] {P Q : PROP} : <affine>?p (P ∧ Q) ⊣⊢ <affine>?p P ∧ <affine>?p Q := by
  cases p
  <;> simp [affinelyIf, affinely_and]

theorem affinelyIf_or {p : Bool} [BI PROP] {P Q : PROP} : <affine>?p (P ∨ Q) ⊣⊢ <affine>?p P ∨ <affine>?p Q := by
  cases p
  <;> simp [affinelyIf, affinely_or]

theorem affinelyIf_exists {p : Bool} [BI PROP] {Ψ : α → PROP} : <affine>?p (∃ a, Ψ a) ⊣⊢ ∃ a, <affine>?p (Ψ a) := by
  cases p
  <;> simp [affinelyIf, affinely_exists]

theorem affinelyIf_intro_false [BI PROP] (P : PROP) : P ⊣⊢ <affine>?false P := by
  simp [affinelyIf]

theorem affinelyIf_intro_true [BI PROP] (P : PROP) : <affine> P ⊣⊢ <affine>?true P := by
  simp [affinelyIf]

-- Conditional Absorbing
@[rw_mono_rule]
theorem absorbinglyIf_mono {p : Bool} [BI PROP] {P Q : PROP} : (P ⊢ Q) → <absorb>?p P ⊢ <absorb>?p Q := by
  intro H
  cases p
  <;> simp [absorbinglyIf, H]
  revert H
  exact absorbingly_mono

-- Conditional Persistent
@[rw_mono_rule]
theorem persistentlyIf_mono {p : Bool} [BI PROP] {P Q : PROP} : (P ⊢ Q) → <pers>?p P ⊢ <pers>?p Q := by
  intro H
  cases p
  <;> simp [persistentlyIf, H]
  revert H
  exact persistently_mono

theorem persistentlyIf_intro_false [BI PROP] (P : PROP) : P ⊣⊢ <pers>?false P := by
  simp [persistentlyIf]

theorem persistentlyIf_intro_true [BI PROP] (P : PROP) : <pers> P ⊣⊢ <pers>?true P := by
  simp [persistentlyIf]

-- Conditional Intuitionistic
@[rw_mono_rule]
theorem intuitionisticallyIf_mono {p : Bool} [BI PROP] {P Q : PROP} : (P ⊢ Q) → □?p P ⊢ □?p Q := by
  intro H
  cases p
  <;> simp [intuitionisticallyIf, H]
  revert H
  exact intuitionistically_mono

theorem intuitionisticallyIf_elim {p : Bool} [BI PROP] {P : PROP} : □?p P ⊢ P := by
  cases p
  <;> simp [intuitionisticallyIf, intuitionistically_elim]

theorem intuitionistically_intuitionisticallyIf (p : Bool) [BI PROP] {P : PROP} : □ P ⊢ □?p P := by
  cases p
  <;> simp [intuitionisticallyIf]
  · exact intuitionistically_elim

theorem intuitionisticallyIf_and {p : Bool} [BI PROP] {P Q : PROP} : □?p (P ∧ Q) ⊣⊢ □?p P ∧ □?p Q := by
  cases p
  <;> simp [intuitionisticallyIf, intuitionistically_and]

theorem intuitionisticallyIf_or (p : Bool) [BI PROP] {P Q : PROP} : □?p (P ∨ Q) ⊣⊢ □?p P ∨ □?p Q := by
  cases p
  <;> simp [intuitionisticallyIf]
  rw' [intuitionistically_or]

theorem intuitionisticallyIf_exists {p : Bool} [BI PROP] {Ψ : α → PROP} : (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a := by
  cases p
  <;> simp [intuitionisticallyIf, intuitionistically_exists]

theorem intuitionisticallyIf_sep_2 {p : Bool} [BI PROP] {P Q : PROP} : □?p P ∗ □?p Q ⊢ □?p (P ∗ Q) := by
  cases p
  <;> simp [intuitionisticallyIf]
  · exact intuitionistically_sep_2

theorem intuitionisticallyIf_idem {p : Bool} [BI PROP] {P : PROP} : □?p □?p P ⊣⊢ □?p P := by
  cases p
  <;> simp [intuitionisticallyIf]
  · exact intuitionistically_idem

theorem intuitionisticallyIf_intro_true [BI PROP] (P : PROP) : □ P ⊣⊢ □?true P := by
  simp [intuitionisticallyIf]

-- Persistent Propositions
theorem persistent_persistently_2 [BI PROP] {P : PROP} [Persistent P] : P ⊢ <pers> P := by
  rw' [persistent]

theorem persistent_and_affinely_sep_l_1 [BI PROP] {P Q : PROP} [Persistent P] : P ∧ Q ⊢ <affine> P ∗ Q := by
  rw' [
    persistent_persistently_2,
    persistently_and_intuitionistically_sep_l,
    intuitionistically_affinely]

theorem persistent_and_affinely_sep_r_1 [BI PROP] {P Q : PROP} [Persistent Q] : P ∧ Q ⊢ P ∗ <affine> Q := by
  rw' [
    (comm : P ∧ Q ⊣⊢ _),
    ← (comm : _ ⊣⊢ P ∗ <affine> Q),
    persistent_and_affinely_sep_l_1]

theorem persistent_and_affinely_sep_l [BI PROP] {P Q : PROP} [Persistent P] [Absorbing P] :
  P ∧ Q ⊣⊢ <affine> P ∗ Q
:= by
  apply anti_symm
  <;> rw' [persistent, ← persistently_elim, persistently_and_intuitionistically_sep_l]

theorem persistent_and_affinely_sep_r [BI PROP] {P Q : PROP} [Persistent Q] [Absorbing Q] :
  P ∧ Q ⊣⊢ P ∗ <affine> Q
:= by
  apply anti_symm
  case left =>
    rw' [
      persistent,
      ← persistently_elim,
      persistently_and_intuitionistically_sep_r]
  case right =>
    rw' [
      persistent,
      ← persistently_elim,
      persistently_and_intuitionistically_sep_r]

theorem persistent_and_sep_1 [BI PROP] {P Q : PROP} [inst : TCOr (Persistent P) (Persistent Q)] :
  P ∧ Q ⊢ P ∗ Q
:= by
  cases inst
  · rw' [persistent_and_affinely_sep_l_1, affinely_elim]
  · rw' [persistent_and_affinely_sep_r_1, affinely_elim]

theorem absorbingly_intuitionistically_into_persistently [BI PROP] {P : PROP} :
  <absorb> □ P ⊣⊢ <pers> P
:= by
  apply anti_symm
  case left =>
    rw' [
      intuitionistically_into_persistently_1,
      absorbingly_elim_persistently]
  case right =>
    rw' [
      ← (idem : <pers> P ∧ _ ⊣⊢ _),
      persistently_and_intuitionistically_sep_r,
      (True_intro : <pers> P ⊢ _)]

theorem persistent_absorbingly_affinely_2 [BI PROP] {P : PROP} [Persistent P] : P ⊢ <absorb> <affine> P := by
  rw' [
    persistent,
    ← absorbingly_intuitionistically_into_persistently,
    intuitionistically_affinely]

-- Big Op
theorem bigOp_sep_nil [BI PROP] : [∗] term([]) ⊣⊢ (emp : PROP) := by
  simp only [bigOp]

theorem bigOp_and_nil [BI PROP] : [∧] term([]) ⊣⊢ (True : PROP) := by
  simp only [bigOp]

theorem bigOp_sep_cons [BI PROP] {P : PROP} {Ps : List PROP} : [∗] term(P :: Ps) ⊣⊢ P ∗ [∗] term(Ps) := by
  cases Ps
  <;> simp only [bigOp]
  rw' [(right_id : _ ∗ emp ⊣⊢ _)]

theorem bigOp_and_cons [BI PROP] {P : PROP} {Ps : List PROP} : [∧] term(P :: Ps) ⊣⊢ P ∧ [∧] term(Ps) := by
  cases Ps
  <;> simp only [bigOp]
  rw' [(right_id : _ ∧ True ⊣⊢ _)]

end Iris.BI
