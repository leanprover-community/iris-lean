import Iris.BI.BigOp
import Iris.BI.Classes
import Iris.BI.Extensions
import Iris.BI.Interface
import Iris.BI.DerivedConnectives
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

theorem impl_intro_l [BI PROP] {P Q R : PROP} : (Q ∧ P ⊢ R) → P ⊢ Q → R := by
  intro H
  apply impl_intro_r
  rw' [← H]
  apply and_intro
  · exact and_elim_r
  · exact and_elim_l

theorem impl_elim [BI PROP] {P Q R : PROP} : (P ⊢ Q → R) → (P ⊢ Q) → P ⊢ R := by
  intro H1 H2
  rw' [← impl_elim_l' H1]
  apply and_intro
  · simp
  · exact H2

theorem impl_elim_r' [BI PROP] {P Q R : PROP} : (Q ⊢ P → R) → P ∧ Q ⊢ R := by
  intros H
  apply impl_elim (Q := P)
  · rw' [and_elim_r, H]
  · rw' [and_elim_l]

theorem impl_elim_l [BI PROP] {P Q : PROP} : (P → Q) ∧ P ⊢ Q := by
  apply impl_elim_l'
  simp

theorem impl_elim_r [BI PROP] {P Q : PROP} : P ∧ (P → Q) ⊢ Q := by
  apply impl_elim_r'
  simp

theorem False_elim [BI PROP] {P : PROP} : False ⊢ P := by
  apply pure_elim'
  simp

theorem True_intro [BI PROP] {P : PROP} : P ⊢ True := by
  apply pure_intro
  simp

@[rwMonoRule]
theorem and_mono [BI PROP] {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∧ P' ⊢ Q ∧ Q' := by
  intro H1 H2
  apply and_intro
  · rw' [← H1, and_elim_l]
  · rw' [← H2, and_elim_r]

@[rwMonoRule]
theorem or_mono [BI PROP] {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∨ P' ⊢ Q ∨ Q' := by
  intro H1 H2
  apply or_elim
  · apply or_intro_l'
    exact H1
  · apply or_intro_r'
    exact H2

@[rwMonoRule]
theorem impl_mono [BI PROP] {P P' Q Q' : PROP} : (Q ⊢ P) → (P' ⊢ Q') → (P → P') ⊢ Q → Q' := by
  intro HP HQ
  apply impl_intro_r
  rw' [HP, ← HQ]
  apply impl_elim_l'
  simp

@[rwMonoRule]
theorem forall_mono [BI PROP] {Φ Ψ : α → PROP} :
  (∀ a, Φ a ⊢ Ψ a) → (∀ a, Φ a) ⊢ ∀ a, Ψ a
:= by
  intro Hφ
  apply forall_intro
  intro a
  rw' [← Hφ a, ← forall_elim _]

@[rwMonoRule]
theorem exist_mono [BI PROP] {Φ Ψ : α → PROP} :
  (∀ a, Φ a ⊢ Ψ a) → (∃ a, Φ a) ⊢ ∃ a, Ψ a
:= by
  intro Hφ
  apply exist_elim
  intro a
  rw' [Hφ a, exist_intro _]

instance and_idemp [BI PROP] : Idemp (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∧ ·]) where
  idemp := by
    intro _
    apply anti_symm
    · exact and_elim_l
    · apply and_intro
      <;> simp

instance or_idemp [BI PROP] : Idemp (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∨ ·]) where
  idemp := by
    intro _
    apply anti_symm
    · apply or_elim
      <;> simp
    · exact or_intro_l

instance and_comm [BI PROP] : Comm (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∧ ·]) where
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

instance True_and [BI PROP] : LeftId (α := PROP) (· ⊣⊢ ·) `[iprop| True] (`[iprop| · ∧ ·]) where
  left_id := by
    intros
    apply anti_symm
    case left =>
      exact and_elim_r
    case right =>
      apply and_intro ?_ reflexivity
      apply pure_intro
      simp

instance and_True [BI PROP] : RightId (α := PROP) (· ⊣⊢ ·) `[iprop| True] (`[iprop| · ∧ ·]) where
  right_id := by
    intros
    apply anti_symm
    case left =>
      exact and_elim_l
    case right =>
      apply and_intro reflexivity ?_
      apply pure_intro
      simp

instance and_assoc [BI PROP] : Assoc (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∧ ·]) where
  assoc := by
    intro _ _ _
    apply anti_symm
    <;> repeat apply and_intro
    <;> repeat apply and_intro
    · exact and_elim_l
    · apply and_elim_r'
      exact and_elim_l
    · apply and_elim_r'
      exact and_elim_r
    · apply and_elim_l'
      exact and_elim_l
    · apply and_elim_l'
      exact and_elim_r
    · exact and_elim_r

theorem and_or_l [BI PROP] {P Q R : PROP} : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R := by
  apply anti_symm
  case left =>
    apply impl_elim_r'
    apply or_elim
    <;> apply impl_intro_l
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

theorem and_exist_l [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a := by
  apply anti_symm
  case left =>
    apply impl_elim_r'
    apply exist_elim
    intro a
    apply impl_intro_l
    rw' [← exist_intro a]
  case right =>
    apply exist_elim
    intro a
    apply and_intro
    · rw' [and_elim_l]
    · rw' [← exist_intro a, and_elim_r]

theorem or_alt [BI PROP] {P Q : PROP} : P ∨ Q ⊣⊢ ∃ (b : Bool), if b then P else Q := by
  apply anti_symm
  case left =>
    apply or_elim
    · rw' [← exist_intro true]
    · rw' [← exist_intro false]
  case right =>
    apply exist_elim
    intro b
    cases b
    · rw' [← or_intro_r]
    · rw' [← or_intro_l]

-- BI
@[rwMonoRule]
theorem wand_mono [BI PROP] {P P' Q Q' : PROP} : (Q ⊢ P) → (P' ⊢ Q') → (P -∗ P') ⊢ Q -∗ Q' := by
  intro HP HQ
  apply wand_intro_r
  rw' [HP, ← HQ]
  apply wand_elim_l'
  simp

instance sep_comm [BI PROP] : Comm (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∗ ·]) where
  comm := by
    intros
    apply anti_symm
    <;> exact sep_comm'

instance sep_assoc [BI PROP] : Assoc (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∗ ·]) where
  assoc := by
    intros P Q R
    apply anti_symm
    case left =>
      rw' [
        (comm : P ∗ (Q ∗ R) ⊣⊢ _),
        (comm : P ∗ Q ⊣⊢ _),
        (comm : Q ∗ R ⊣⊢ _),
        (comm : (Q ∗ P) ∗ R ⊣⊢ _),
        sep_assoc']
    case right =>
      exact sep_assoc'

instance emp_sep [BI PROP] : LeftId (α := PROP) (· ⊣⊢ ·) `[iprop| emp] (`[iprop| · ∗ ·]) where
  left_id := by
    intros
    apply anti_symm
    · exact emp_sep_2
    · exact emp_sep_1

instance sep_emp [BI PROP] : RightId (α := PROP) (· ⊣⊢ ·) `[iprop| emp] (`[iprop| · ∗ ·]) where
  right_id := by
    intro x
    rw' [(comm : `[iprop| x ∗ emp] ⊣⊢ _), (left_id : emp ∗ x ⊣⊢ _)]

theorem True_sep_2 [BI PROP] {P : PROP} : P ⊢ True ∗ P := by
  rw' [emp_sep_1]
  apply sep_mono ?_ reflexivity
  apply pure_intro
  simp

theorem wand_intro_l [BI PROP] {P Q R : PROP} : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R := by
  rw' [(comm : Q ∗ P ⊣⊢ _)]
  exact wand_intro_r

theorem wand_elim_l [BI PROP] {P Q : PROP} : (P -∗ Q) ∗ P ⊢ Q := by
  apply wand_elim_l'
  simp

theorem wand_elim_r [BI PROP] {P Q : PROP} : P ∗ (P -∗ Q) ⊢ Q := by
  rw' [sep_comm', wand_elim_l]

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

theorem sep_exist_l [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a := by
  apply anti_symm
  case left =>
    apply wand_elim_r'
    apply exist_elim
    intro a
    apply wand_intro_l
    rw' [← exist_intro a]
  case right =>
    apply exist_elim
    intro a
    rw' [(exist_intro _ : Ψ a ⊢ _)]

theorem sep_exist_r [BI PROP] {Φ : α → PROP} {Q : PROP} : (∃ a, Φ a) ∗ Q ⊣⊢ ∃ a, Φ a ∗ Q := by
  apply anti_symm
  all_goals
    rw' [(comm : _ ∗ Q ⊣⊢ _), sep_exist_l]
    apply exist_mono
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
  apply wand_intro_r
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
  <;> simp [bi_wand_iff, and_elim_l, and_elim_r]

-- Pure
theorem pure_elim (φ : Prop) [BI PROP] {Q R : PROP} : (Q ⊢ ⌜φ⌝) → (φ → Q ⊢ R) → Q ⊢ R := by
  intro HQ HQR
  rw' [← (idemp : Q ∧ Q ⊣⊢ _), HQ]
  apply impl_elim_l'
  apply pure_elim'
  intro Hφ
  apply impl_intro_l
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

theorem pure_impl_1 {φ1 φ2 : Prop} [BI PROP] : ⌜φ1 → φ2⌝ ⊢ (⌜φ1⌝ → ⌜φ2⌝ : PROP) := by
  apply impl_intro_l
  rw' [← pure_and]
  apply pure_mono
  simp_all

theorem pure_forall_1 {φ : α → Prop} [BI PROP] : ⌜∀ x, φ x⌝ ⊢ ∀ x, (⌜φ x⌝ : PROP) := by
  apply forall_intro
  intro x
  apply pure_mono
  simp_all

theorem pure_exist [inst : BI PROP] {φ : α → Prop} : ⌜∃ x, φ x⌝ ⊣⊢ (∃ x, ⌜φ x⌝ : PROP) := by
  apply anti_symm
  case left =>
    apply pure_elim'
    intro ⟨x, H⟩
    rw' [← exist_intro x]
    apply pure_mono
    intro _
    exact H
  case right =>
    apply exist_elim
    intro a
    apply pure_mono
    intro H
    exact ⟨a, H⟩

-- Affine
theorem affinely_elim_emp [BI PROP] {P : PROP} : <affine> P ⊢ emp := by
  simp [bi_affinely, and_elim_l]

theorem affinely_elim [BI PROP] {P : PROP} : <affine> P ⊢ P := by
  simp [bi_affinely, and_elim_r]

@[rwMonoRule]
theorem affinely_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <affine> P ⊢ <affine> Q := by
  intro H
  simp only [bi_affinely]
  rw' [H]

theorem affinely_idemp [BI PROP] {P : PROP} : <affine> <affine> P ⊣⊢ <affine> P := by
  simp only [bi_affinely]
  rw' [
    (assoc : emp ∧ emp ∧ _ ⊣⊢ _),
    (idemp : emp ∧ emp ⊣⊢ _)]

theorem affinely_emp [BI PROP] : <affine> emp ⊣⊢ (emp : PROP) := by
  simp only [bi_affinely]
  exact idemp

theorem affinely_or [BI PROP] {P Q : PROP} : <affine> (P ∨ Q) ⊣⊢ <affine> P ∨ <affine> Q := by
  exact and_or_l

theorem affinely_and [BI PROP] {P Q : PROP} : <affine> (P ∧ Q) ⊣⊢ <affine> P ∧ <affine> Q := by
  rw' [
    !bi_affinely,
    (comm : emp ∧ P ⊣⊢ _),
    (assoc : (P ∧ emp) ∧ _ ⊣⊢ _),
    ← (assoc : _ ⊣⊢ (P ∧ emp) ∧ _),
    ← (assoc : _ ⊣⊢ (P ∧ emp ∧ emp) ∧ _),
    (idemp : emp ∧ emp ⊣⊢ _),
    (assoc : P ∧ emp ∧ _ ⊣⊢ _),
    (assoc : emp ∧ P ∧ _ ⊣⊢ _),
    (comm : emp ∧ P ⊣⊢ _)]

theorem affinely_sep_2 [BI PROP] {P Q : PROP} : <affine> P ∗ <affine> Q ⊢ <affine> (P ∗ Q) := by
  simp only [bi_affinely]
  apply and_intro
  · rw' [!and_elim_l, (right_id : emp ∗ emp ⊣⊢ _)]
  · rw' [!and_elim_r]

theorem affinely_forall [BI PROP] {Φ : α → PROP} : <affine> (∀ a, Φ a) ⊢ ∀ a, <affine> (Φ a) := by
  apply forall_intro
  intro a
  rw' [forall_elim a]

theorem affinely_exist [BI PROP] {Φ : α → PROP} : <affine> (∃ a, Φ a) ⊣⊢ ∃ a, <affine> (Φ a) := by
  exact and_exist_l

theorem affinely_True_emp [BI PROP] : <affine> True ⊣⊢ <affine> (emp : PROP) := by
  apply anti_symm
  <;> simp only [bi_affinely]
  · apply and_intro
    <;> exact and_elim_l
  · rw' [(right_id : _ ∧ True ⊣⊢ _)]
    exact and_elim_l

theorem affinely_and_l [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ <affine> (P ∧ Q) := by
  simp only [bi_affinely]
  rw' [(assoc : emp ∧ P ∧ _ ⊣⊢ _)]

theorem affinely_and_r [BI PROP] {P Q : PROP} : P ∧ <affine> Q ⊣⊢ <affine> (P ∧ Q) := by
  simp only [bi_affinely]
  rw' [
    (assoc : P ∧ emp ∧ _ ⊣⊢ _),
    (assoc : emp ∧ P ∧ _ ⊣⊢ _),
    (comm : P ∧ emp ⊣⊢ _)]

theorem affinely_and_lr [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ P ∧ <affine> Q := by
  rw' [affinely_and_l, affinely_and_r]

-- Absorbing
theorem absorbingly_intro [BI PROP] {P : PROP} : P ⊢ <absorb> P := by
  exact True_sep_2

@[rwMonoRule]
theorem absorbingly_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <absorb> P ⊢ <absorb> Q := by
  intro H
  simp only [bi_absorbingly]
  rw' [H]

theorem absorbingly_idemp [BI PROP] {P : PROP} : <absorb> <absorb> P ⊣⊢ <absorb> P := by
  apply anti_symm
  case left =>
    simp only [bi_absorbingly]
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
  simp [bi_absorbingly, sep_or_l]

theorem absorbingly_and_1 [BI PROP] {P Q : PROP} : <absorb> (P ∧ Q) ⊢ <absorb> P ∧ <absorb> Q := by
  apply and_intro
  · rw' [and_elim_l]
  · rw' [and_elim_r]

theorem absorbingly_forall [BI PROP] (Φ : α → PROP) : <absorb> (∀ a, Φ a) ⊢ ∀ a, <absorb> (Φ a) := by
  apply forall_intro
  intro a
  rw' [forall_elim a]

theorem absorbingly_exist [BI PROP] (Φ : α → PROP) : <absorb> (∃ a, Φ a) ⊣⊢ ∃ a, <absorb> (Φ a) := by
  simp [bi_absorbingly, sep_exist_l]

theorem absorbingly_sep [BI PROP] {P Q : PROP} : <absorb> (P ∗ Q) ⊣⊢ <absorb> P ∗ <absorb> Q := by
  rw' [← absorbingly_idemp]
  simp only [bi_absorbingly]
  rw' [
    (assoc : True ∗ P ∗ Q ⊣⊢ _),
    (assoc : True ∗ (True ∗ P) ∗ Q ⊣⊢ _),
    (comm : True ∗ True ∗ P ⊣⊢ _),
    ← (assoc : _ ⊣⊢ ((True ∗ P) ∗ True) ∗ Q)]

theorem absorbingly_True_emp [BI PROP] : <absorb> True ⊣⊢ <absorb> (emp : PROP) := by
  rw' [absorbingly_pure]
  simp only [bi_absorbingly]
  rw' [(right_id : True ∗ emp ⊣⊢ _)]

theorem absorbingly_wand [BI PROP] {P Q : PROP} : <absorb> (P -∗ Q) ⊢ <absorb> P -∗ <absorb> Q := by
  apply wand_intro_l
  rw' [← absorbingly_sep, wand_elim_r]

theorem absorbingly_sep_l [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ <absorb> (P ∗ Q) := by
  simp only [bi_absorbingly]
  rw' [(assoc : True ∗ P ∗ Q ⊣⊢ _)]

theorem absorbingly_sep_r [BI PROP] {P Q : PROP} : P ∗ <absorb> Q ⊣⊢ <absorb> (P ∗ Q) := by
  simp only [bi_absorbingly]
  rw' [!(assoc : _ ⊣⊢ _ ∗ Q), (comm : P ∗ True ⊣⊢ _)]

theorem absorbingly_sep_lr [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ P ∗ <absorb> Q := by
  rw' [absorbingly_sep_l, absorbingly_sep_r]

-- Affine / Absorbing Propositions
theorem affine_affinely [BI PROP] (P : PROP) [Affine P] : <affine> P ⊣⊢ P := by
  apply anti_symm
  <;> simp only [bi_affinely]
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
    simp only [bi_absorbingly]
    rw' [
      (comm : `[iprop| True ∗ <pers> P] ⊣⊢ _),
      persistently_absorbing]
  case right =>
    exact absorbingly_intro

theorem persistently_forall_1 [BI PROP] {Ψ : α → PROP} : <pers> (∀ a, Ψ a) ⊢ ∀ a, <pers> (Ψ a) := by
  apply forall_intro
  intro x
  rw' [forall_elim x]

theorem persistently_exist [BI PROP] {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊣⊢ ∃ a, <pers> (Ψ a) := by
  apply anti_symm
  case left =>
    exact persistently_exist_1
  case right =>
    apply exist_elim
    intro a
    rw' [exist_intro a]

theorem persistently_and [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊣⊢ <pers> P ∧ <pers> Q := by
  apply anti_symm
  case left =>
    apply and_intro
    · rw' [and_elim_l]
    · rw' [and_elim_r]
  case right =>
    exact persistently_and_2

theorem persistently_if {p : Bool} [BI PROP] {P Q : PROP} :
  (<pers> if p then P else Q) ⊣⊢ if p then <pers> P else <pers> Q
:= by
  cases p
  <;> simp

theorem persistently_or [BI PROP] {P Q : PROP} : <pers> (P ∨ Q) ⊣⊢ <pers> P ∨ <pers> Q := by
  rw' [!or_alt, persistently_exist]
  apply anti_symm
  <;> apply exist_elim
  <;> intro a
  <;> rw' [← exist_intro a, persistently_if]

theorem persistently_emp_intro [BI PROP] {P : PROP} : P ⊢ <pers> emp := by
  rw' [← persistently_absorbing (Q := P)]
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
  rw' [persistently_and_emp, persistently_and_sep_elim]

theorem persistently_and_sep_assoc [BI PROP] {P Q R : PROP} : <pers> P ∧ (Q ∗ R) ⊣⊢ (<pers> P ∧ Q) ∗ R := by
  apply anti_symm
  case left =>
    rw' [
      persistently_idemp_2,
      persistently_and_sep_elim_emp,
      (assoc : (emp ∧ <pers> P) ∗ Q ∗ R ⊣⊢ _)]
    apply sep_mono ?_ reflexivity
    apply and_intro
    · rw' [and_elim_r, persistently_absorbing]
    · rw' [and_elim_l, (left_id : emp ∗ Q ⊣⊢ _)]
  case right =>
    apply and_intro
    · rw' [and_elim_l, persistently_absorbing]
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
    (comm : `[iprop| <pers> P ∧ emp] ⊣⊢ _),
    persistently_and_emp_elim,
    (comm : `[iprop| P ∗ True] ⊣⊢ _)]

theorem persistently_elim [BI PROP] {P : PROP} [Absorbing P] : <pers> P ⊢ P := by
  rw' [persistently_into_absorbingly, absorbing]

theorem persistently_idemp [BI PROP] {P : PROP} : <pers> <pers> P ⊣⊢ <pers> P := by
  apply anti_symm
  · rw' [persistently_into_absorbingly, absorbingly_elim_persistently]
  · exact persistently_idemp_2

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
    rw [← (left_id : `[iprop| emp ∗ Q] ⊣⊢ _)]
  rw' [persistently_and_sep_assoc, and_elim_l]

theorem persistently_and_sep [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊢ <pers> (P ∗ Q) := by
  rw' [persistently_and, ← persistently_idemp, ← persistently_and]
  conv =>
    lhs
    rw [← (left_id : emp ∗ Q ⊣⊢ _)]
  rw' [
    persistently_and_sep_assoc,
    (comm : <pers> P ∧ emp ⊣⊢ _),
    persistently_and_emp_elim]

theorem persistently_affinely_elim [BI PROP] {P : PROP} : <pers> <affine> P ⊣⊢ <pers> P := by
  simp only [bi_affinely]
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
    · exact persistently_absorbing
    · rw' [(comm : `[iprop| <pers> P ∗ <pers> Q ⊣⊢ _]), persistently_absorbing]

theorem persistently_sep_2 [BI PROP] {P Q : PROP} : <pers> P ∗ <pers> Q ⊢ <pers> (P ∗ Q) := by
  rw' [← persistently_and_sep, persistently_and, ← and_sep_persistently]

-- Intuitionistic
theorem intuitionistically_elim [BI PROP] {P : PROP} : □ P ⊢ P := by
  exact persistently_and_emp_elim

theorem intuitionistically_emp [BI PROP] : □ emp ⊣⊢ (emp : PROP) := by
  simp only [bi_intuitionistically]
  rw' [
    ← persistently_True_emp,
    persistently_pure,
    affinely_True_emp,
    affinely_emp]

theorem intuitionistically_True_emp [BI PROP] : □ True ⊣⊢ (emp : PROP) := by
  rw' [← intuitionistically_emp]
  simp only [bi_intuitionistically]
  rw' [persistently_True_emp]

theorem intuitionistically_and [BI PROP] {P Q : PROP} : □ (P ∧ Q) ⊣⊢ □ P ∧ □ Q := by
  simp only [bi_intuitionistically]
  rw' [persistently_and, affinely_and]

theorem intuitionistically_forall [BI PROP] {Φ : α → PROP} : □ (∀ x, Φ x) ⊢ ∀ x, □ Φ x := by
  simp only [bi_intuitionistically]
  rw' [persistently_forall_1, affinely_forall]

theorem intuitionistically_or [BI PROP] {P Q : PROP} : □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q := by
  simp only [bi_intuitionistically]
  rw' [persistently_or, affinely_or]

theorem intuitionistically_exist [BI PROP] {Φ : α → PROP} : □ (∃ x, Φ x) ⊣⊢ ∃ x, □ Φ x := by
  simp only [bi_intuitionistically]
  rw' [persistently_exist, affinely_exist]

theorem intuitionistically_sep_2 [BI PROP] {P Q : PROP} : □ P ∗ □ Q ⊢ □ (P ∗ Q) := by
  rw' [affinely_sep_2, persistently_sep_2]

@[rwMonoRule]
theorem intuitionistically_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → □ P ⊢ □ Q := by
  intro H
  simp only [bi_intuitionistically]
  rw' [H]

theorem intuitionistically_idemp [BI PROP] {P : PROP} : □ □ P ⊣⊢ □ P := by
  simp only [bi_intuitionistically]
  rw' [persistently_affinely_elim, persistently_idemp]

theorem intuitionistically_into_persistently_1 [BI PROP] {P : PROP} : □ P ⊢ <pers> P := by
  rw' [affinely_elim]

theorem intuitionistically_persistently_elim [BI PROP] {P : PROP} : □ <pers> P ⊣⊢ □ P := by
  simp only [bi_intuitionistically]
  rw' [persistently_idemp]

theorem intuitionistic_intuitionistically [BI PROP] {P : PROP} [Affine P] [Persistent P] : □ P ⊣⊢ P := by
  apply anti_symm
  · exact intuitionistically_elim
  conv =>
    lhs
    rw [← affine_affinely P]
  rw' [persistent]

theorem intuitionistically_affinely [BI PROP] {P : PROP} : □ P ⊢ <affine> P := by
  simp only [bi_intuitionistically, bi_affinely]
  apply and_intro
  · exact and_elim_l
  · exact persistently_and_emp_elim

theorem intuitionistically_affinely_elim [BI PROP] {P : PROP} : □ <affine> P ⊣⊢ □ P := by
  simp only [bi_intuitionistically]
  rw' [persistently_affinely_elim]

theorem persistently_and_intuitionistically_sep_l [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊣⊢ □ P ∗ Q := by
  apply anti_symm
  case left =>
    simp only [bi_intuitionistically, bi_affinely]
    rw' [
      (comm : emp ∧ <pers> P ⊣⊢ _),
      ← persistently_and_sep_assoc,
      (left_id : emp ∗ Q ⊣⊢ _)]
  case right =>
    apply and_intro
    · rw' [affinely_elim, persistently_absorbing]
    · rw' [affinely_elim_emp, (left_id : emp ∗ Q ⊣⊢ _)]

theorem persistently_and_intuitionistically_sep_r [BI PROP] {P Q : PROP} : P ∧ <pers> Q ⊣⊢ P ∗ □ Q := by
  rw' [(comm : P ∧ _ ⊣⊢ _), (comm : P ∗ _ ⊣⊢ _)]
  exact persistently_and_intuitionistically_sep_l

theorem and_sep_intuitionistically [BI PROP] {P Q : PROP} : □ P ∧ □ Q ⊣⊢ □ P ∗ □ Q := by
  rw' [← persistently_and_intuitionistically_sep_l]
  simp only [bi_intuitionistically]
  rw'[← affinely_and, affinely_and_r]

theorem intuitionistically_sep_dup [BI PROP] {P : PROP} : □ P ⊣⊢ □ P ∗ □ P := by
  rw' [← persistently_and_intuitionistically_sep_l]
  simp only [bi_intuitionistically]
  rw' [
    affinely_and_r,
    (idemp : _ ∧ _ ⊣⊢ _)]

-- Intuitionistic BIAffine
theorem intuitionistically_into_persistently [BIAffine PROP] {P : PROP} : □ P ⊣⊢ <pers> P := by
  exact affine_affinely _

-- Conditional Affine
@[rwMonoRule]
theorem affinely_if_mono {p : Bool} [BI PROP] {P Q : PROP} : (P ⊢ Q) → <affine>?p P ⊢ <affine>?p Q := by
  intro H
  cases p
  <;> simp [bi_affinely_if, H]
  revert H
  exact affinely_mono

theorem affinely_if_flag_mono {p q : Bool} [BI PROP] {P : PROP} : (q → p) → <affine>?p P ⊢ <affine>?q P := by
  cases p
  <;> cases q
  <;> simp [bi_affinely_if, affinely_elim]

theorem affinely_if_elim {p : Bool} [BI PROP] {P : PROP} : <affine>?p P ⊢ P := by
  cases p
  <;> simp [bi_affinely_if, affinely_elim]

theorem affinely_affinely_if {p : Bool} [BI PROP] {P : PROP} : <affine> P ⊢ <affine>?p P := by
  cases p
  <;> simp [bi_affinely_if, affinely_elim]

theorem affinely_if_and {p : Bool} [BI PROP] {P Q : PROP} : <affine>?p (P ∧ Q) ⊣⊢ <affine>?p P ∧ <affine>?p Q := by
  cases p
  <;> simp [bi_affinely_if, affinely_and]

theorem affinely_if_or {p : Bool} [BI PROP] {P Q : PROP} : <affine>?p (P ∨ Q) ⊣⊢ <affine>?p P ∨ <affine>?p Q := by
  cases p
  <;> simp [bi_affinely_if, affinely_or]

theorem affinely_if_exist {p : Bool} [BI PROP] {Ψ : α → PROP} : <affine>?p (∃ a, Ψ a) ⊣⊢ ∃ a, <affine>?p (Ψ a) := by
  cases p
  <;> simp [bi_affinely_if, affinely_exist]

theorem affinely_if_intro_False [BI PROP] (P : PROP) : P ⊣⊢ <affine>?false P := by
  simp [bi_affinely_if]

theorem affinely_if_intro_True [BI PROP] (P : PROP) : <affine> P ⊣⊢ <affine>?true P := by
  simp [bi_affinely_if]

-- Conditional Absorbing
@[rwMonoRule]
theorem absorbingly_if_mono {p : Bool} [BI PROP] {P Q : PROP} : (P ⊢ Q) → <absorb>?p P ⊢ <absorb>?p Q := by
  intro H
  cases p
  <;> simp [bi_absorbingly_if, H]
  revert H
  exact absorbingly_mono

-- Conditional Persistent
@[rwMonoRule]
theorem persistently_if_mono {p : Bool} [BI PROP] {P Q : PROP} : (P ⊢ Q) → <pers>?p P ⊢ <pers>?p Q := by
  intro H
  cases p
  <;> simp [bi_persistently_if, H]
  revert H
  exact persistently_mono

theorem persistently_if_intro_False [BI PROP] (P : PROP) : P ⊣⊢ <pers>?false P := by
  simp [bi_persistently_if]

theorem persistently_if_intro_True [BI PROP] (P : PROP) : <pers> P ⊣⊢ <pers>?true P := by
  simp [bi_persistently_if]

-- Conditional Intuitionistic
@[rwMonoRule]
theorem intuitionistically_if_mono {p : Bool} [BI PROP] {P Q : PROP} : (P ⊢ Q) → □?p P ⊢ □?p Q := by
  intro H
  cases p
  <;> simp [bi_intuitionistically_if, H]
  revert H
  exact intuitionistically_mono

theorem intuitionistically_if_elim {p : Bool} [BI PROP] {P : PROP} : □?p P ⊢ P := by
  cases p
  <;> simp [bi_intuitionistically_if, intuitionistically_elim]

theorem intuitionistically_intuitionistically_if (p : Bool) [BI PROP] {P : PROP} : □ P ⊢ □?p P := by
  cases p
  <;> simp [bi_intuitionistically_if]
  · exact intuitionistically_elim

theorem intuitionistically_if_and {p : Bool} [BI PROP] {P Q : PROP} : □?p (P ∧ Q) ⊣⊢ □?p P ∧ □?p Q := by
  cases p
  <;> simp [bi_intuitionistically_if, intuitionistically_and]

theorem intuitionistically_if_or (p : Bool) [BI PROP] {P Q : PROP} : □?p (P ∨ Q) ⊣⊢ □?p P ∨ □?p Q := by
  cases p
  <;> simp [bi_intuitionistically_if]
  rw' [intuitionistically_or]

theorem intuitionistically_if_exist {p : Bool} [BI PROP] {Ψ : α → PROP} : (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a := by
  cases p
  <;> simp [bi_intuitionistically_if, intuitionistically_exist]

theorem intuitionistically_if_sep_2 {p : Bool} [BI PROP] {P Q : PROP} : □?p P ∗ □?p Q ⊢ □?p (P ∗ Q) := by
  cases p
  <;> simp [bi_intuitionistically_if]
  · exact intuitionistically_sep_2

theorem intuitionistically_if_idemp {p : Bool} [BI PROP] {P : PROP} : □?p □?p P ⊣⊢ □?p P := by
  cases p
  <;> simp [bi_intuitionistically_if]
  · exact intuitionistically_idemp

theorem intuitionistically_if_intro_True [BI PROP] (P : PROP) : □ P ⊣⊢ □?true P := by
  simp [bi_intuitionistically_if]

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
      ← (idemp : <pers> P ∧ _ ⊣⊢ _),
      persistently_and_intuitionistically_sep_r,
      (True_intro : <pers> P ⊢ _)]

theorem persistent_absorbingly_affinely_2 [BI PROP] {P : PROP} [Persistent P] : P ⊢ <absorb> <affine> P := by
  rw' [
    persistent,
    ← absorbingly_intuitionistically_into_persistently,
    intuitionistically_affinely]

-- Big Op
theorem big_op_sep_nil [BI PROP] : [∗] `[term| []] ⊣⊢ (emp : PROP) := by
  simp only [big_op]

theorem big_op_and_nil [BI PROP] : [∧] `[term| []] ⊣⊢ (True : PROP) := by
  simp only [big_op]

theorem big_op_sep_cons [BI PROP] {P : PROP} {Ps : List PROP} : [∗] `[term| P :: Ps] ⊣⊢ P ∗ [∗] `[term| Ps] := by
  cases Ps
  <;> simp only [big_op]
  rw' [(right_id : _ ∗ emp ⊣⊢ _)]

theorem big_op_and_cons [BI PROP] {P : PROP} {Ps : List PROP} : [∧] `[term| P :: Ps] ⊣⊢ P ∧ [∧] `[term| Ps] := by
  cases Ps
  <;> simp only [big_op]
  rw' [(right_id : _ ∧ True ⊣⊢ _)]

end Iris.BI
