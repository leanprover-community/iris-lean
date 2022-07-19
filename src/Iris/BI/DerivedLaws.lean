import Iris.BI.Classes
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

scoped macro "anti_symm" colGt PROP:term : term => `(anti_symm (α := $PROP) (R := (· ⊣⊢ ·)) (S := (· ⊢ ·)) ?left ?right)

-- INSTANCES
-- And
instance and_comm [BI PROP] : Comm (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∧ ·]) where
  comm := by
    intros
    apply anti_symm PROP
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
    apply anti_symm PROP
    case left =>
      exact and_elim_r
    case right =>
      apply and_intro ?_ reflexivity
      apply pure_intro
      simp

instance and_True [BI PROP] : RightId (α := PROP) (· ⊣⊢ ·) `[iprop| True] (`[iprop| · ∧ ·]) where
  right_id := by
    intros
    apply anti_symm PROP
    case left =>
      exact and_elim_l
    case right =>
      apply and_intro reflexivity ?_
      apply pure_intro
      simp

-- Sep
instance sep_comm [BI PROP] : Comm (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∗ ·]) where
  comm := by
    intros
    apply anti_symm PROP
    <;> exact sep_comm'

instance sep_assoc [BI PROP] : Assoc (α := PROP) (· ⊣⊢ ·) (`[iprop| · ∗ ·]) where
  assoc := by
    intros P Q R
    apply anti_symm PROP
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
    apply anti_symm PROP
    · exact emp_sep_2
    · exact emp_sep_1

instance sep_emp [BI PROP] : RightId (α := PROP) (· ⊣⊢ ·) `[iprop| emp] (`[iprop| · ∗ ·]) where
  right_id := by
    intro x
    rw' [(comm : `[iprop| x ∗ emp] ⊣⊢ _), (left_id : emp ∗ x ⊣⊢ _)]

instance sep_mono' [BI PROP] : MonotonicBinary (α := PROP) (· ⊢ ·) (`[iprop| · ∗ ·]) where
  monotonicity_binary := sep_mono

-- Persistent
instance persistently_mono' [BI PROP] : MonotonicUnary (α := PROP) (· ⊢ ·) (`[iprop| <pers> ·]) where
  monotonicity_unary := persistently_mono

-- THEOREMS
-- Logic
theorem or_intro_l' [BI PROP] {P Q R : PROP} : (P ⊢ Q) → P ⊢ Q ∨ R := by
  intro H
  rw' [H, ← or_intro_l]

theorem or_intro_r' [BI PROP] {P Q R : PROP} : (P ⊢ R) → P ⊢ Q ∨ R := by
  intro H
  rw' [H, ← or_intro_r]

theorem impl_intro_l [BI PROP] {P Q R : PROP} : (Q ∧ P ⊢ R) → P ⊢ Q → R := by
  intro H
  apply impl_intro_r
  rw' [← H, (comm : P ∧ Q ⊣⊢ _)]

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

theorem impl_elim_r [BI PROP] {P Q : PROP} : P ∧ (P → Q) ⊢ Q := by
  apply impl_elim_r'
  simp

theorem False_elim [BI PROP] {P : PROP} : False ⊢ P := by
  apply pure_elim'
  simp

instance and_mono' [BI PROP] : MonotonicBinary (α := PROP) (· ⊢ ·) (`[iprop| · ∧ ·]) where
  monotonicity_binary := by
    intro _ _ _ _ H1 H2
    apply and_intro
    · rw' [← H1, and_elim_l]
    · rw' [← H2, and_elim_r]

instance or_mono' [BI PROP] : MonotonicBinary (α := PROP) (· ⊢ ·) (`[iprop| · ∨ ·]) where
  monotonicity_binary := by
    intro _ _ _ _ H1 H2
    apply or_elim
    · apply or_intro_l'
      exact H1
    · apply or_intro_r'
      exact H2

instance impl_mono' [BI PROP] : MonotonicLeftContravariantBinary (α := PROP) (· ⊢ ·) (`[iprop| · → ·]) where
  monotonicity_left_contravariant_binary := by
    intro _ _ _ _ HP HQ
    apply impl_intro_r
    rw' [HP, ← HQ]
    apply impl_elim_l'
    simp

instance forall_mono' [BI PROP] : MonotonicPointwiseUnary (α := PROP) (β := β) (· ⊢ ·) BIBase.forall where
  monotonicity_pointwise_unary := by
    intro _ _ Hφ
    apply forall_intro
    intro a
    rw' [← Hφ a, ← forall_elim _]

instance exist_mono' [BI PROP] : MonotonicPointwiseUnary (α := PROP) (β := β) (· ⊢ ·) BIBase.exists where
  monotonicity_pointwise_unary := by
    intro _ _ Hφ
    apply exist_elim
    intro a
    rw' [Hφ a, exist_intro _]

theorem or_alt [BI PROP] {P Q : PROP} : P ∨ Q ⊣⊢ ∃ (b : Bool), if b then P else Q := by
  apply anti_symm PROP
  case left =>
    apply or_elim ?left ?right
    · rw' [← exist_intro true]
    · rw' [← exist_intro false]
  case right =>
    apply exist_elim
    intro b
    cases b
    · rw' [← or_intro_r]
    · rw' [← or_intro_l]

-- BI
instance wand_mono' [BI PROP] : MonotonicLeftContravariantBinary (α := PROP) (· ⊢ ·) (`[iprop| · -∗ ·]) where
  monotonicity_left_contravariant_binary := by
    intro _ _ _ _ HP HQ
    apply wand_intro_r
    rw' [HP, ← HQ]
    apply wand_elim_l'
    simp

theorem True_sep_2 [BI PROP] {P : PROP} : P ⊢ True ∗ P := by
  rw' [emp_sep_1]
  apply monotonicity_binary ?_ reflexivity
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
  apply anti_symm PROP
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

theorem sep_exist_l [BI PROP] {P : PROP} (Ψ : A → PROP) : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a := by
  apply anti_symm PROP
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

-- Affine
theorem affinely_elim_emp [BI PROP] {P : PROP} : <affine> P ⊢ emp := by
  simp [bi_affinely, and_elim_l]

theorem affinely_elim [BI PROP] {P : PROP} : <affine> P ⊢ P := by
  simp [bi_affinely, and_elim_r]

instance affinely_mono' [BI PROP] : MonotonicUnary (α := PROP) (· ⊢ ·) (`[iprop| <affine> ·]) where
  monotonicity_unary := by
    intro _ _ H
    rw' [H]

-- Absorbing
theorem absorbingly_intro [BI PROP] {P : PROP} : P ⊢ <absorb> P := by
  exact True_sep_2

instance absorbingly_mono' [BI PROP] : MonotonicUnary (α := PROP) (· ⊢ ·) (`[iprop| <absorb> ·]) where
  monotonicity_unary := by
    intro _ _ H
    simp only [bi_absorbingly]
    rw' [H]

theorem absorbingly_idemp [BI PROP] {P : PROP} : <absorb> <absorb> P ⊣⊢ <absorb> P := by
  apply anti_symm PROP
  case left =>
    simp only [bi_absorbingly]
    rw' [(assoc : True ∗ True ∗ P ⊣⊢ _)]
    apply monotonicity_binary ?_ reflexivity
    apply pure_intro
    simp
  case right =>
    rw' [← absorbingly_intro]

theorem absorbingly_pure {φ : Prop} [BI PROP] : <absorb> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  apply anti_symm PROP
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

theorem absorbingly_wand [BI PROP] {P Q : PROP} : <absorb> (P -∗ Q) ⊢ <absorb> P -∗ <absorb> Q := by
  apply wand_intro_l
  rw' [← absorbingly_sep, wand_elim_r]

theorem absorbingly_sep_l [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ <absorb> (P ∗ Q) := by
  simp only [bi_absorbingly]
  rw' [(assoc : True ∗ P ∗ Q ⊣⊢ _)]

theorem absorbingly_sep_r [BI PROP] {P Q : PROP} : P ∗ <absorb> Q ⊣⊢ <absorb> (P ∗ Q) := by
  simp only [bi_absorbingly]
  rw' [!(assoc : _ ⊣⊢ _ ∗ Q), (comm : P ∗ True ⊣⊢ _)]

-- Affine / Absorbing Propositions
theorem sep_elim_l [BI PROP] {P Q : PROP} [instQP : TCOr (Affine Q) (Absorbing P)] : P ∗ Q ⊢ P := by
  cases instQP
  case l =>
    rw' [affine, (right_id : P ∗ emp ⊣⊢ _)]
  case r =>
    rw' [
      (pure_intro True.intro : Q ⊢ _),
      (comm : P ∗ True ⊣⊢ _),
      absorbing]

-- Persistent
theorem absorbingly_elim_persistently [BI PROP] {P : PROP} : <absorb> <pers> P ⊣⊢ <pers> P := by
  apply anti_symm PROP
  case left =>
    simp only [bi_absorbingly]
    rw' [(comm : `[iprop| True ∗ <pers> P] ⊣⊢ _), persistently_absorbing]
  case right =>
    exact absorbingly_intro

theorem persistently_exist [BI PROP] {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊣⊢ ∃ a, <pers> (Ψ a) := by
  apply anti_symm PROP
  case left =>
    exact persistently_exist_1
  case right =>
    apply exist_elim
    intro a
    rw' [exist_intro a]

theorem persistently_and [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊣⊢ <pers> P ∧ <pers> Q := by
  apply anti_symm PROP
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
  apply anti_symm PROP
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
  apply anti_symm PROP
  case left =>
    exact persistently_emp_intro
  case right =>
    apply monotonicity_unary
    apply pure_intro
    simp

theorem persistently_True [BI PROP] : True ⊢ <pers> (True : PROP) := by
  rw' [persistently_True_emp, persistently_emp_intro]

theorem persistently_and_emp [BI PROP] {P : PROP} : <pers> P ⊣⊢ <pers> (emp ∧ P) := by
  apply anti_symm PROP
  case left =>
    rw' [persistently_and]
    apply and_intro ?_ reflexivity
    exact persistently_emp_intro
  case right =>
    rw' [and_elim_r]

theorem persistently_and_sep_elim_emp [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ (emp ∧ P) ∗ Q := by
  rw' [persistently_and_emp, persistently_and_sep_elim]

theorem persistently_and_sep_assoc [BI PROP] {P Q R : PROP} : <pers> P ∧ (Q ∗ R) ⊣⊢ (<pers> P ∧ Q) ∗ R := by
  apply anti_symm PROP
  case left =>
    rw' [
      persistently_idemp_2,
      persistently_and_sep_elim_emp,
      (assoc : (emp ∧ <pers> P) ∗ Q ∗ R ⊣⊢ _)]
    apply monotonicity_binary ?_ reflexivity
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
  apply anti_symm PROP
  · rw' [persistently_into_absorbingly, absorbingly_elim_persistently]
  · exact persistently_idemp_2

theorem persistently_pure {φ : Prop} [BI PROP] : <pers> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  apply anti_symm PROP
  case left =>
    rw' [persistently_into_absorbingly, absorbingly_pure]
  case right =>
    apply pure_elim'
    intro Hφ
    rw' [persistently_True]
    apply monotonicity_unary
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

theorem and_sep_persistently [BI PROP] {P Q : PROP} : <pers> P ∧ <pers> Q ⊣⊢ <pers> P ∗ <pers> Q := by
  apply anti_symm PROP
  case left =>
    exact persistently_and_sep_l_1
  case right =>
    apply and_intro
    · exact persistently_absorbing
    · rw' [(comm : `[iprop| <pers> P ∗ <pers> Q ⊣⊢ _]), persistently_absorbing]

theorem persistently_sep_2 [BI PROP] {P Q : PROP} : <pers> P ∗ <pers> Q ⊢ <pers> (P ∗ Q) := by
  rw' [← persistently_and_sep, persistently_and, ← and_sep_persistently]

-- Intuitionistic
theorem intuitionistically_affinely [BI PROP] {P : PROP} : □ P ⊢ <affine> P := by
  simp only [bi_intuitionistically]
  apply and_intro
  · exact and_elim_l
  · exact persistently_and_emp_elim

theorem persistently_and_intuitionistically_sep_l [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊣⊢ □ P ∗ Q := by
  simp only [bi_intuitionistically]
  apply anti_symm PROP
  case left =>
    simp only [bi_affinely]
    rw' [
      (comm : emp ∧ <pers> P ⊣⊢ _),
      ← persistently_and_sep_assoc,
      (left_id : emp ∗ Q ⊣⊢ _)]
  case right =>
    apply and_intro
    · rw' [affinely_elim, persistently_absorbing]
    · rw' [affinely_elim_emp, (left_id : emp ∗ Q ⊣⊢ _)]

-- Persistent Propositions
theorem persistent_and_affinely_sep_l [BI PROP] {P Q : PROP} [Persistent P] [Absorbing P] :
  P ∧ Q ⊣⊢ <affine> P ∗ Q
:= by
  apply anti_symm PROP
  <;> rw' [persistent, ← persistently_elim, persistently_and_intuitionistically_sep_l]

end Iris.BI
