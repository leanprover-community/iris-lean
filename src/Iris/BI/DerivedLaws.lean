import Iris.BI.Interface
import Iris.BI.DerivedConnectives
import Iris.Std.Classes

namespace Iris.BI
open Iris.Std
open BI

-- # Macros
syntax "trans_rw" term "using" colGt term : tactic
macro_rules
  | `(tactic| trans_rw $rule using $mono) => `(tactic|
      apply transitivity (by
        apply $mono
        <;> try exact $rule
      ) ?_
    )

-- # Entails
instance entails_anti_symm [BI PROP] : AntiSymm (α := PROP) (· ⊣⊢ ·) (· ⊢ ·) where
  anti_symm := by
    intro _ _ H1 H2
    rw [equiv_entails]
    exact And.intro H1 H2

scoped macro "anti_symm" colGt PROP:term : term => `(anti_symm (α := $PROP) (R := (· ⊣⊢ ·)) (S := (· ⊢ ·)) ?left ?right)

theorem equiv_entails_1_1 [BI PROP] {P Q : PROP} : (P ⊣⊢ Q) → (P ⊢ Q) := by
  intro h
  exact equiv_entails.mp h |>.left

theorem equiv_entails_1_2 [BI PROP] {P Q : PROP} : (P ⊣⊢ Q) → (Q ⊢ P) := by
  intro h
  exact equiv_entails.mp h |>.right

theorem equiv_entails_2 [BI PROP] {P Q : PROP} : (P ⊢ Q) → (Q ⊢ P) → (P ⊣⊢ Q) := by
  intro h1 h2
  apply equiv_entails.mpr
  exact And.intro h1 h2

-- # Instances
-- ## And
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
      exact True.intro

instance and_True [BI PROP] : RightId (α := PROP) (· ⊣⊢ ·) `[iprop| True] (`[iprop| · ∧ ·]) where
  right_id := by
    intros
    apply anti_symm PROP
    case left =>
      exact and_elim_l
    case right =>
      apply and_intro reflexivity ?_
      apply pure_intro
      exact True.intro

-- ## Sep
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
      rw [(comm : P ∗ (Q ∗ R) ⊣⊢ _)]
      rw [(comm : P ∗ Q ⊣⊢ _)]
      rw [(comm : Q ∗ R ⊣⊢ _)]
      rw [(comm : (Q ∗ P) ∗ R ⊣⊢ _)]
      exact sep_assoc'
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
    rw [(comm : `[iprop| x ∗ emp] ⊣⊢ _)]
    exact left_id

-- # Theorems
-- ## Logic
theorem or_intro_l' [BI PROP] {P Q R : PROP} : (P ⊢ Q) → P ⊢ Q ∨ R := by
  intro H
  apply transitivity H ?_
  exact or_intro_l

theorem or_intro_r' [BI PROP] {P Q R : PROP} : (P ⊢ R) → P ⊢ Q ∨ R := by
  intro H
  apply transitivity H ?_
  exact or_intro_r

theorem and_mono [BI PROP] {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∧ P' ⊢ Q ∧ Q' := by
  intro H1 H2
  apply and_intro
  · apply transitivity ?_ H1
    exact and_elim_l
  · apply transitivity ?_ H2
    exact and_elim_r

theorem or_mono [BI PROP] {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∨ P' ⊢ Q ∨ Q' := by
  intro H1 H2
  apply or_elim
  · exact or_intro_l' H1
  · exact or_intro_r' H2

theorem exist_mono [BI PROP] {Φ Ψ : α → PROP} : (∀ a, Φ a ⊢ Ψ a) → (∃ a, Φ a) ⊢ ∃ a, Ψ a := by
  intro Hφ
  apply exist_elim
  intro a
  apply transitivity (Hφ a) ?_
  exact exist_intro _

theorem or_alt [BI PROP] {P Q : PROP} : P ∨ Q ⊣⊢ ∃ (b : Bool), if b then P else Q := by
  apply anti_symm PROP
  case left =>
    apply or_elim ?left ?right
    case left =>
      apply transitivity ?_ (exist_intro true)
      simp only [ite_true]
      exact reflexivity
    case right =>
      apply transitivity ?_ (exist_intro false)
      simp only [ite_false]
      exact reflexivity
  case right =>
    apply exist_elim
    intro b
    cases b
    · simp only [ite_false]
      exact or_intro_r
    · simp only [ite_true]
      exact or_intro_l

-- ## Sep
theorem sep_mono_l [BI PROP] {P P' Q : PROP} : (P ⊢ Q) → P ∗ P' ⊢ Q ∗ P' := by
  intro H
  exact sep_mono H reflexivity

theorem sep_mono_r [BI PROP] {P P' Q' : PROP} : (P' ⊢ Q') → P ∗ P' ⊢ P ∗ Q' := by
  intro H
  exact sep_mono reflexivity H

theorem True_sep_2 [BI PROP] {P : PROP} : P ⊢ True ∗ P := by
  apply transitivity emp_sep_1 ?_
  apply sep_mono ?_ reflexivity
  apply pure_intro
  exact True.intro

-- ## Wand
theorem wand_intro_l [BI PROP] {P Q R : PROP} : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R := by
  rw [(comm : Q ∗ P ⊣⊢ _)]
  exact wand_intro_r

theorem wand_elim_l [BI PROP] {P Q : PROP} : (P -∗ Q) ∗ P ⊢ Q := by
  apply wand_elim_l'
  exact reflexivity

theorem wand_elim_r [BI PROP] {P Q : PROP} : P ∗ (P -∗ Q) ⊢ Q := by
  apply transitivity sep_comm' ?_
  exact wand_elim_l

theorem wand_elim_r' [BI PROP] {P Q R : PROP} : (Q ⊢ P -∗ R) → P ∗ Q ⊢ R := by
  intro H
  trans_rw H using sep_mono_r
  exact wand_elim_r

-- ## Absorbing
theorem absorbingly_intro [BI PROP] {P : PROP} : P ⊢ <absorb> P := by
  exact True_sep_2

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

-- ## Persistent
theorem absorbingly_elim_persistently [BI PROP] {P : PROP} : <absorb> <pers> P ⊣⊢ <pers> P := by
  apply anti_symm PROP
  case left =>
    simp only [bi_absorbingly]
    rw [(comm : `[iprop| True ∗ <pers> P] ⊣⊢ _)]
    exact persistently_absorbing
  case right =>
    exact absorbingly_intro

theorem persistently_exist [BI PROP] {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊣⊢ ∃ a, <pers> (Ψ a) := by
  apply anti_symm PROP
  case left =>
    exact persistently_exist_1
  case right =>
    apply exist_elim
    intros
    apply persistently_mono ?_
    exact exist_intro _

theorem persistently_and [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊣⊢ <pers> P ∧ <pers> Q := by
  apply anti_symm PROP
  case left =>
    apply and_intro ?_ ?_
    <;> apply persistently_mono
    · exact and_elim_l
    · exact and_elim_r
  case right =>
    exact persistently_and_2

theorem persistently_if {p : Bool} [BI PROP] {P Q : PROP} :
  (<pers> if p then P else Q) ⊣⊢ if p then <pers> P else <pers> Q
:= by
  cases p
  · simp only [ite_false]
  · simp only [ite_true]

theorem persistently_or [BI PROP] {P Q : PROP} : <pers> (P ∨ Q) ⊣⊢ <pers> P ∨ <pers> Q := by
  repeat rw [or_alt]
  rw [persistently_exist]
  apply anti_symm PROP
  <;> apply exist_elim
  <;> intro a
  <;> apply transitivity ?_ (exist_intro a)
  · exact equiv_entails_1_1 persistently_if
  · exact equiv_entails_1_2 persistently_if

theorem persistently_emp_intro [BI PROP] {P : PROP} : P ⊢ <pers> emp := by
  apply transitivity ?_ (persistently_absorbing (Q := P))
  conv =>
    lhs
    rw [← (left_id : emp ∗ P ⊣⊢ _)]
  apply sep_mono ?_ reflexivity
  exact persistently_emp_2

theorem persistently_True_emp [BI PROP] : <pers> True ⊣⊢ <pers> (emp : PROP) := by
  apply anti_symm PROP
  case left =>
    exact persistently_emp_intro
  case right =>
    apply persistently_mono ?_
    apply pure_intro
    exact True.intro

theorem persistently_True [BI PROP] : True ⊢ <pers> (True : PROP) := by
  rw [persistently_True_emp]
  exact persistently_emp_intro

theorem persistently_and_emp [BI PROP] {P : PROP} : <pers> P ⊣⊢ <pers> (emp ∧ P) := by
  apply anti_symm PROP
  case left =>
    rw [persistently_and]
    apply and_intro ?_ reflexivity
    exact persistently_emp_intro
  case right =>
    apply persistently_mono ?_
    exact and_elim_r

theorem persistently_and_sep_elim_emp [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ (emp ∧ P) ∗ Q := by
  rw [persistently_and_emp]
  exact persistently_and_sep_elim

theorem persistently_and_sep_assoc [BI PROP] {P Q R : PROP} : <pers> P ∧ (Q ∗ R) ⊣⊢ (<pers> P ∧ Q) ∗ R := by
  apply anti_symm PROP
  case left =>
    trans_rw persistently_idemp_2 using and_mono ?_ reflexivity
    apply transitivity persistently_and_sep_elim_emp ?_
    rw [(assoc : (emp ∧ <pers> P) ∗ Q ∗ R ⊣⊢ _)]
    apply sep_mono_l
    apply and_intro ?left ?right
    case left =>
      trans_rw and_elim_r using sep_mono ?_ reflexivity
      exact persistently_absorbing
    case right =>
      trans_rw and_elim_l using sep_mono ?_ reflexivity
      exact equiv_entails_1_1 (left_id : emp ∗ Q ⊣⊢ _)
  case right =>
    apply and_intro ?left ?right
    case left =>
      trans_rw and_elim_l using sep_mono ?_ reflexivity
      exact persistently_absorbing
    case right =>
      apply sep_mono ?_ reflexivity
      exact and_elim_r

theorem persistently_and_emp_elim [BI PROP] {P : PROP} : emp ∧ <pers> P ⊢ P := by
  rw [(comm : emp ∧ <pers> P ⊣⊢ _)]
  apply transitivity persistently_and_sep_elim_emp ?_
  rw [(right_id : (emp ∧ P) ∗ emp ⊣⊢ _)]
  exact and_elim_r

theorem persistently_into_absorbingly [BI PROP] {P : PROP} : <pers> P ⊢ <absorb> P := by
  rw [← (right_id : <pers> P ∧ True ⊣⊢ _)]
  rw [← (left_id (α := PROP) : emp ∗ True ⊣⊢ _)]
  rw [persistently_and_sep_assoc]
  rw [(comm : `[iprop| <pers> P ∧ emp] ⊣⊢ _)]
  trans_rw persistently_and_emp_elim using sep_mono ?_ reflexivity
  rw [(comm : `[iprop| P ∗ True] ⊣⊢ _)]
  exact reflexivity

theorem persistently_idemp_1 [BI PROP] {P : PROP} : <pers> <pers> P ⊢ <pers> P := by
  apply transitivity persistently_into_absorbingly ?_
  apply equiv_entails_1_1
  exact absorbingly_elim_persistently

theorem persistently_idemp [BI PROP] {P : PROP} : <pers> <pers> P ⊣⊢ <pers> P := by
  apply anti_symm PROP
  · exact persistently_idemp_1
  · exact persistently_idemp_2

theorem persistently_pure {φ : Prop} [BI PROP] : <pers> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  apply anti_symm PROP
  case left =>
    apply transitivity persistently_into_absorbingly ?_
    apply equiv_entails_1_1
    exact absorbingly_pure
  case right =>
    apply pure_elim'
    intro Hφ
    apply transitivity persistently_True ?_
    apply persistently_mono
    apply pure_intro
    exact Hφ

theorem persistently_and_sep_l_1 [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ <pers> P ∗ Q := by
  conv =>
    lhs
    rw [← (left_id : `[iprop| emp ∗ Q] ⊣⊢ _)]
  rw [persistently_and_sep_assoc]
  apply sep_mono ?_ reflexivity
  exact and_elim_l

theorem persistently_and_sep [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊢ <pers> (P ∗ Q) := by
  rw [persistently_and]
  rw [← persistently_idemp]
  rw [← persistently_and]
  conv =>
    lhs
    rw [← (left_id : emp ∗ Q ⊣⊢ _)]
  rw [persistently_and_sep_assoc]
  rw [(comm : <pers> P ∧ emp ⊣⊢ _)]
  apply persistently_mono
  apply sep_mono ?_ reflexivity
  exact persistently_and_emp_elim

theorem and_sep_persistently [BI PROP] {P Q : PROP} : <pers> P ∧ <pers> Q ⊣⊢ <pers> P ∗ <pers> Q := by
  apply anti_symm PROP
  case left =>
    exact persistently_and_sep_l_1
  case right =>
    apply and_intro
    · exact persistently_absorbing
    · rw [(comm : `[iprop| <pers> P ∗ <pers> Q ⊣⊢ _])]
      exact persistently_absorbing

theorem persistently_sep_2 [BI PROP] {P Q : PROP} : <pers> P ∗ <pers> Q ⊢ <pers> (P ∗ Q) := by
  apply transitivity ?_ persistently_and_sep
  rw [persistently_and]
  rw [← and_sep_persistently]
  exact reflexivity

end Iris.BI
