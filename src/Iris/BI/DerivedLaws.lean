import Iris.BI.Classes
import Iris.BI.Interface
import Iris.BI.DerivedConnectives
import Iris.Std.Classes
import Iris.Std.TC

namespace Iris.BI
open Iris.Std
open BI

-- MACROS
macro "trans_rw" rule:term "using" colGt mono:term : tactic => `(
  apply transitivity ?rw ?_ ;
  case rw =>
    apply $mono
    <;> try exact $rule
)

-- Entails
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

-- THEOREMS
-- Logic
theorem or_intro_l' [BI PROP] {P Q R : PROP} : (P ⊢ Q) → P ⊢ Q ∨ R := by
  intro H
  apply transitivity H ?_
  exact or_intro_l

theorem or_intro_r' [BI PROP] {P Q R : PROP} : (P ⊢ R) → P ⊢ Q ∨ R := by
  intro H
  apply transitivity H ?_
  exact or_intro_r

theorem impl_intro_l [BI PROP] {P Q R : PROP} : (Q ∧ P ⊢ R) → P ⊢ Q → R := by
  intro H
  apply impl_intro_r
  apply transitivity ?_ H
  exact equiv_entails_1_1 (comm : P ∧ Q ⊣⊢ _)

theorem impl_elim [BI PROP] {P Q R : PROP} : (P ⊢ Q → R) → (P ⊢ Q) → P ⊢ R := by
  intro H1 H2
  apply transitivity ?_ (impl_elim_l' H1)
  apply and_intro
  · exact reflexivity
  · exact H2

theorem impl_elim_r' [BI PROP] {P Q R : PROP} : (Q ⊢ P → R) → P ∧ Q ⊢ R := by
  intros H
  apply impl_elim (Q := P)
  · apply transitivity and_elim_r ?_
    exact H
  · apply transitivity and_elim_l ?_
    exact reflexivity

theorem impl_elim_r [BI PROP] {P Q : PROP} : P ∧ (P → Q) ⊢ Q := by
  apply impl_elim_r'
  exact reflexivity

theorem False_elim [BI PROP] {P : PROP} : False ⊢ P := by
  apply pure_elim'
  intro H
  exact False.elim H

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

theorem forall_mono [BI PROP] (Φ Ψ : α → PROP) : (∀ a, Φ a ⊢ Ψ a) → (∀ a, Φ a) ⊢ ∀ a, Ψ a := by
  intro H
  apply forall_intro
  intro a
  apply transitivity ?_ (H a)
  exact forall_elim _

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

-- BI
theorem sep_mono_l [BI PROP] {P P' Q : PROP} : (P ⊢ Q) → P ∗ P' ⊢ Q ∗ P' := by
  intro H
  exact sep_mono H reflexivity

theorem sep_mono_r [BI PROP] {P P' Q' : PROP} : (P' ⊢ Q') → P ∗ P' ⊢ P ∗ Q' := by
  intro H
  exact sep_mono reflexivity H

theorem wand_mono [BI PROP] {P P' Q Q' : PROP} : (Q ⊢ P) → (P' ⊢ Q') → (P -∗ P') ⊢ Q -∗ Q' := by
  intro HP HQ
  apply wand_intro_r
  trans_rw HP using sep_mono reflexivity ?_
  apply transitivity ?_ HQ
  apply wand_elim_l'
  exact reflexivity

theorem True_sep_2 [BI PROP] {P : PROP} : P ⊢ True ∗ P := by
  apply transitivity emp_sep_1 ?_
  apply sep_mono ?_ reflexivity
  apply pure_intro
  exact True.intro

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
    <;> apply sep_mono reflexivity ?_
    · exact or_intro_l
    · exact or_intro_r

theorem sep_exist_l [BI PROP] {P : PROP} (Ψ : A → PROP) : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a := by
  apply anti_symm PROP
  case left =>
    apply wand_elim_r'
    apply exist_elim
    intro a
    apply wand_intro_l
    apply transitivity ?_ (exist_intro a)
    exact reflexivity
  case right =>
    apply exist_elim
    intro a
    apply sep_mono reflexivity ?_
    exact exist_intro _

-- Affine
theorem affinely_elim_emp [BI PROP] {P : PROP} : <affine> P ⊢ emp := by
  simp only [bi_affinely]
  exact and_elim_l

theorem affinely_elim [BI PROP] {P : PROP} : <affine> P ⊢ P := by
  simp only [bi_affinely]
  exact and_elim_r

-- Absorbing
theorem absorbingly_intro [BI PROP] {P : PROP} : P ⊢ <absorb> P := by
  exact True_sep_2

theorem absorbingly_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <absorb> P ⊢ <absorb> Q := by
  intro H
  simp only [bi_absorbingly]
  apply sep_mono reflexivity ?_
  exact H

theorem absorbingly_idemp [BI PROP] {P : PROP} : <absorb> <absorb> P ⊣⊢ <absorb> P := by
  apply anti_symm PROP
  case left =>
    repeat rw [bi_absorbingly]
    rw [(assoc : True ∗ True ∗ P ⊣⊢ _)]
    apply sep_mono ?_ reflexivity
    exact pure_intro True.intro
  case right =>
    apply transitivity ?_ absorbingly_intro
    exact reflexivity

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
  simp only [bi_absorbingly]
  exact sep_or_l

theorem absorbingly_and_1 [BI PROP] {P Q : PROP} : <absorb> (P ∧ Q) ⊢ <absorb> P ∧ <absorb> Q := by
  apply and_intro
  <;> apply absorbingly_mono
  · exact and_elim_l
  · exact and_elim_r

theorem absorbingly_forall [BI PROP] (Φ : α → PROP) : <absorb> (∀ a, Φ a) ⊢ ∀ a, <absorb> (Φ a) := by
  apply forall_intro
  intro a
  trans_rw (forall_elim a) using absorbingly_mono
  exact reflexivity

theorem absorbingly_exist [BI PROP] (Φ : α → PROP) : <absorb> (∃ a, Φ a) ⊣⊢ ∃ a, <absorb> (Φ a) := by
  simp only [bi_absorbingly]
  exact sep_exist_l _

theorem absorbingly_sep [BI PROP] {P Q : PROP} : <absorb> (P ∗ Q) ⊣⊢ <absorb> P ∗ <absorb> Q := by
  rw [← absorbingly_idemp]
  simp only [bi_absorbingly]
  rw [(assoc : True ∗ P ∗ Q ⊣⊢ _)]
  rw [(assoc : True ∗ (True ∗ P) ∗ Q ⊣⊢ _)]
  rw [(comm : True ∗ True ∗ P ⊣⊢ _)]
  rw [← (assoc : _ ⊣⊢ ((True ∗ P) ∗ True) ∗ Q)]

theorem absorbingly_wand [BI PROP] {P Q : PROP} : <absorb> (P -∗ Q) ⊢ <absorb> P -∗ <absorb> Q := by
  apply wand_intro_l
  rw [← absorbingly_sep]
  trans_rw wand_elim_r using absorbingly_mono
  exact reflexivity

theorem absorbingly_sep_l [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ <absorb> (P ∗ Q) := by
  simp only [bi_absorbingly]
  rw [(assoc : True ∗ P ∗ Q ⊣⊢ _)]

theorem absorbingly_sep_r [BI PROP] {P Q : PROP} : P ∗ <absorb> Q ⊣⊢ <absorb> (P ∗ Q) := by
  simp only [bi_absorbingly]
  repeat rw [(assoc : _ ⊣⊢ _ ∗ Q)]
  rw [(comm : P ∗ True ⊣⊢ _)]

-- Affine / Absorbing Propositions
theorem sep_elim_l [BI PROP] {P Q : PROP} [instQP : TCOr (Affine Q) (Absorbing P)] : P ∗ Q ⊢ P := by
  cases instQP
  case l instQ =>
    trans_rw instQ.affine using sep_mono reflexivity ?_
    rw [(right_id : P ∗ emp ⊣⊢ _)]
    exact reflexivity
  case r instP =>
    trans_rw pure_intro True.intro using sep_mono reflexivity ?_
    rw [(comm : P ∗ True ⊣⊢ _)]
    exact instP.absorbing

-- Persistent
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
    apply persistently_mono
    exact exist_intro _

theorem persistently_and [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊣⊢ <pers> P ∧ <pers> Q := by
  apply anti_symm PROP
  case left =>
    apply and_intro
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
    apply persistently_mono
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
    apply persistently_mono
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

theorem persistently_elim [BI PROP] {P : PROP} [inst : Absorbing P] : <pers> P ⊢ P := by
  apply transitivity persistently_into_absorbingly ?_
  exact inst.absorbing

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
    rw [(comm : emp ∧ <pers> P ⊣⊢ _)]
    rw [← persistently_and_sep_assoc]
    rw [(left_id : emp ∗ Q ⊣⊢ _)]
    exact reflexivity
  case right =>
    apply and_intro ?left ?right
    case left =>
      trans_rw affinely_elim using sep_mono ?_ reflexivity
      exact persistently_absorbing
    case right =>
      trans_rw affinely_elim_emp using sep_mono ?_ reflexivity
      rw [(left_id : emp ∗ Q ⊣⊢ _)]
      exact reflexivity

-- Persistent Propositions
theorem persistent_and_affinely_sep_l_1 [BI PROP] {P Q : PROP} [inst : Persistent P] : P ∧ Q ⊢ <affine> P ∗ Q := by
  trans_rw inst.persistent using and_mono ?_ reflexivity
  apply transitivity (equiv_entails_1_1 persistently_and_intuitionistically_sep_l) ?_
  trans_rw intuitionistically_affinely using sep_mono ?_ reflexivity
  exact reflexivity

theorem persistent_and_affinely_sep_l [BI PROP] {P Q : PROP} [instPersistent : Persistent P] [Absorbing P] :
  P ∧ Q ⊣⊢ <affine> P ∗ Q
:= by
  have : P ⊣⊢ <pers> P := by
    apply anti_symm PROP
    · exact instPersistent.persistent
    · exact persistently_elim
  rw [this]
  exact persistently_and_intuitionistically_sep_l

end Iris.BI
