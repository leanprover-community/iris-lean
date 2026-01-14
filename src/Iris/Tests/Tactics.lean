/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Oliver Soeser
-/
import Iris.BI
import Iris.ProofMode

namespace Iris.Tests
open Iris.BI

/- This file contains tests with various scenarios for all available tactics. -/

-- start stop
theorem start_stop [BI PROP] (Q : PROP) (H : Q ⊢ Q) : Q ⊢ Q := by
  istart
  iintro _HQ
  have HH: True := by trivial
  istop
  exact H

-- rename
namespace rename

theorem rename [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => H
  iexact H

theorem rename_by_type [BI PROP] (Q : PROP) : □ P ∗ Q ⊢ Q := by
  iintro ⟨_HP, HQ⟩
  irename: Q => H
  iexact H

theorem rename_twice [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => H
  irename H => HQ
  iexact HQ

theorem rename_id [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => HQ
  iexact HQ

end rename

-- clear
namespace clear

theorem intuitionistic [BI PROP] (Q : PROP) : □ P ⊢ Q -∗ Q := by
  iintro □HP
  iintro HQ
  iclear HP
  iexact HQ

theorem spatial [BI PROP] (Q : PROP) : <affine> P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iclear HP
  iexact HQ

end clear

-- intro
namespace intro

theorem spatial [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iexact HQ

theorem intuitionistic [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro □HQ
  iexact HQ

theorem as_intuitionistic [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ Q := by
  iintro □HQ
  iexact HQ

theorem as_intuitionistic_in_spatial [BI PROP] (Q : PROP) : ⊢ <pers> Q → Q := by
  iintro HQ
  iexact HQ

theorem drop [BI PROP] (Q : PROP) : ⊢ P → Q -∗ Q := by
  iintro - HQ
  iexact HQ

theorem drop_after [BI PROP] (Q : PROP) : ⊢ Q -∗ P → Q := by
  iintro HQ -
  iexact HQ

theorem «forall» [BI PROP] : ⊢ ∀ x, ⌜x = 0⌝ → (⌜x = 0⌝ : PROP) := by
  iintro x
  iintro H
  iexact H

theorem pure [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ ⌜φ⌝ -∗ Q -∗ Q := by
  iintro ⌜Hφ⌝ HQ
  iexact HQ

theorem pattern [BI PROP] (Q : PROP) : □ (P1 ∨ P2) ∗ Q ⊢ Q := by
  iintro ⟨□(_HP1 | _HP2), HQ⟩
  <;> iexact HQ

theorem multiple_spatial [BI PROP] (Q : PROP) : ⊢ <affine> P -∗ Q -∗ Q := by
  iintro _HP HQ
  iexact HQ

theorem multiple_intuitionistic [BI PROP] (Q : PROP) : ⊢ □ P -∗ □ Q -∗ Q := by
  iintro □_HP □HQ
  iexact HQ

theorem multiple_patterns [BI PROP] (Q : PROP) : ⊢ □ (P1 ∧ P2) -∗ Q ∨ Q -∗ Q := by
  iintro □⟨_HP1, ∗_HP2⟩ (HQ | HQ)
  <;> iexact HQ

end intro

-- exists
namespace «exists»

theorem id [BI PROP] : ⊢@{PROP} ∃ x, x := by
  iexists iprop(True)
  ipure_intro
  exact True.intro

theorem f [BI PROP] : ⊢@{PROP} ∃ (_x : Nat), True ∨ False := by
  iexists 42
  ileft
  ipure_intro
  exact True.intro

theorem pure [BI PROP] : ⊢@{PROP} ⌜∃ x, x ∨ False⌝ := by
  iexists True
  ipure_intro
  exact Or.inl True.intro


theorem mvar [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
  iexists ?y
  ipure_intro
  rfl

theorem mvar_anon [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
  iexists _
  ipure_intro
  rfl

theorem mvar_two [BI PROP] : ⊢@{PROP} ∃ x y : Nat, ⌜x = y⌝ := by
  iexists _, 1
  ipure_intro
  rfl


end «exists»

-- exact
namespace exact

theorem exact [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iexact HQ

theorem def_eq [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ □ Q := by
  iintro HQ
  iexact HQ

theorem intuitionistic [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro HQ
  iexact HQ

end exact

-- assumption
namespace assumption

theorem exact [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro _HQ
  iassumption

theorem from_assumption [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ □ Q := by
  iintro _HQ
  iassumption

theorem intuitionistic [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro □_HQ
  iassumption

theorem lean [BI PROP] (Q : PROP) (H : ⊢ Q) : <affine> P ⊢ Q := by
  iintro _HP
  iassumption

theorem lean_pure [BI PROP] (Q : PROP) : <affine> ⌜⊢ Q⌝ ⊢ Q := by
  iintro ⌜H⌝
  iassumption

end assumption

-- apply
namespace apply

theorem exact [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iapply HQ

theorem apply [BI PROP] (P Q : PROP) : ⊢ P -∗ (P -∗ Q) -∗ Q := by
  iintro HP H
  iapply H with HP

theorem multiple [BI PROP] (P Q R : PROP) : ⊢ P -∗ Q -∗ (P -∗ Q -∗ R) -∗ R := by
  iintro HP HQ H
  iapply H with HP, HQ

theorem multiple' [BI PROP] (P Q R S : PROP) : ⊢ (P -∗ Q) -∗ P -∗ R -∗ (Q -∗ R -∗ S) -∗ S := by
  iintro HPQ HP HR H
  iapply H with [HPQ, HP], HR
  iapply HPQ with HP

theorem exact_intuitionistic [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro □HQ
  iapply HQ

theorem apply_intuitionistic [BI PROP] (P Q : PROP) : ⊢ □ P -∗ (P -∗ Q) -∗ Q := by
  iintro HP H
  iapply H with HP

theorem multiple_intuitionistic [BI PROP] (P Q R : PROP) : ⊢ □ P -∗ Q -∗ □ (P -∗ Q -∗ □ R) -∗ R := by
  iintro □HP HQ □H
  iapply H with [], [HQ] as Q
  case Q => iexact HQ
  iexact HP

theorem later [BI PROP] (P Q : PROP) : ⊢ (▷ P -∗ Q) -∗ P -∗ Q := by
  iintro H HP
  iapply H with HP

theorem test_affine [BI PROP] [BIAffine PROP] (P Q : PROP) : ⊢ (P → Q) -∗ <pers> P -∗ Q := by
  iintro H HP
  iapply H with HP

theorem later_affine [BI PROP] [BIAffine PROP] (P Q : PROP) : ⊢ (▷ P → Q) -∗ P -∗ Q := by
  iintro H HP
  iapply H with HP

theorem exact_lean [BI PROP] (Q : PROP) (H : ⊢ Q) : ⊢ Q := by
  iapply H

theorem exact_lean' [BI PROP] (Q : PROP) : Q ⊢ (emp ∗ Q) ∗ emp := by
  iapply (wand_intro sep_emp.mpr)
  iemp_intro

theorem exact_lean'' [BI PROP] (Q : PROP) (H : 0 = 0 → ⊢ Q) : ⊢ Q := by
  iapply H
  rfl

theorem exact_lean''' [BI PROP] : ⊢@{PROP} ⌜1 = 1⌝ := by
  istart
  iapply (pure_intro (P:=emp))
  . rfl
  iemp_intro

theorem apply_lean [BI PROP] (P Q : PROP) (H : P ⊢ Q) (HP : ⊢ P) : ⊢ Q := by
  iapply H
  iapply HP

theorem apply_lean' [BI PROP] (P Q : PROP) (H : ⊢ P -∗ Q) (HP : ⊢ P) : ⊢ Q := by
  iapply H with []
  iapply HP

theorem apply_lean'' [BI PROP] (P Q : PROP) (H1 : P ⊢ Q) (H2 : Q ⊢ R) : P ⊢ R := by
  iintro HP
  iapply (wand_intro (emp_sep.mp.trans H2))
  . ipure_intro; trivial
  iapply H1 with HP

theorem multiple_lean [BI PROP] (P Q R : PROP) (H : P ⊢ Q -∗ R) (HP : ⊢ P) : ⊢ Q -∗ R := by
  iintro HQ
  iapply H with [], HQ
  iapply HP

theorem multiple_lean' [BI PROP] (P Q R : PROP) (H : P ∗ Q ⊢ R) (HP : ⊢ P) : ⊢ Q -∗ R := by
  iintro HQ
  iapply (wand_intro H) with [], HQ
  iapply HP

theorem exact_forall [BI PROP] (P : α → PROP) (a : α) (H : ⊢ ∀ x, P x) : ⊢ P a := by
  istart
  iapply H

theorem exact_forall' [BI PROP] (P : α → PROP) (a : α) (H : ∀ x, ⊢ P x) : ⊢ P a := by
  iapply H

theorem apply_forall [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  iapply H $! a, b with HP

theorem apply_forall' [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $! a, b with HP

/-- error: ispecialize: iprop(P a -∗ Q b) is not a forall -/
#guard_msgs in
theorem apply_forall_too_many [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $! a, b, _ with HP

theorem apply_forall2 [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H with HP

theorem apply_forall3 [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $! ?_, ?_ with HP

theorem apply_forall4 [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H
  iapply HP

theorem apply_forall_intuitionistic [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  iapply H $! a with HP

theorem apply_forall_intuitionistic' [BI PROP] (P Q : α → PROP) (a b : α) : (□ ∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $! a, b with HP

theorem apply_two_wands [BI PROP] (P Q : Nat → PROP) :
  (P 1 -∗ P 2 -∗ Q 1) ⊢ □ P 1 -∗ P 2 -∗ Q 1 := by
  iintro H □HP1 HP2
  iapply H
  . iexact HP1
  . iexact HP2

theorem apply_and_l [BI PROP] (P Q : Nat → PROP) :
  ((P 1 -∗ P 2) ∧ (Q 1 -∗ Q 2)) ⊢ P 1 -∗ P 2 := by
  iintro H HP1
  iapply H
  iexact HP1

theorem apply_and_r [BI PROP] (P Q : Nat → PROP) :
  ((P 1 -∗ P 2) ∧ (Q 1 -∗ Q 2)) ⊢ Q 1 -∗ Q 2 := by
  iintro H HQ1
  iapply H
  iexact HQ1

theorem apply_and_l_exact [BI PROP] (P Q : Nat → PROP) :
  (P 1 ∧ Q 1) ⊢ P 1 := by
  iintro H
  iapply H

theorem apply_and_r_exact [BI PROP] (P Q : Nat → PROP) :
  (P 1 ∧ Q 1) ⊢ Q 1 := by
  iintro H
  iapply H

end apply

-- have
namespace ihave

theorem exact_lean [BI PROP] (Q : PROP) (H : ⊢ Q) : ⊢ Q := by
  ihave HQ := H
  iexact HQ

theorem exact_lean_forall [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H
  case x => exact 1
  iapply HQ

theorem exact_lean_forall2 [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H ?res
  case res => exact 1
  iexact HQ

theorem exact_lean_forall3 [BI PROP] (Q : Nat → Nat → PROP) (H : ∀ x y, ⊢ Q x y) : ⊢ Q 1 1 := by
  ihave HQ := H ?res ?res
  case res => exact 1
  iexact HQ

theorem exact_lean_forall4 [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H
  iexact HQ

theorem exact_lean_tc [BI PROP] (Q : Nat → PROP) (H : ∀ (P : PROP) [Persistent P], ⊢ P) : ⊢ Q 1 := by
  ihave HQ := H
  rotate_right 1; exact iprop(□ Q 1)
  . apply inferInstance
  iexact HQ

theorem exact_lean_tc2 [BI PROP] (Q : Nat → PROP) (H : ∀ (P : PROP) [Persistent P], ⊢ P) : ⊢ Q 1 := by
  ihave HQ := H iprop(□ Q _)
  rotate_right 1; exact 1
  iexact HQ

theorem exact_spatial [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro H
  ihave HQ := H
  iexact HQ

theorem apply_lean [BI PROP] (P Q : PROP) (H : P ⊢ Q) : ⊢ P -∗ Q := by
  ihave HPQ := H
  iexact HPQ

theorem apply_forall [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  ihave H' := H $! a, b
  iapply H' with HP

theorem apply_forall_spatial [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  ihave H' := H $! a, b with HP
  iexact H'

theorem apply_forall_intuitionistic [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  ihave H' := H $! a, b
  iapply H' with HP

theorem apply_forall_intuitionistic_iris [BI PROP] (P Q : α → PROP) (a b : α) : (□ ∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  ihave H' := H $! a, b with [HP]
  . iexact HP
  iexact H'

end ihave

-- ex falso
namespace exfalso

theorem false_intro [BI PROP] (Q : PROP) : False ⊢ Q := by
  iintro ⟨⟩

theorem false [BI PROP] (P : PROP) : □ P ⊢ False -∗ Q := by
  iintro _HP HF
  iexfalso
  iexact HF

theorem pure [BI PROP] (P : PROP) (HF : False) : ⊢ P := by
  istart
  iexfalso
  ipure_intro
  exact HF

end exfalso

-- pure
namespace pure

theorem move [BI PROP] (Q : PROP) : <affine> ⌜φ⌝ ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

theorem move_multiple [BI PROP] (Q : PROP) : <affine> ⌜φ1⌝ ⊢ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
  iintro Hφ1
  iintro Hφ2
  iintro HQ
  ipure Hφ1
  ipure Hφ2
  iexact HQ

theorem move_conjunction [BI PROP] (Q : PROP) : (⌜φ1⌝ ∧ <affine> ⌜φ2⌝) ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

end pure

-- intuitionistic
namespace intuitionistic

theorem move [BI PROP] (P : PROP) : □ P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iexact HQ

theorem move_multiple [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iintuitionistic HQ
  iexact HQ

theorem move_twice [BI PROP] (P : PROP) : □ P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iintuitionistic HP
  iexact HQ

end intuitionistic

-- spatial
namespace spatial

theorem move [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro □HP
  iintro □HQ
  ispatial HP
  iexact HQ

theorem move_multiple [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro □HP
  iintro □HQ
  ispatial HP
  ispatial HQ
  iexact HQ

theorem move_twice [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro □HP
  iintro □HQ
  ispatial HP
  ispatial HP
  iexact HQ

end spatial

-- emp intro
namespace empintro

theorem simple [BI PROP] : ⊢ (emp : PROP) := by
  iemp_intro

theorem affine_env [BI PROP] (P : PROP) : <affine> P ⊢ emp := by
  iintro _HP
  iemp_intro

end empintro

-- pure intro
namespace pureintro

theorem simple [BI PROP] : ⊢ (⌜True⌝ : PROP) := by
  ipure_intro
  exact True.intro

theorem or [BI PROP] : ⊢ True ∨ (False : PROP) := by
  ipure_intro
  apply Or.inl True.intro

theorem with_proof [BI PROP] (H : A → B) (P Q : PROP) : <affine> P ⊢ <pers> Q → ⌜A⌝ → ⌜B⌝ := by
  iintro _HP □_HQ
  ipure_intro
  exact H

end pureintro

-- specialize
namespace specialize

theorem wand_spatial [BI PROP] (Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ with HP
  iexact HPQ

theorem wand_spatial_subgoal [BI PROP] (Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ with [HP]
  . iexact HP
  iexact HPQ

theorem wand_spatial_subgoal_named [BI PROP] (Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ with [HP] as G
  case G => iexact HP
  iexact HPQ

theorem wand_intuitionistic [BI PROP] (Q : PROP) : □ P ⊢ □ (P -∗ Q) -∗ □ Q := by
  iintro □HP □HPQ
  ispecialize HPQ with HP
  iexact HPQ

theorem wand_intuitionistic_subgoal [BI PROP] (Q : PROP) : □ P ⊢ □ (P -∗ Q) -∗ Q := by
  iintro □HP □HPQ
  ispecialize HPQ with []
  . iexact HP
  iexact HPQ

theorem wand_intuitionistic_required [BI PROP] (Q : PROP) : □ P ⊢ □ (□ P -∗ Q) -∗ □ Q := by
  iintro □HP □HPQ
  ispecialize HPQ with HP
  iexact HPQ

theorem wand_intuitionistic_spatial [BI PROP] (Q : PROP) : □ P ⊢ (P -∗ Q) -∗ Q := by
  iintro □HP HPQ
  ispecialize HPQ with HP
  iexact HPQ

theorem wand_intuitionistic_required_spatial [BI PROP] (Q : PROP) : □ P ⊢ (□ P -∗ Q) -∗ Q := by
  iintro □HP HPQ
  ispecialize HPQ with HP
  iexact HPQ

theorem wand_spatial_intuitionistic [BI PROP] (Q : PROP) : P ⊢ □ (P -∗ Q) -∗ Q := by
  iintro HP □HPQ
  ispecialize HPQ with HP
  iexact HPQ

theorem wand_spatial_multiple [BI PROP] (Q : PROP) : ⊢ P1 -∗ P2 -∗ (P1 -∗ P2 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HPQ
  ispecialize HPQ with HP1, HP2
  iexact HPQ

theorem wand_spatial_multiple_subgoal [BI PROP] (Q : PROP) : ⊢ P1 -∗ P2 -∗ (P1 -∗ P2 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HPQ
  ispecialize HPQ with [HP1], [HP2]
  . iexact HP1
  . iexact HP2
  iexact HPQ

theorem wand_intuitionistic_multiple [BI PROP] (Q : PROP) :
    ⊢ □ P1 -∗ □ P2 -∗ □ (P1 -∗ □ P2 -∗ Q) -∗ □ Q := by
  iintro □HP1 □HP2 □HPQ
  ispecialize HPQ with HP1, HP2
  iexact HPQ

theorem wand_multiple [BI PROP] (Q : PROP) :
    ⊢ P1 -∗ □ P2 -∗ P3 -∗ □ (P1 -∗ P2 -∗ P3 -∗ Q) -∗ Q := by
  iintro HP1 □HP2 HP3 HPQ
  ispecialize HPQ with HP1, HP2, HP3
  iexact HPQ

theorem forall_spatial [BI PROP] (Q : Nat → PROP) : ⊢ (∀ x, Q x) -∗ Q (y + 1) := by
  iintro HQ
  ispecialize HQ $! (y + 1)
  iexact HQ

theorem forall_intuitionistic [BI PROP] (Q : Nat → PROP) : ⊢ □ (∀ x, Q x) -∗ □ Q y := by
  iintro □HQ
  ispecialize HQ $! y
  iexact HQ

theorem forall_spatial_intuitionistic [BI PROP] (Q : Nat → PROP) : ⊢ (∀ x, □ Q x) -∗ □ Q y := by
  iintro HQ
  ispecialize HQ $! y
  iexact HQ

theorem forall_spatial_multiple [BI PROP] (Q : Nat → Nat → PROP) :
    ⊢ (∀ x, ∀ y, Q x y) -∗ Q x y := by
  iintro HQ
  ispecialize HQ $! x, y
  iexact HQ

theorem forall_intuitionistic_multiple [BI PROP] (Q : Nat → Nat → PROP) :
    ⊢ □ (∀ x, ∀ y, Q x y) -∗ □ Q x y := by
  iintro □HQ
  ispecialize HQ $! x, y
  iexact HQ

theorem forall_multiple [BI PROP] (Q : Nat → Nat → PROP) : ⊢ (∀ x, □ (∀ y, Q x y)) -∗ □ Q x y := by
  iintro HQ
  ispecialize HQ $! x, y
  iexact HQ

theorem multiple [BI PROP] (Q : Nat → PROP) :
    ⊢ □ P1 -∗ P2 -∗ (□ P1 -∗ (∀ x, P2 -∗ Q x)) -∗ Q y := by
  iintro □HP1 HP2 HPQ
  ispecialize HPQ with HP1
  ispecialize HPQ $! y with HP2
  iexact HPQ

end specialize

-- split
namespace split

theorem and [BI PROP] (Q : PROP) : Q ⊢ Q ∧ Q := by
  iintro HQ
  isplit
  <;> iexact HQ

theorem sep_left [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro HQ
  iintro _HR
  isplitl [HP _HR]
  · iexact HP
  · iexact HQ

theorem sep_right [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro HQ
  iintro _HR
  isplitr [HQ]
  · iexact HP
  · iexact HQ

theorem sep_left_all [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ P -∗ □ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro □HQ
  iintro _HR
  isplitl
  · iexact HP
  · iexact HQ

theorem sep_right_all [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ □ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro □HP
  iintro HQ
  iintro _HR
  isplitr
  · iexact HP
  · iexact HQ

end split

-- left / right
namespace leftright

theorem left [BI PROP] (P : PROP) : P ⊢ P ∨ Q := by
  iintro HP
  ileft
  iexact HP

theorem right [BI PROP] (Q : PROP) : Q ⊢ P ∨ Q := by
  iintro HQ
  iright
  iexact HQ

theorem complex [BI PROP] (P Q : PROP) : ⊢ P -∗ Q -∗ P ∗ (R ∨ Q ∨ R) := by
  iintro HP HQ
  isplitl [HP]
  · iassumption
  iright
  ileft
  iexact HQ

end leftright

-- cases
namespace cases

theorem rename [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  icases HP with H
  iexact H

theorem clear [BI PROP] (P Q : PROP) : ⊢ P -∗ <affine> Q -∗ P := by
  iintro HP
  iintro HQ
  icases HQ with -
  iexact HP

theorem and [BI PROP] (Q : PROP) : □ (P1 ∧ P2 ∧ Q) ⊢ Q := by
  iintro □HP
  icases HP with ⟨_HP1, _HP2, HQ⟩
  iexact HQ

theorem and_intuitionistic [BI PROP] (Q : PROP) : □ P ∧ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨_HP, HQ⟩
  iexact HQ

theorem and_persistent_left [BI PROP] (Q : PROP) : <pers> Q ∧ <affine> P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨□HQ, _HP⟩
  iexact HQ

theorem and_persistent_right [BI PROP] (Q : PROP) : Q ∧ <pers> P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, _HP⟩
  iexact HQ

theorem sep [BI PROP] [BIAffine PROP] (Q : PROP) : P1 ∗ P2 ∗ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨_HP1, _HP2, HQ⟩
  iexact HQ

theorem disjunction [BI PROP] (Q : PROP) : Q ⊢ <affine> (P1 ∨ P2 ∨ P3) -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (_HP1 | _HP2 | _HP3)
  <;> iexact HQ

theorem conjunction_and_disjunction [BI PROP] [BIAffine PROP] (Q : PROP) :
    (P11 ∨ P12 ∨ P13) ∗ P2 ∗ (P31 ∨ P32 ∨ P33) ∗ Q ⊢ Q := by
  iintro HP
  icases HP with ⟨_HP11 | _HP12 | _HP13, HP2, HP31 | HP32 | HP33, HQ⟩
  <;> iexact HQ

theorem move_to_pure [BI PROP] (Q : PROP) : ⊢ <affine> ⌜⊢ Q⌝ -∗ Q := by
  iintro HQ
  icases HQ with ⌜HQ⌝
  istop
  exact HQ

theorem move_to_pure_ascii [BI PROP] (Q : PROP) : ⊢ <affine> ⌜⊢ Q⌝ -∗ Q := by
  iintro HQ
  icases HQ with %HQ
  istop
  exact HQ

theorem move_to_intuitionistic [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro HQ
  icases HQ with □HQ
  iexact HQ

theorem move_to_intuitionistic_ascii [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro HQ
  icases HQ with #HQ
  iexact HQ

theorem move_to_spatial [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro □HQ
  icases HQ with ∗HQ
  iexact HQ

theorem move_to_spatial_ascii [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro □HQ
  icases HQ with *HQ
  iexact HQ

theorem move_to_pure_conjunction [BI PROP] (Q : PROP) : ⊢ <affine> ⌜φ⌝ ∗ Q -∗ Q := by
  iintro HφQ
  icases HφQ with ⟨⌜Hφ⌝, HQ⟩
  iexact HQ

theorem move_to_pure_disjunction [BI PROP] (Q : PROP) :
    ⊢ <affine> ⌜φ1⌝ ∨ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  icases Hφ with (⌜Hφ1⌝ | ⌜Hφ2⌝)
  <;> iexact HQ

theorem move_to_intuitionistic_conjunction [BI PROP] (Q : PROP) : ⊢ □ P ∗ Q -∗ Q := by
  iintro HPQ
  icases HPQ with ⟨□_HP, HQ⟩
  iexact HQ

theorem move_to_intuitionistic_disjunction [BI PROP] (Q : PROP) : ⊢ □ Q ∨ Q -∗ Q := by
  iintro HQQ
  icases HQQ with (□HQ | HQ)
  <;> iexact HQ

theorem move_to_spatial_conjunction [BI PROP] (Q : PROP) : ⊢ □ (P ∧ Q) -∗ Q := by
  iintro □HPQ
  icases HPQ with ⟨_HP, ∗HQ⟩
  iexact HQ

theorem move_to_spatial_disjunction [BI PROP] (Q : PROP) : ⊢ □ (Q ∨ Q) -∗ Q := by
  iintro □HPQ
  icases HPQ with (HQ | ∗HQ)
  <;> iexact HQ

theorem move_to_intuitionistic_and_back_conjunction [BI PROP] (Q : PROP) : ⊢ □ (P ∧ Q) -∗ Q := by
  iintro HPQ
  icases HPQ with □⟨_HP, ∗HQ⟩
  iexact HQ

theorem move_to_intuitionistic_and_back_disjunction [BI PROP] (Q : PROP) : ⊢ □ (Q ∨ Q) -∗ Q := by
  iintro HPQ
  icases HPQ with □(HQ | ∗HQ)
  <;> iexact HQ

theorem conjunction_clear [BI PROP] [BIAffine PROP] (Q : PROP) : Q ∗ P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

theorem disjunction_clear [BI PROP] [BIAffine PROP] (Q : PROP) : Q ⊢ P1 ∨ P2 -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (- | _HP2)
  <;> iexact HQ

theorem and_destruct_spatial_right [BI PROP] (Q : PROP) : P ∧ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨-, HQ⟩
  iexact HQ

theorem and_destruct_spatial_left [BI PROP] (Q : PROP) : Q ∧ P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

theorem and_clear_spatial_multiple [BI PROP] (Q : PROP) : P1 ∧ P2 ∧ Q ∧ P3 ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨-, -, HQ, -⟩
  iexact HQ

theorem and_destruct_intuitionistic_right [BI PROP] (Q : PROP) : □ (P ∧ Q) ⊢ Q := by
  iintro □HPQ
  icases HPQ with ⟨-, HQ⟩
  iexact HQ

theorem and_destruct_intuitionistic_left [BI PROP] (Q : PROP) : □ (Q ∧ P) ⊢ Q := by
  iintro □HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

theorem and_clear_intuitionistic_multiple [BI PROP] (Q : PROP) : □ (P1 ∧ P2 ∧ Q ∧ P3) ⊢ Q := by
  iintro □HPQ
  icases HPQ with ⟨-, -, HQ, -⟩
  iexact HQ

theorem «exists» [BI PROP] (Q : Nat → PROP) : (∃ x, Q x) ⊢ ∃ x, Q x ∨ False := by
  iintro ⟨x, H⟩
  iexists x
  ileft
  iexact H

theorem exists_intuitionistic [BI PROP] (Q : Nat → PROP) : □ (∃ x, Q x) ⊢ ∃ x, □ Q x ∨ False := by
  iintro ⟨x, □H⟩
  iexists x
  ileft
  iexact H
