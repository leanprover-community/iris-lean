/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI.Classes
import Iris.BI.BI
import Iris.BI.DerivedLaws
import Iris.Algebra

class Plainly (PROP : Type _) where
  plainly : PROP → PROP
export Plainly(plainly)

syntax "■ " term:40 : term

macro_rules
  | `(iprop(■ $P))  => ``(Plainly.plainly iprop($P))

delab_rule Plainly.plainly
  | `($_ $P) => do ``(iprop(■  $(← Iris.BI.unpackIprop P)))

def Plainly.plainlyIf [Iris.BI.BIBase PROP] [Plainly PROP] (p : Bool) (P : PROP) : PROP :=
  iprop(if p then ■ P else P)

syntax:max "■?" term:max ppHardSpace term:40 : term

macro_rules
  | `(iprop(■? $p $P))  => ``(Plainly.plainlyIf $p iprop($P))

delab_rule Plainly.plainlyIf
  | `($_ $p $P) => do ``(iprop(■? $p $(← Iris.BI.unpackIprop P)))

namespace Iris.BI
open Iris.Std BI

-- FIXME: These names are inconsistent
class BiPlainly (PROP : Type _) [BI PROP] extends Plainly PROP where
  [ne : OFE.NonExpansive (Plainly.plainly (PROP := PROP))]
  mono {P Q : PROP} : iprop(P ⊢ Q) → iprop(■ P ⊢ ■ Q)
  elim_persistently {P : PROP} : iprop(■ P ⊢ <pers> P)
  idemp {P : PROP} : iprop(■ P ⊢ ■ ■ P)
  plainly_forall {A : Type _} (Ψ : A → PROP) : iprop(∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a)
  plainly_impl_plainly {P Q : PROP} : iprop((■ P → ■ Q) ⊢ ■ (■ P → Q))
  emp_intro {P : PROP} : iprop(P ⊢ ■ emp)
  plainly_absorb {P Q : PROP} : iprop(■ P ∗ Q ⊢ ■ P)
  later_plainly_1 (P : PROP) : iprop(▷ ■ P ⊢ ■ ▷ P)
  later_plainly_2 (P : PROP) : iprop(■ ▷ P ⊢ ▷ ■ P)

class BiPersistentlyImplPlainly (PROP : Type _) [BI PROP] [BiPlainly PROP] where
  pers_impl_plainly (P Q : PROP) : iprop((■ P → <pers> Q) ⊢ <pers> (■ P → Q))

class BiPlainlyExist (PROP : Type _) [BI PROP] [BiPlainly PROP] where
  plainly_exist_1 A (Ψ : A → PROP) : iprop(■ (∃ a, Ψ a) ⊢ ∃ a, ■ (Ψ a))

-- Internal Eq's

class Plain {PROP: Type _}  [BI PROP] [Plainly PROP] [BiPlainly PROP] (P : PROP) where
  plain : P ⊢ ■ P


section PlainlyLaws
open BiPlainly

variable {PROP : Type _} [BI PROP] [BiPlainly PROP]
variable {P Q R : PROP}

theorem affinely_plainly_elim : <affine> ■ P ⊢ P :=
  (affinely_mono elim_persistently).trans persistently_and_emp_elim

theorem persistently_elim_plainly : <pers> ■ P ⊣⊢ ■ P :=
  ⟨absorbingly_of_persistently.trans <| sep_symm.trans plainly_absorb,
   idemp.trans elim_persistently⟩

theorem plainly_persistently_elim : ■ <pers> P ⊣⊢ ■ P :=
  ⟨by
    apply Entails.trans true_and.2
    apply Entails.trans
    · apply and_mono
      · apply emp_intro
      · apply BIBase.Entails.rfl
    apply flip Entails.trans
    · apply mono
      apply persistently_and_emp_elim
    apply Entails.trans and_forall_bool.1
    apply flip Entails.trans
    · apply mono
      apply and_forall_bool.2
    -- apply Entails.trans
    -- · apply forall_mono
    --   intro a
    --   exact BIBase.Entails.rfl
    apply flip Entails.trans
    · rename_i I1 I2
      -- Universe issue? I guess we neeed sForall
      have H := @plainly_forall PROP I1 I2
      sorry
    all_goals sorry,
   idemp.trans <| mono elim_persistently⟩

theorem absorbingly_elim_plainly : <absorb> ■ P ⊣⊢ ■ P :=
  ⟨by
    apply Entails.trans (absorbingly_mono <| persistently_elim_plainly.2)
    apply (flip Entails.trans persistently_elim_plainly.1)
    apply Entails.trans absorbingly_persistently.1
    apply BIBase.Entails.rfl,
   by
    apply flip Entails.trans (absorbingly_mono <| persistently_elim_plainly.1)
    apply (Entails.trans persistently_elim_plainly.2)
    apply flip Entails.trans absorbingly_persistently.2
    apply BIBase.Entails.rfl⟩

theorem plainly_and_sep_elim : ■ P ∧ Q ⊢ (emp ∧ P) ∗ Q := by
  apply Entails.trans
  · apply and_mono
    · apply elim_persistently
    · apply BIBase.Entails.rfl
  apply persistently_and_sep_elim_emp

theorem plainly_and_sep_assoc : ■ P ∧ (Q ∗ R) ⊣⊢ (■ P ∧ Q) ∗ R :=
  ⟨ by
    apply Entails.trans (and_mono persistently_elim_plainly.2 BIBase.Entails.rfl)
    apply (flip Entails.trans)
    · apply sep_mono (and_mono persistently_elim_plainly.1 BIBase.Entails.rfl) BIBase.Entails.rfl
    apply persistently_and_sep_assoc.1,
    by
      apply flip Entails.trans (and_mono persistently_elim_plainly.1 BIBase.Entails.rfl)
      apply Entails.trans
      · apply sep_mono (and_mono persistently_elim_plainly.2 BIBase.Entails.rfl) BIBase.Entails.rfl
      apply persistently_and_sep_assoc.2 ⟩

theorem plainly_and_emp_elim : emp ∧ ■ P ⊢ P := by
  apply Entails.trans (and_mono BIBase.Entails.rfl elim_persistently)
  apply persistently_and_emp_elim

theorem plainly_into_absorbingly : ■ P ⊢ <absorb> P :=
  elim_persistently.trans absorbingly_of_persistently

theorem plainly_elim [ Absorbing P ] : ■ P ⊢ P :=
  elim_persistently.trans persistently_elim

theorem plainly_idemp : ■ ■ P ⊣⊢ ■ P :=
  ⟨plainly_into_absorbingly.trans absorbingly_elim_plainly.1, idemp⟩

theorem plainly_intro' (H : ■ P ⊢ Q) : ■ P ⊢ ■ Q :=
  plainly_idemp.2.trans <| mono <| H

-- theorem plainly_pure φ : ■ ⌜φ⌝ ⊣⊢@{PROP} ⌜φ⌝.
-- theorem plainly_forall {A} (Ψ : A → PROP) : ■ (∀ a, Ψ a) ⊣⊢ ∀ a, ■ (Ψ a).
-- theorem plainly_exist_2 {A} (Ψ : A → PROP) : (∃ a, ■ (Ψ a)) ⊢ ■ (∃ a, Ψ a).
-- theorem plainly_exist `{!BiPlainlyExist PROP} {A} (Ψ : A → PROP) : ■ (∃ a, Ψ a) ⊣⊢ ∃ a, ■ (Ψ a).

theorem plainly_and : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q :=
  ⟨ by sorry, sorry ⟩
theorem plainly_or_2 : ■ P ∨ ■ Q ⊢ ■ (P ∨ Q) := sorry
-- theorem plainly_or `{!BiPlainlyExist PROP} P Q : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q.
theorem plainly_impl : ■ (P → Q) ⊢ ■ P → ■ Q := sorry
-- theorem plainly_emp_2 : emp ⊢@{PROP} ■ emp.
theorem plainly_sep_dup : ■ P ⊣⊢ ■ P ∗ ■ P :=
  ⟨ by
      apply Entails.trans and_self.2
      apply Entails.trans <| and_mono BIBase.Entails.rfl emp_sep.2
      apply Entails.trans <| plainly_and_sep_assoc.1
      apply Entails.trans <| sep_mono and_elim_l BIBase.Entails.rfl
      apply BIBase.Entails.rfl,
    by exact plainly_absorb ⟩

theorem plainly_and_sep_l_1 : ■ P ∧ Q ⊢ ■ P ∗ Q := by
  apply Entails.trans <| and_mono BIBase.Entails.rfl emp_sep.2
  apply Entails.trans <| plainly_and_sep_assoc.1
  apply Entails.trans <| sep_mono and_elim_l BIBase.Entails.rfl
  apply BIBase.Entails.rfl

theorem plainly_and_sep_r_1 : P ∧ ■ Q ⊢ P ∗ ■ Q :=
  and_comm.1.trans <| plainly_and_sep_l_1.trans sep_symm

-- theorem plainly_True_emp : ■ True ⊣⊢@{PROP} ■ emp.

theorem plainly_and_sep : ■ (P ∧ Q) ⊢ ■ (P ∗ Q) := sorry
theorem plainly_affinely_elim : ■ <affine> P ⊣⊢ ■ P := sorry
theorem intuitionistically_plainly_elim : □ ■ P ⊢ □ P := sorry
theorem intuitionistically_plainly : □ ■ P ⊢ ■ □ P := sorry
theorem and_sep_plainly : ■ P ∧ ■ Q ⊣⊢ ■ P ∗ ■ Q := sorry
theorem plainly_sep_2 : ■ P ∗ ■ Q ⊢ ■ (P ∗ Q) := sorry
-- theorem plainly_sep `{!BiPositive PROP} P Q : ■ (P ∗ Q) ⊣⊢ ■ P ∗ ■ Q.
theorem plainly_wand : ■ (P -∗ Q) ⊢ ■ P -∗ ■ Q := sorry
theorem plainly_entails_l : (P ⊢ ■ Q) → P ⊢ ■ Q ∗ P := sorry
theorem plainly_entails_r : (P ⊢ ■ Q) → P ⊢ P ∗ ■ Q := sorry
theorem plainly_impl_wand_2 : ■ (P -∗ Q) ⊢ ■ (P → Q) := sorry
theorem impl_wand_plainly_2 : (■ P -∗ Q) ⊢ (■ P → Q) := sorry
theorem impl_wand_affinely_plainly : (■ P → Q) ⊣⊢ (<affine> ■ P -∗ Q) := sorry
-- theorem persistently_wand_affinely_plainly `{!BiPersistentlyImplPlainly PROP} P Q : (<affine> ■ P -∗ <pers> Q) ⊢ <pers> (<affine> ■ P -∗ Q).
theorem plainly_wand_affinely_plainly : (<affine> ■ P -∗ ■ Q) ⊢ ■ (<affine> ■ P -∗ Q) := sorry


section AffineBI

variable [BIAffine PROP]

--  theorem plainly_emp : ■ emp ⊣⊢@{PROP} emp.
theorem plainly_and_sep_l : ■ P ∧ Q ⊣⊢ ■ P ∗ Q := sorry
theorem plainly_and_sep_r : P ∧ ■ Q ⊣⊢ P ∗ ■ Q := sorry
theorem plainly_impl_wand : ■ (P → Q) ⊣⊢ ■ (P -∗ Q) := sorry
theorem impl_wand_plainly : (■ P → Q) ⊣⊢ (■ P -∗ Q) := sorry

end AffineBI

end PlainlyLaws

end Iris.BI
