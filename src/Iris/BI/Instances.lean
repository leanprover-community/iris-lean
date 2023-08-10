/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Classes
import Iris.BI.DerivedLaws
import Iris.BI.Extensions
import Iris.BI.BI
import Iris.Std.Classes

namespace Iris.BI
open Iris.Std
open BI

-- Persistent
instance pure_persistent (φ : Prop) [BI PROP] :
  Persistent (PROP := PROP) iprop(⌜φ⌝)
where
  persistent := by
    rw' [persistently_pure]

instance emp_persistent [BI PROP] :
  Persistent (PROP := PROP) iprop(emp)
where
  persistent := persistently_emp_intro

instance and_persistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent iprop(P ∧ Q)
where
  persistent := by
    rw' [persistently_and, !← persistent]

instance or_persistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent iprop(P ∨ Q)
where
  persistent := by
    rw' [persistently_or, !← persistent]

instance exists_persistent [BI PROP] (Ψ : α → PROP) :
  [∀ x, Persistent (Ψ x)] →
  Persistent iprop(∃ x, Ψ x)
where
  persistent := by
    rw' [persistently_exists, ← persistent]

instance sep_persistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent iprop(P ∗ Q)
where
  persistent := by
    rw' [← persistently_sep_2, !← persistent]

instance persistently_persistent [BI PROP] (P : PROP) :
  Persistent iprop(<pers> P)
where
  persistent := persistently_idem_2

instance affinely_persistent [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent iprop(<affine> P)
where
  persistent := by
    simp [affinely, persistent]

instance affinelyIf_persistent (p : Bool) [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent iprop(<affine>?p P)
where
  persistent := by
    cases p
    <;> simp [affinelyIf, persistent]

instance intuitionistically_persistent [BI PROP] (P : PROP) :
  Persistent iprop(□ P)
where
  persistent := by
    simp [intuitionistically, persistent]

instance absorbingly_persistent [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent iprop(<absorb> P)
where
  persistent := by
    simp [absorbingly, persistent]

instance absorbinglyIf_persistent (p : Bool) [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent iprop(<absorb>?p P)
where
  persistent := by
    cases p
    <;> simp [absorbinglyIf, persistent]

-- Affine
instance emp_affine [BI PROP] :
  Affine (PROP := PROP) iprop(emp)
where
  affine := by
    simp

instance false_affine [BI PROP] :
  Affine (PROP := PROP) iprop(False)
where
  affine := false_elim

instance and_affine_l [BI PROP] (P Q : PROP) :
  [Affine P] →
  Affine iprop(P ∧ Q)
where
  affine := by
    rw' [affine, and_elim_l]

instance and_affine_r [BI PROP] (P Q : PROP) :
  [Affine Q] →
  Affine iprop(P ∧ Q)
where
  affine := by
    rw' [affine, and_elim_r]

instance or_affine [BI PROP] (P Q : PROP) :
  [Affine P] →
  [Affine Q] →
  Affine iprop(P ∨ Q)
where
  affine := by
    apply or_elim
    <;> exact affine

instance forall_affine [Inhabited α] [BI PROP] (Φ : α → PROP) :
  [∀ x, Affine (Φ x)] →
  Affine iprop(∀ x, Φ x)
where
  affine := by
    rw' [← affine (P := Φ default), forall_elim default]

instance exists_affine [BI PROP] (Φ : α → PROP) :
  [∀ x, Affine (Φ x)] →
  Affine iprop(∃ x, Φ x)
where
  affine := by
    apply exists_elim
    intro a
    exact affine

instance sep_affine [BI PROP] (P Q : PROP) :
  [Affine P] →
  [Affine Q] →
  Affine iprop(P ∗ Q)
where
  affine := by
    rw' [
      affine,
      (left_id : emp ∗ Q ⊣⊢ _),
      affine]

instance affinely_affine [BI PROP] (P : PROP) :
  Affine iprop(<affine> P)
where
  affine := by
    simp [affinely, affine]

instance affinelyIf_affine (p : Bool) [BI PROP] (P : PROP) :
  [Affine P] →
  Affine iprop(<affine>?p P)
where
  affine := by
    cases p
    <;> simp [affinelyIf, affine]

instance intuitionistically_affine [BI PROP] (P : PROP) :
  Affine iprop(□ P)
where
  affine := by
    simp [intuitionistically, affine]

instance intuitionisticallyIf_affine (p : Bool) [BI PROP] (P : PROP) :
  [Affine P] →
  Affine iprop(□?p P)
where
  affine := by
    cases p
    <;> simp [intuitionisticallyIf, affine]

-- Absorbing
instance pure_absorbing (φ : Prop) [BI PROP] :
  Absorbing (PROP := PROP) iprop(⌜φ⌝)
where
  absorbing := by
    rw' [absorbingly_pure]

instance and_absorbing [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing iprop(P ∧ Q)
where
  absorbing := by
    rw' [absorbingly_and_1, !absorbing]

instance or_absorbing [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing iprop(P ∨ Q)
where
  absorbing := by
    rw' [absorbingly_or, !absorbing]

instance forall_absorbing [BI PROP] (Φ : α → PROP) :
  [∀ x, Absorbing (Φ x)] →
  Absorbing iprop(∀ x, Φ x)
where
  absorbing := by
    rw' [absorbingly_forall Φ, absorbing]

instance exists_absorbing [BI PROP] (Φ : α → PROP) :
  [∀ x, Absorbing (Φ x)] →
  Absorbing iprop(∃ x, Φ x)
where
  absorbing := by
    rw' [absorbingly_exists Φ, absorbing]

instance imp_absorbing [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing iprop(P → Q)
where
  absorbing := by
    apply imp_intro'
    rw' [
      persistent_and_affinely_sep_l,
      absorbingly_sep_r,
      ← persistent_and_affinely_sep_l,
      imp_elim_r,
      absorbing]

instance sep_absorbing_l [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  Absorbing iprop(P ∗ Q)
where
  absorbing := by
    rw' [← absorbingly_sep_l, absorbing]

instance sep_absorbing_r [BI PROP] (P Q : PROP) :
  [Absorbing Q] →
  Absorbing iprop(P ∗ Q)
where
  absorbing := by
    rw' [← absorbingly_sep_r, absorbing]

instance wand_absorbing_l [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  Absorbing iprop(P -∗ Q)
where
  absorbing := by
    simp only [absorbingly]
    apply wand_intro'
    rw' [
      (assoc : P ∗ True ∗ (P -∗ Q) ⊣⊢ _),
      (sep_elim_l : P ∗ True ⊢ _),
      wand_elim_r]

instance wand_absorbing_r [BI PROP] (P Q : PROP) :
  [Absorbing Q] →
  Absorbing iprop(P -∗ Q)
where
  absorbing := by
    rw' [absorbingly_wand, (absorbing : _ ⊢ Q), (absorbingly_intro : _ ⊢ <absorb> P)]

instance absorbingly_absorbing [BI PROP] (P : PROP) :
  Absorbing iprop(<absorb> P)
where
  absorbing := by
    rw' [absorbingly_idem]

instance persistently_absorbing [BI PROP] (P : PROP) :
  Absorbing iprop(<pers> P)
where
  absorbing := by
    rw' [absorbingly_persistently]

instance persistentlyIf_absorbing [BI PROP] (P : PROP) (p : Bool) :
  [Absorbing P] →
  Absorbing iprop(<pers>?p P)
where
  absorbing := by
    cases p
    <;> simp [persistentlyIf, absorbing]

section Affine

instance (priority := default + 10) biAffine_absorbing [BIAffine PROP] (P : PROP) :
  Absorbing P
where
  absorbing := by
    simp only [absorbingly]
    rw' [
      (affine : (True : PROP) ⊢ _),
      (left_id : emp ∗ P ⊣⊢ _)]

end Affine
end Iris.BI
