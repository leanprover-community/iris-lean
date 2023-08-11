/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
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
instance pure_persistent (φ : Prop) [BI PROP] : Persistent (PROP := PROP) iprop(⌜φ⌝) where
  persistent := persistently_pure.2

instance emp_persistent [BI PROP] : Persistent (PROP := PROP) iprop(emp) where
  persistent := persistently_emp_intro

instance and_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∧ Q) where
  persistent := (and_mono persistent persistent).trans persistently_and.2

instance or_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∨ Q) where
  persistent := (or_mono persistent persistent).trans persistently_or.2

instance exists_persistent [BI PROP] (Ψ : α → PROP) [∀ x, Persistent (Ψ x)] :
    Persistent iprop(∃ x, Ψ x) where
  persistent := (exists_mono fun _ => persistent).trans persistently_exists.2

instance sep_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∗ Q) where
  persistent := (sep_mono persistent persistent).trans persistently_sep_2

instance persistently_persistent [BI PROP] (P : PROP) : Persistent iprop(<pers> P) where
  persistent := persistently_idem_2

instance affinely_persistent [BI PROP] (P : PROP) [Persistent P] : Persistent iprop(<affine> P) :=
  inferInstanceAs (Persistent iprop(_ ∧ _))

instance affinelyIf_persistent (p : Bool) [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<affine>?p P) := by
  cases p <;> simp [affinelyIf] <;> infer_instance

instance intuitionistically_persistent [BI PROP] (P : PROP) : Persistent iprop(□ P) :=
  inferInstanceAs (Persistent iprop(<affine> _))

instance absorbingly_persistent [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<absorb> P) :=
  inferInstanceAs (Persistent iprop(_ ∗ _))

instance absorbinglyIf_persistent (p : Bool) [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<absorb>?p P) := by
  cases p <;> simp [absorbinglyIf] <;> infer_instance

-- Affine
instance emp_affine [BI PROP] : Affine (PROP := PROP) iprop(emp) where
  affine := .rfl

theorem affine_mono [BI PROP] (h : (P : PROP) ⊢ Q) [Affine Q] : Affine P where
  affine := h.trans affine

instance false_affine [BI PROP] : Affine (PROP := PROP) iprop(False) where
  affine := false_elim

instance and_affine_l [BI PROP] (P Q : PROP) [Affine P] : Affine iprop(P ∧ Q) where
  affine := and_elim_l.trans affine

instance and_affine_r [BI PROP] (P Q : PROP) [Affine Q] : Affine iprop(P ∧ Q) where
  affine := and_elim_r.trans affine

instance or_affine [BI PROP] (P Q : PROP) [Affine P] [Affine Q] : Affine iprop(P ∨ Q) where
  affine := or_elim affine affine

instance forall_affine [Inhabited α] [BI PROP] (Φ : α → PROP) [∀ x, Affine (Φ x)] :
    Affine iprop(∀ x, Φ x) where
  affine := (forall_elim default).trans affine

instance exists_affine [BI PROP] (Φ : α → PROP) [∀ x, Affine (Φ x)] : Affine iprop(∃ x, Φ x) where
  affine := exists_elim fun _ => affine

instance sep_affine [BI PROP] (P Q : PROP) [Affine P] [Affine Q] : Affine iprop(P ∗ Q) where
  affine := (sep_mono affine affine).trans sep_emp.1

instance affinely_affine [BI PROP] (P : PROP) : Affine iprop(<affine> P) where
  affine := affinely_elim_emp

instance affinelyIf_affine (p : Bool) [BI PROP] (P : PROP) [Affine P] :
    Affine iprop(<affine>?p P) := by
  cases p <;> simp [affinelyIf] <;> infer_instance

instance intuitionistically_affine [BI PROP] (P : PROP) : Affine iprop(□ P) :=
  inferInstanceAs (Affine iprop(<affine> _))

instance intuitionisticallyIf_affine (p : Bool) [BI PROP] (P : PROP) [Affine P] :
    Affine iprop(□?p P) := by
  cases p <;> simp [intuitionisticallyIf] <;> infer_instance

-- Absorbing
instance and_absorbing [BI PROP] (P Q : PROP) [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P ∧ Q) where
  absorbing := absorbingly_and_1.trans (and_mono absorbing absorbing)

instance or_absorbing [BI PROP] (P Q : PROP) [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P ∨ Q) where
  absorbing := absorbingly_or.1.trans (or_mono absorbing absorbing)

instance forall_absorbing [BI PROP] (Φ : α → PROP) [∀ x, Absorbing (Φ x)] :
    Absorbing iprop(∀ x, Φ x) where
  absorbing := absorbingly_forall.trans (forall_mono fun _ => absorbing)

instance exists_absorbing [BI PROP] (Φ : α → PROP) [∀ x, Absorbing (Φ x)] :
    Absorbing iprop(∃ x, Φ x) where
  absorbing := absorbingly_exists.1.trans (exists_mono fun _ => absorbing)

instance imp_absorbing [BI PROP] (P Q : PROP) [Persistent P] [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P → Q) where
  absorbing := imp_intro' <| persistent_and_affinely_sep_l.1.trans <| absorbingly_sep_r.1.trans <|
    (absorbingly_mono <| persistent_and_affinely_sep_l.2.trans imp_elim_r).trans absorbing

instance sep_absorbing_l [BI PROP] (P Q : PROP) [Absorbing P] : Absorbing iprop(P ∗ Q) where
  absorbing := absorbingly_sep_l.2.trans (sep_mono_l absorbing)

instance sep_absorbing_r [BI PROP] (P Q : PROP) [Absorbing Q] : Absorbing iprop(P ∗ Q) where
  absorbing := absorbingly_sep_r.2.trans (sep_mono_r absorbing)

instance wand_absorbing_l [BI PROP] (P Q : PROP) [Absorbing P] : Absorbing iprop(P -∗ Q) where
  absorbing := wand_intro' <| sep_assoc.2.trans <| (sep_mono_l sep_elim_l).trans wand_elim_r

instance wand_absorbing_r [BI PROP] (P Q : PROP) [Absorbing Q] : Absorbing iprop(P -∗ Q) where
  absorbing := absorbingly_wand.trans (wand_mono absorbingly_intro absorbing)

instance absorbingly_absorbing [BI PROP] (P : PROP) : Absorbing iprop(<absorb> P) where
  absorbing := absorbingly_idem.1

instance persistently_absorbing [BI PROP] (P : PROP) : Absorbing iprop(<pers> P) where
  absorbing := absorbingly_persistently.1

instance persistentlyIf_absorbing [BI PROP] (P : PROP) (p : Bool) [Absorbing P] :
    Absorbing iprop(<pers>?p P) := by
  cases p <;> simp [persistentlyIf] <;> infer_instance

instance (priority := default + 10) biAffineAbsorbing [BIAffine PROP] (P : PROP) : Absorbing P where
  absorbing := (sep_mono_l affine).trans emp_sep.1
