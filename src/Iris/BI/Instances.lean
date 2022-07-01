import Iris.BI.Classes
import Iris.BI.DerivedConnectives
import Iris.BI.DerivedLaws
import Iris.BI.Extensions
import Iris.BI.Interface
import Iris.Std.Classes

namespace Iris.BI
open Iris.Std
open BI

-- Persistent
instance purePersistent (φ : Prop) [BI PROP] :
  Persistent (PROP := PROP) `[iprop| ⌜φ⌝]
where
  persistent := by
    apply equiv_entails_1_2
    exact persistently_pure

instance empPersistent [BI PROP] :
  Persistent (PROP := PROP) `[iprop| emp]
where
  persistent := by
    exact persistently_emp_intro

instance andPersistent [BI PROP] (P Q : PROP)
  [instP : Persistent P]
  [instQ : Persistent Q] :
  Persistent `[iprop| P ∧ Q]
where
  persistent := by
    rw [persistently_and]
    exact and_mono instP.persistent instQ.persistent

instance orPersistent [BI PROP] (P Q : PROP)
  [instP : Persistent P]
  [instQ : Persistent Q] :
  Persistent `[iprop| P ∨ Q]
where
  persistent := by
    rw [persistently_or]
    exact or_mono instP.persistent instQ.persistent

instance existPersistent [BI PROP] (Ψ : α → PROP)
  (h : ∀ x, Persistent (Ψ x)) :
  Persistent `[iprop| ∃ x, Ψ x]
where
  persistent := by
    rw [persistently_exist]
    apply exist_mono
    intro x
    exact (h x).persistent

instance sepPersistent [BI PROP] (P Q : PROP)
  [instP : Persistent P]
  [instQ : Persistent Q] :
  Persistent `[iprop| P ∗ Q]
where
  persistent := by
    apply transitivity ?_ persistently_sep_2
    exact sep_mono instP.persistent instQ.persistent

instance persistentlyPersistent [BI PROP] (P : PROP) :
  Persistent `[iprop| <pers> P]
where
  persistent := by
    exact BI.persistently_idemp_2

instance affinelyPersistent [BI PROP] (P : PROP)
  [Persistent P] :
  Persistent `[iprop| <affine> P]
where
  persistent := by
    exact (andPersistent _ _).persistent

instance affinelyIfPersistent (p : Bool) [BI PROP] (P : PROP)
  [instP : Persistent P] :
  Persistent `[iprop| <affine>?p P]
where
  persistent := by
    simp only [bi_affinely_if]
    cases p
    <;> simp only [ite_true, ite_false]
    · exact instP.persistent
    · exact (affinelyPersistent _).persistent

instance intuitionisticallyPersistent [BI PROP] (P : PROP) :
  Persistent `[iprop| □ P]
where
  persistent := by
    exact (affinelyPersistent _).persistent

instance absorbinglyPersistent [BI PROP] (P : PROP)
  [Persistent P] :
  Persistent `[iprop| <absorb> P]
where
  persistent := by
    exact (sepPersistent _ _).persistent

instance absorbinglyIfPersistent (p : Bool) [BI PROP] (P : PROP)
  [instP : Persistent P] :
  Persistent `[iprop| <absorb>?p P]
where
  persistent := by
    simp only [bi_absorbingly_if]
    cases p
    <;> simp only [ite_true, ite_false]
    · exact instP.persistent
    · exact (absorbinglyPersistent _).persistent

-- Affine
instance empAffine [BI PROP] :
  Affine (PROP := PROP) `[iprop| emp]
where
  affine := by
    exact reflexivity

instance falseAffine [BI PROP] :
  Affine (PROP := PROP) `[iprop| False]
where
  affine := by
    exact False_elim

instance andAffineL [BI PROP] (P Q : PROP)
  [instP : Affine P] :
  Affine `[iprop| P ∧ Q]
where
  affine := by
    trans_rw instP.affine using and_mono ?_ reflexivity
    exact and_elim_l

instance andAffineR [BI PROP] (P Q : PROP)
  [instQ : Affine Q] :
  Affine `[iprop| P ∧ Q]
where
  affine := by
    trans_rw instQ.affine using and_mono reflexivity ?_
    exact and_elim_r

instance orAffine [BI PROP] (P Q : PROP)
  [instP : Affine P]
  [instQ : Affine Q] :
  Affine `[iprop| P ∨ Q]
where
  affine := by
    apply or_elim
    · exact instP.affine
    · exact instQ.affine

instance forallAffine [inhab : Inhabited α] [BI PROP] (Φ : α → PROP)
  [inst : ∀ x, Affine (Φ x)] :
  Affine `[iprop| ∀ x, Φ x]
where
  affine := by
    apply transitivity ?_ (inst inhab.default).affine
    exact forall_elim inhab.default

instance existAffine [BI PROP] (Φ : α → PROP)
  [inst : ∀ x, Affine (Φ x)] :
  Affine `[iprop| ∃ x, Φ x]
where
  affine := by
    apply exist_elim
    intro a
    exact (inst a).affine

instance sepAffine [BI PROP] (P Q : PROP)
  [instP : Affine P]
  [instQ : Affine Q] :
  Affine `[iprop| P ∗ Q]
where
  affine := by
    trans_rw instP.affine using sep_mono ?_ reflexivity
    rw [(left_id : emp ∗ Q ⊣⊢ _)]
    exact instQ.affine

instance affinelyAffine [BI PROP] (P : PROP) :
  Affine `[iprop| <affine> P]
where
  affine := by
    exact (andAffineL _ _).affine

instance affinelyIfAffine (p : Bool) [BI PROP] (P : PROP)
  [instP : Affine P] :
  Affine `[iprop| <affine>?p P]
where
  affine := by
    simp only [bi_affinely_if]
    cases p
    <;> simp only [ite_true, ite_false]
    · exact instP.affine
    · exact (affinelyAffine _).affine

instance intuitionisticallyAffine [BI PROP] (P : PROP) :
  Affine `[iprop| □ P]
where
  affine := by
    simp only [bi_intuitionistically]
    exact (affinelyAffine _ ).affine

instance intuitionisticallyIfAffine (p : Bool) [BI PROP] (P : PROP)
  [instP : Affine P] :
  Affine `[iprop| □?p P]
where
  affine := by
    simp only [bi_intuitionistically_if]
    cases p
    <;> simp only [ite_true, ite_false]
    · exact instP.affine
    · exact (intuitionisticallyAffine _).affine

-- Absorbing
instance pureAbsorbing (φ : Prop) [BI PROP] :
  Absorbing (PROP := PROP) `[iprop| ⌜φ⌝]
where
  absorbing := sorry

instance andAbsorbing [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P ∧ Q]
where
  absorbing := sorry

instance orAbsorbing [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P ∨ Q]
where
  absorbing := sorry

instance forallAbsorbing [BI PROP] (Φ : α → PROP) :
  [∀ x, Absorbing (Φ x)] →
  Absorbing `[iprop| ∀ x, Φ x]
where
  absorbing := sorry

instance existAbsorbing [BI PROP] (Φ : α → PROP) :
  [∀ x, Absorbing (Φ x)] →
  Absorbing `[iprop| ∃ x, Φ x]
where
  absorbing := sorry

instance implAbsorbing [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P → Q]
where
  absorbing := sorry

instance sepAbsorbingL [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  Absorbing `[iprop| P ∗ Q]
where
  absorbing := sorry

instance sepAbsorbingR [BI PROP] (P Q : PROP) :
  [Absorbing Q] →
  Absorbing `[iprop| P ∗ Q]
where
  absorbing := sorry

instance wandAbsorbingL [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  Absorbing `[iprop| P -∗ Q]
where
  absorbing := sorry

instance wandAbsorbingR [BI PROP] (P Q : PROP) :
  [Absorbing Q] →
  Absorbing `[iprop| P -∗ Q]
where
  absorbing := sorry

instance absorbinglyAbsorbing [BI PROP] (P : PROP) :
  Absorbing `[iprop| <absorb> P]
where
  absorbing := sorry

instance persistentlyAbsorbing [BI PROP] (P : PROP) :
  Absorbing `[iprop| <pers> P]
where
  absorbing := sorry

instance persistentlyIfAbsorbing [BI PROP] (P : PROP) (p : Bool) :
  [Absorbing P] →
  Absorbing `[iprop| <pers>?p P]
where
  absorbing := sorry

section Affine

instance biAffineAbsorbing [BIAffine PROP] (P : PROP) :
  Absorbing P
where
  absorbing := sorry

end Affine
end Iris.BI
