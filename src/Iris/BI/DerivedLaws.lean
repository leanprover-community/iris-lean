import Iris.BI.Classes
import Iris.BI.DerivedConnectives
import Iris.BI.Extensions
import Iris.BI.Interface

namespace Iris.BI

-- Persistent instances
instance pure_persistent (φ : Prop) [BI PROP] :
  Persistent (PROP := PROP) `[iprop| ⌜φ⌝]
where
  persistent := sorry

instance emp_persistent [BI PROP] :
  Persistent (PROP := PROP) `[iprop| emp]
where
  persistent := sorry

instance and_persistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent `[iprop| P ∧ Q]
where
  persistent := sorry

instance or_persistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent `[iprop| P ∨ Q]
where
  persistent := sorry

instance exist_persistent [BI PROP] (Ψ : α → PROP) (h : ∀ x, Persistent (Ψ x)) :
  Persistent `[iprop| ∃ x, Ψ x]
where
  persistent := sorry

instance sep_persistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent `[iprop| P ∗ Q]
where
  persistent := sorry

instance persistently_persistent [BI PROP] (P : PROP) :
  Persistent `[iprop| <pers> P]
where
  persistent := sorry

instance affinely_persistent [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent `[iprop| <affine> P]
where
  persistent := sorry

instance affinely_if_persistent (p : Bool) [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent `[iprop| <affine>?p P]
where
  persistent := sorry

instance intuitionistically_persistent [BI PROP] (P : PROP) :
  Persistent `[iprop| □ P]
where
  persistent := sorry

instance absorbingly_persistent [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent `[iprop| <absorb> P]
where
  persistent := sorry

instance absorbingly_if_persistent (p : Bool) [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent `[iprop| <absorb>?p P]
where
  persistent := sorry

-- Affine instances
instance emp_affine [BI PROP] :
  Affine (PROP := PROP) `[iprop| emp]
where
  affine := sorry

instance False_affine [BI PROP] :
  Affine (PROP := PROP) `[iprop| False]
where
  affine := sorry

instance and_affine_l [BI PROP] (P Q : PROP) :
  [Affine P] →
  Affine `[iprop| P ∧ Q]
where
  affine := sorry

instance and_affine_r [BI PROP] (P Q : PROP) :
  [Affine Q] →
  Affine `[iprop| P ∧ Q]
where
  affine := sorry

instance or_affine [BI PROP] (P Q : PROP) :
  [Affine P] →
  [Affine Q] →
  Affine `[iprop| P ∨ Q]
where
  affine := sorry

instance forall_affine [Inhabited α] [BI PROP] (Φ : α → PROP) :
  [∀ x, Affine (Φ x)] →
  Affine `[iprop| ∀ x, Φ x]
where
  affine := sorry

instance exist_affine [BI PROP] (Φ : α → PROP) :
  [∀ x, Affine (Φ x)] →
  Affine `[iprop| ∃ x, Φ x]
where
  affine := sorry

instance sep_affine [BI PROP] (P Q : PROP) :
  [Affine P] →
  [Affine Q] →
  Affine `[iprop| P ∗ Q]
where
  affine := sorry

instance affinely_affine [BI PROP] (P : PROP) :
  Affine `[iprop| <affine> P]
where
  affine := sorry

instance affinely_if_affine (p : Bool) [BI PROP] (P : PROP) :
  [Affine P] →
  Affine `[iprop| <affine>?p P]
where
  affine := sorry

instance intuitionistically_affine [BI PROP] (P : PROP) :
  Affine `[iprop| □ P]
where
  affine := sorry

instance intuitionistically_if_affine (p : Bool) [BI PROP] (P : PROP) :
  [Affine P] →
  Affine `[iprop| □?p P]
where
  affine := sorry

-- Absorbing instances
instance pure_absorbing (φ : Prop) [BI PROP] :
  Absorbing (PROP := PROP) `[iprop| ⌜φ⌝]
where
  absorbing := sorry

instance and_absorbing [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P ∧ Q]
where
  absorbing := sorry

instance or_absorbing [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P ∨ Q]
where
  absorbing := sorry

instance forall_absorbing [BI PROP] (Φ : α → PROP) :
  [∀ x, Absorbing (Φ x)] →
  Absorbing `[iprop| ∀ x, Φ x]
where
  absorbing := sorry

instance exist_absorbing [BI PROP] (Φ : α → PROP) :
  [∀ x, Absorbing (Φ x)] →
  Absorbing `[iprop| ∃ x, Φ x]
where
  absorbing := sorry

instance impl_absorbing [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P → Q]
where
  absorbing := sorry

instance sep_absorbing_l [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  Absorbing `[iprop| P ∗ Q]
where
  absorbing := sorry

instance sep_absorbing_r [BI PROP] (P Q : PROP) :
  [Absorbing Q] →
  Absorbing `[iprop| P ∗ Q]
where
  absorbing := sorry

instance wand_absorbing_l [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  Absorbing `[iprop| P -∗ Q]
where
  absorbing := sorry

instance wand_absorbing_r [BI PROP] (P Q : PROP) :
  [Absorbing Q] →
  Absorbing `[iprop| P -∗ Q]
where
  absorbing := sorry

instance absorbingly_absorbing [BI PROP] (P : PROP) :
  Absorbing `[iprop| <absorb> P]
where
  absorbing := sorry

instance persistently_absorbing [BI PROP] (P : PROP) :
  Absorbing `[iprop| <pers> P]
where
  absorbing := sorry

instance persistently_if_absorbing [BI PROP] (P : PROP) (p : Bool) :
  [Absorbing P] →
  Absorbing `[iprop| <pers>?p P]
where
  absorbing := sorry

section Affine

instance bi_affine_absorbing [BIAffine PROP] (P : PROP) :
  Absorbing P
where
  absorbing := sorry

end Affine

end Iris.BI
