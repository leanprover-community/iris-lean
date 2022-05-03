import Iris.BI.Classes
import Iris.BI.DerivedConnectives
import Iris.BI.Interface

namespace Iris.BI

variable [BI PROP]

-- Persistent instances
instance pure_persistent (φ : Prop) : Persistent (PROP := PROP) `[iprop| ⌜φ⌝] where
  persistent := sorry
instance emp_persistent : Persistent (PROP := PROP) `[iprop| emp] where
  persistent := sorry
instance and_persistent (P Q : PROP) [Persistent P] [Persistent Q] : Persistent `[iprop| P ∧ Q] where
  persistent := sorry
instance or_persistent (P Q : PROP) [Persistent P] [Persistent Q] : Persistent `[iprop| P ∨ Q] where
  persistent := sorry
-- TODO `forall_persistent` if `BiPersistentlyForall`
instance exist_persistent (Ψ : α → PROP) (h : ∀ x, Persistent (Ψ x)) : Persistent `[iprop| ∃ x, Ψ x] where
  persistent := sorry

instance sep_persistent (P Q : PROP) [Persistent P] [Persistent Q] : Persistent `[iprop| P ∗ Q] where
  persistent := sorry

instance persistently_persistent (P : PROP) : Persistent `[iprop| <pers> P] where
  persistent := sorry
instance affinely_persistent (P : PROP) [Persistent P] : Persistent `[iprop| <affine> P] where
  persistent := sorry
instance affinely_if_persistent (p : Bool) (P : PROP) [Persistent P] : Persistent `[iprop| <affine>?p P] where
  persistent := sorry
instance intuitionistically_persistent (P : PROP) : Persistent `[iprop| □ P] where
  persistent := sorry
instance absorbingly_persistent (P : PROP) [Persistent P] : Persistent `[iprop| <absorb> P] where
  persistent := sorry
instance absorbingly_if_persistent (p : Bool) (P : PROP) [Persistent P] : Persistent `[iprop| <absorb>?p P] where
  persistent := sorry
-- TODO add `from_option_persistent`

-- Affine instances
instance emp_affine : Affine (PROP := PROP) `[iprop| emp] where
  affine := sorry
instance False_affine : Affine (PROP := PROP) `[iprop| False] where
  affine := sorry
instance and_affine_l (P Q : PROP) [Affine P] : Affine `[iprop| P ∧ Q] where
  affine := sorry
instance and_affine_r (P Q : PROP) [Affine Q] : Affine `[iprop| P ∧ Q] where
  affine := sorry
instance or_affine (P Q : PROP) [Affine P] [Affine Q] : Affine `[iprop| P ∨ Q] where
  affine := sorry
instance forall_affine [Inhabited α] (Φ : α → PROP) (h : ∀ x, Affine (Φ x)) : Affine `[iprop| ∀ x, Φ x] where
  affine := sorry
instance exist_affine (Φ : α → PROP) (h : ∀ x, Affine `[iprop| Φ x]) : Affine `[iprop| ∃ x, Φ x] where
  affine := sorry

instance sep_affine (P Q : PROP) [Affine P] [Affine Q] : Affine `[iprop| P ∗ Q] where
  affine := sorry
instance affinely_affine (P : PROP) : Affine `[iprop| <affine> P] where
  affine := sorry
instance affinely_if_affine (p : Bool) (P : PROP) [Affine P] : Affine `[iprop| <affine>?p P] where
  affine := sorry
instance intuitionistically_affine (P : PROP) : Affine `[iprop| □ P] where
  affine := sorry
instance intuitionistically_if_affine (p : Bool) (P : PROP) [Affine P] : Affine `[iprop| □?p P] where
  affine := sorry

-- Absorbing instances
instance pure_absorbing (φ : Prop) : Absorbing (PROP := PROP) `[iprop| ⌜φ⌝] where
  absorbing := sorry
instance and_absorbing (P Q : PROP) [Absorbing P] [Absorbing Q] : Absorbing `[iprop| P ∧ Q] where
  absorbing := sorry
instance or_absorbing (P Q : PROP) [Absorbing P] [Absorbing Q] : Absorbing `[iprop| P ∨ Q] where
  absorbing := sorry
instance forall_absorbing (Φ : α → PROP) (h : ∀ x, Absorbing (Φ x)) : Absorbing `[iprop| ∀ x, Φ x] where
  absorbing := sorry
instance exist_absorbing (Φ : α → PROP) (h : ∀ x, Absorbing (Φ x)) : Absorbing `[iprop| ∃ x, Φ x] where
  absorbing := sorry

instance impl_absorbing (P Q : PROP) [Persistent P] [Absorbing P] [Absorbing Q] : Absorbing `[iprop| P → Q] where
  absorbing := sorry

instance sep_absorbing_l (P Q : PROP) [Absorbing P] : Absorbing `[iprop| P ∗ Q] where
  absorbing := sorry
instance sep_absorbing_r (P Q : PROP) [Absorbing Q] : Absorbing `[iprop| P ∗ Q] where
  absorbing := sorry

instance wand_absorbing_l (P Q : PROP) [Absorbing P] : Absorbing `[iprop| P -∗ Q] where
  absorbing := sorry
instance wand_absorbing_r (P Q : PROP) [Absorbing Q] : Absorbing `[iprop| P -∗ Q] where
  absorbing := sorry

instance absorbingly_absorbing (P : PROP) : Absorbing `[iprop| <absorb> P] where
  absorbing := sorry
instance persistently_absorbing (P : PROP) : Absorbing `[iprop| <pers> P] where
  absorbing := sorry
instance persistently_if_absorbing (P : PROP) (p : Bool) [Absorbing P] : Absorbing `[iprop| <pers>?p P] where
  absorbing := sorry

end Iris.BI
