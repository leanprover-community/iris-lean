import Iris.BI
import Iris.Proofmode.Classes

namespace Iris.Proofmode
open Iris.BI

variable [bi : BI PROP]

-- AsEmpValid
instance (priority := default + 10) as_emp_valid_emp_valid (P : PROP) : AsEmpValid (⊢ P) P where
  bi := bi
  as_emp_valid := sorry

instance as_emp_valid_entails (P Q : PROP) : AsEmpValid (P ⊢ Q) `[iprop| P -∗ Q] where
  bi := bi
  as_emp_valid := sorry

instance as_emp_valid_equiv (P Q : PROP) : AsEmpValid (P ≡ Q) `[iprop| P ∗-∗ Q] where
  bi := bi
  as_emp_valid := sorry

-- FromImpl
instance from_impl_impl (P1 P2 : PROP) :
  FromImpl `[iprop| P1 → P2] P1 P2
where
  from_impl := sorry

-- FromWand
instance from_wand_wand (P1 P2 : PROP) :
  FromWand `[iprop| P1 -∗ P2] P1 P2
where
  from_wand := sorry

-- IntoPersistent
instance (priority := default + 20) into_persistent_persistently (p : Bool) (P Q : PROP) :
  [IntoPersistent true P Q] →             -- if <pers> P ⊢ <pers> Q
  IntoPersistent p `[iprop| <pers> P] Q   -- then <pers>?p <pers> P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 20) into_persistent_affinely (p : Bool) (P Q : PROP) :
  [IntoPersistent p P Q] →                -- if <pers>?p P ⊢ <pers> Q
  IntoPersistent p `[iprop| <affine> P] Q -- then <pers>?p <affine> P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 20) into_persistent_intuitionistically (p : Bool) (P Q : PROP) :
  [IntoPersistent true P Q] →             -- if <pers> P ⊢ <pers> Q
  IntoPersistent p `[iprop| □ P] Q        -- then <pers>?p □ P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 10) into_persistent_here (P : PROP) :
  IntoPersistent true P P                 -- always <pers> P ⊢ <pers> P
where
  into_persistent := sorry

instance (priority := default - 10) into_persistent_persistent (P : PROP) :
  [Persistent P] →                        -- if P is persistent
  IntoPersistent false P P                -- then P ⊢ <pers> P
where
  into_persistent := sorry

-- FromAffinely
instance from_affinely_affine (P : PROP) :
  [Affine P] →                                  -- if P is affine
  FromAffinely P P                              -- then <affine> P ⊢ P
where
  from_affinely := sorry

instance (priority := default - 10) from_affinely_default (P : PROP) :
  FromAffinely `[iprop| <affine> P] P           -- always <affine> P ⊢ <affine> P
where
  from_affinely := sorry

instance (priority := default - 10) from_affinely_intuitionistically (P : PROP) :
  FromAffinely `[iprop| □ P] `[iprop| <pers> P] -- always <affine> <pers> P ⊢ □ P
where
  from_affinely := sorry

end Iris.Proofmode
