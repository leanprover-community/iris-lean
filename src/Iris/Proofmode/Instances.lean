import Iris.BI
import Iris.Proofmode.Classes

namespace Iris.Proofmode
open Iris.BI

-- AsEmpValid
instance (priority := default + 10) as_emp_valid_emp_valid [bi : BI PROP] (P : PROP) :
  AsEmpValid (⊢ P) P
where
  bi := bi
  as_emp_valid := sorry

instance as_emp_valid_entails [bi : BI PROP] (P Q : PROP) :
  AsEmpValid (P ⊢ Q) `[iprop| P -∗ Q]
where
  bi := bi
  as_emp_valid := sorry

instance as_emp_valid_equiv [bi : BI PROP] (P Q : PROP) :
  AsEmpValid (P ≡ Q) `[iprop| P ∗-∗ Q]
where
  bi := bi
  as_emp_valid := sorry

-- FromImpl
instance from_impl_impl [BI PROP] (P1 P2 : PROP) :
  FromImpl `[iprop| P1 → P2] P1 P2
where
  from_impl := sorry

-- FromWand
instance from_wand_wand [BI PROP] (P1 P2 : PROP) :
  FromWand `[iprop| P1 -∗ P2] P1 P2
where
  from_wand := sorry

-- IntoPersistent
instance (priority := default + 20) into_persistent_persistently (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent true P Q] →             -- if <pers> P ⊢ <pers> Q
  IntoPersistent p `[iprop| <pers> P] Q   -- then <pers>?p <pers> P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 20) into_persistent_affinely (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent p P Q] →                -- if <pers>?p P ⊢ <pers> Q
  IntoPersistent p `[iprop| <affine> P] Q -- then <pers>?p <affine> P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 20) into_persistent_intuitionistically (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent true P Q] →             -- if <pers> P ⊢ <pers> Q
  IntoPersistent p `[iprop| □ P] Q        -- then <pers>?p □ P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 10) into_persistent_here [BI PROP] (P : PROP) :
  IntoPersistent true P P                 -- always <pers> P ⊢ <pers> P
where
  into_persistent := sorry

instance (priority := default - 10) into_persistent_persistent [BI PROP] (P : PROP) :
  [Persistent P] →                        -- if P is persistent
  IntoPersistent false P P                -- then P ⊢ <pers> P
where
  into_persistent := sorry

-- FromAffinely
instance from_affinely_affine [BI PROP] (P : PROP) :
  [Affine P] →                                  -- if P is affine
  FromAffinely P P                              -- then <affine> P ⊢ P
where
  from_affinely := sorry

instance (priority := default - 10) from_affinely_default [BI PROP] (P : PROP) :
  FromAffinely `[iprop| <affine> P] P           -- always <affine> P ⊢ <affine> P
where
  from_affinely := sorry

instance (priority := default - 10) from_affinely_intuitionistically [BI PROP] (P : PROP) :
  FromAffinely `[iprop| □ P] `[iprop| <pers> P] -- always <affine> <pers> P ⊢ □ P
where
  from_affinely := sorry

-- FromAssumption
instance (priority := default + 100) from_assumption_exact (p : Bool) [BI PROP] (P : PROP) :
  FromAssumption p P P
where
  from_assumption := sorry

instance (priority := default + 30) from_assumption_persistently_r [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| <pers> Q]
where
  from_assumption := sorry

instance (priority := default + 30) from_assumption_affinely_r [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| <affine> Q]
where
  from_assumption := sorry

instance (priority := default + 30) from_assumption_intuitionistically_r [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| □ Q]
where
  from_assumption := sorry

instance (priority := default + 20) from_assumption_absorbingly_r (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p P `[iprop| <absorb> Q]
where
  from_assumption := sorry

instance (priority := default + 20) from_assumption_intuitionistically_l (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption p `[iprop| □ P] Q
where
  from_assumption := sorry

instance (priority := default + 20) from_assumption_intuitionistically_l_true (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p `[iprop| □ P] Q
where
  from_assumption := sorry

instance (priority := default + 30) from_assumption_persistently_l_true [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true `[iprop| <pers> P] Q
where
  from_assumption := sorry

instance (priority := default + 30) from_assumption_persistently_l_false [BI PROP] (P Q : PROP) :
  [BIAffine PROP] →
  [FromAssumption true P Q] →
  FromAssumption false `[iprop| <pers> P] Q
where
  from_assumption := sorry

instance (priority := default + 20) from_assumption_affinely_l (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p `[iprop| <affine> P] Q
where
  from_assumption := sorry

instance (priority := default + 10) from_assumption_forall (p : Bool) [BI PROP] (Φ : α → PROP) (x : α) (Q : PROP) :
  [FromAssumption p (Φ x) Q] →
  FromAssumption p `[iprop| ∀ x, Φ x] Q
where
  from_assumption := sorry

end Iris.Proofmode
