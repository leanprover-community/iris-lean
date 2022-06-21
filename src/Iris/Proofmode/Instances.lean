import Iris.BI
import Iris.Proofmode.Classes
import Iris.Std.TC

namespace Iris.Proofmode
open Iris.BI Iris.Std

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

-- FromForall
instance from_forall_forall [BI PROP] (Φ : α → PROP) :
  FromForall (BIBase.forall Φ) Φ
where
  from_forall := sorry

-- FromAnd
instance (priority := default - 10) from_and_and [BI PROP] (P1 P2 : PROP) :
  FromAnd `[iprop| P1 ∧ P2] P1 P2
where
  from_and := sorry

instance (priority := default + 30) from_and_sep_persistent_l [BI PROP] (P1 P1' P2 : PROP) :
  [Persistent P1] →
  [IntoAbsorbingly P1' P1] →
  FromAnd `[iprop| P1 ∗ P2] P1' P2
where
  from_and := sorry

instance (priority := default + 20) from_and_sep_persistent_r [BI PROP] (P1 P2 P2' : PROP) :
  [Persistent P2] →
  [IntoAbsorbingly P2' P2] →
  FromAnd `[iprop| P1 ∗ P2] P1 P2'
where
  from_and := sorry

instance (priority := default + 50) from_and_pure (φ ψ : Prop) [BI PROP] :
  FromAnd (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_and := sorry

instance (priority := default + 40) from_and_persistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromAnd P Q1 Q2] →
  FromAnd `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_and := sorry

instance (priority := default + 10) from_and_persistently_sep [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromAnd `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_and := sorry

-- IntoAnd
instance (priority := default - 10) into_and_and (p : Bool) [BI PROP] (P Q : PROP) :
  IntoAnd p `[iprop| P ∧ Q] P Q
where
  into_and := sorry

instance into_and_and_affine_l [BI PROP] (P Q Q' : PROP) :
  [Affine P] →
  [FromAffinely Q' Q] →
  IntoAnd false `[iprop| P ∧ Q] P Q'
where
  into_and := sorry

instance into_and_and_affine_r [BI PROP] (P P' Q : PROP) :
  [Affine Q] →
  [FromAffinely P' P] →
  IntoAnd false `[iprop| P ∧ Q] P' Q
where
  into_and := sorry

instance into_and_sep_affine (p : Bool) [BI PROP] (P Q : PROP) :
  [TCOr (Affine P) (Absorbing Q)] →
  [TCOr (Absorbing P) (Affine Q)] →
  IntoAnd p `[iprop| P ∗ Q] P Q
where
  into_and := sorry

instance into_and_pure (p : Bool) (φ ψ : Prop) [BI PROP] :
  IntoAnd (PROP := PROP) p `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_and := sorry

instance into_and_affinely (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  into_and := sorry

instance into_and_intuitionistically (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_and := sorry

instance into_and_persistently (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_and := sorry

-- FromSep
instance (priority := default - 10) from_sep_sep [BI PROP] (P1 P2 : PROP) :
  FromSep `[iprop| P1 ∗ P2] P1 P2
where
  from_sep := sorry

instance (priority := default - 20) from_sep_and [BI PROP] (P1 P2 : PROP) :
  [TCOr (Affine P1) (Absorbing P2)] →
  [TCOr (Absorbing P1) (Affine P2)] →
  FromSep `[iprop| P1 ∧ P2] P1 P2
where
  from_sep := sorry

instance (priority := default + 20) from_sep_pure (φ ψ : Prop) [BI PROP] :
  FromSep (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_sep := sorry

instance (priority := default + 10) from_sep_affinely [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  from_sep := sorry

instance (priority := default + 10) from_sep_intuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  from_sep := sorry

instance (priority := default + 10) from_sep_absorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  from_sep := sorry

instance (priority := default + 10) from_sep_persistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_sep := sorry

-- AndIntoSep (private)
private class AndIntoSep [BI PROP] (P Q : PROP) (P' Q' : outParam PROP) where
  and_into_sep : P' ∗ Q' ⊢ P ∧ Q

instance (priority := default + 10) and_into_sep_affine [BI PROP] (P Q Q' : PROP) :
  [Affine P] →
  [FromAffinely Q' Q] →
  AndIntoSep P Q P Q'
where
  and_into_sep := sorry

instance and_into_sep [BI PROP] (P Q : PROP) :
  AndIntoSep P Q `[iprop| <affine> P] Q
where
  and_into_sep := sorry

-- IntoSep
instance into_sep_sep [BI PROP] (P Q : PROP) :
  IntoSep `[iprop| P ∗ Q] P Q
where
  into_sep := sorry

instance into_sep_and_persistent_l [BI PROP] (P Q P' Q' : PROP) :
  [Persistent P] →
  [AndIntoSep P Q P' Q'] →
  IntoSep `[iprop| P ∧ Q] P' Q'
where
  into_sep := sorry

instance into_sep_and_persistent_r [BI PROP] (P Q P' Q' : PROP) :
  [Persistent Q] →
  [AndIntoSep Q P Q' P'] →
  IntoSep `[iprop| P ∧ Q] P' Q'
where
  into_sep := sorry

instance into_sep_pure (φ ψ : Prop) [BI PROP] :
  IntoSep (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_sep := sorry

instance (priority := default - 10) into_sep_affinely_trim [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  IntoSep `[iprop| <affine> P] Q1 Q2
where
  into_sep := sorry

instance into_sep_persistently_affine [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  [TCOr (Affine Q1) (Absorbing Q2)] →
  [TCOr (Absorbing Q1) (Affine Q2)] →
  IntoSep `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_sep := sorry

instance into_sep_intuitionistically_affine [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  [TCOr (Affine Q1) (Absorbing Q2)] →
  [TCOr (Absorbing Q1) (Affine Q2)] →
  IntoSep `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_sep := sorry

-- FromOr
instance from_or_or [BI PROP] (P1 P2 : PROP) :
  FromOr `[iprop| P1 ∨ P2] P1 P2
where
  from_or := sorry

instance from_or_pure (φ ψ : Prop) [BI PROP] :
  FromOr (PROP := PROP) `[iprop| ⌜φ ∨ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_or := sorry

instance from_or_affinely [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  from_or := sorry

instance from_or_intuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  from_or := sorry

instance from_or_absorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  from_or := sorry

instance from_or_persistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_or := sorry

-- IntoOr
instance into_or_or [BI PROP] (P Q : PROP) :
  IntoOr `[iprop| P ∨ Q] P Q
where
  into_or := sorry

instance into_or_pure (φ ψ : Prop) [BI PROP] :
  IntoOr (PROP := PROP) `[iprop| ⌜φ ∨ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_or := sorry

instance into_or_affinely [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  into_or := sorry

instance into_or_intuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_or := sorry

instance into_or_absorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  into_or := sorry

instance into_or_persistently [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_or := sorry

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
  [Affine P] →                                        -- if P is affine
  FromAffinely P P true                               -- then <affine> P ⊢ P
where
  from_affinely := sorry

instance (priority := default - 10) from_affinely_default [BI PROP] (P : PROP) :
  FromAffinely `[iprop| <affine> P] P true            -- always <affine> P ⊢ <affine> P
where
  from_affinely := sorry

instance (priority := default - 10) from_affinely_intuitionistically [BI PROP] (P : PROP) :
  FromAffinely `[iprop| □ P] `[iprop| <pers> P] true  -- always <affine> <pers> P ⊢ □ P
where
  from_affinely := sorry

instance from_affinely_id [BI PROP] (P : PROP) :
  FromAffinely P P false                              -- always P ⊢ P
where
  from_affinely := sorry

-- IntoAbsorbingly
instance (priority := default + 30) into_absorbingly_True [BI PROP] :
  IntoAbsorbingly (PROP := PROP) `[iprop| True] `[iprop| emp]
where
  into_absorbingly := sorry

instance (priority := default + 20) into_absorbingly_absorbing [BI PROP] (P : PROP) :
  [Absorbing P] →
  IntoAbsorbingly P P
where
  into_absorbingly := sorry

instance (priority := default + 10) into_absorbingly_intuitionistically [BI PROP] (P : PROP) :
  IntoAbsorbingly `[iprop| <pers> P] `[iprop| □ P]
where
  into_absorbingly := sorry

instance (priority := default - 10) into_absorbingly_default [BI PROP] (P : PROP) :
  IntoAbsorbingly `[iprop| <absorb> P] P
where
  into_absorbingly := sorry

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

-- IntoPure
instance into_pure_pure (φ : Prop) [BI PROP] :
  IntoPure (PROP := PROP) `[iprop| ⌜φ⌝] φ
where
  into_pure := sorry

instance into_pure_pure_and (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∧ P2] (φ1 ∧ φ2)
where
  into_pure := sorry

instance into_pure_pure_or (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∨ P2] (φ1 ∨ φ2)
where
  into_pure := sorry

instance into_pure_exist [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, IntoPure (Φ x) (φ x)] →
  IntoPure `[iprop| ∃ x, Φ x] (∃ x, φ x)
where
  into_pure := sorry

instance into_pure_pure_sep (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∗ P2] (φ1 ∧ φ2)
where
  into_pure := sorry

instance into_pure_affinely [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <affine> P] φ
where
  into_pure := sorry

instance into_pure_intuitionistically [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| □ P] φ
where
  into_pure := sorry

instance into_pure_absorbingly [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <absorb> P] φ
where
  into_pure := sorry

instance into_pure_persistently [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <pers> P] φ
where
  into_pure := sorry

end Iris.Proofmode
