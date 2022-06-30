import Iris.BI
import Iris.Proofmode.Classes
import Iris.Std.TC

namespace Iris.Proofmode
open Iris.BI Iris.Std

-- AsEmpValid
instance (priority := default + 10) asEmpValidEmpValid [bi : BI PROP] (P : PROP) :
  AsEmpValid (⊢ P) P
where
  bi := bi
  as_emp_valid := sorry

instance asEmpValidEntails [bi : BI PROP] (P Q : PROP) :
  AsEmpValid (P ⊢ Q) `[iprop| P -∗ Q]
where
  bi := bi
  as_emp_valid := sorry

instance asEmpValidEquiv [bi : BI PROP] (P Q : PROP) :
  AsEmpValid (P ≡ Q) `[iprop| P ∗-∗ Q]
where
  bi := bi
  as_emp_valid := sorry

-- FromImpl
instance fromImplImpl [BI PROP] (P1 P2 : PROP) :
  FromImpl `[iprop| P1 → P2] P1 P2
where
  from_impl := sorry

-- FromWand
instance fromWandWand [BI PROP] (P1 P2 : PROP) :
  FromWand `[iprop| P1 -∗ P2] P1 P2
where
  from_wand := sorry

-- FromForall
instance fromForallForall [BI PROP] (Φ : α → PROP) :
  FromForall (BIBase.forall Φ) Φ
where
  from_forall := sorry

-- FromExist
instance (priority := default + 10) fromExistExist [BI PROP] (Φ : α → PROP) :
  FromExist `[iprop| ∃ a, Φ a] Φ
where
  from_exist := sorry

instance fromExistPure (φ : α → Prop) [BI PROP] :
  FromExist (PROP := PROP) `[iprop| ⌜∃ x, φ x⌝] (fun a => `[iprop| ⌜φ a⌝])
where
  from_exist := sorry

instance fromExistAffinely [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExist P Φ] →
  FromExist `[iprop| <affine> P] (fun a => `[iprop| <affine> (Φ a)])
where
  from_exist := sorry

instance fromExistIntuitionistically [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExist P Φ] →
  FromExist `[iprop| □ P] (fun a => `[iprop| □ (Φ a)])
where
  from_exist := sorry

instance fromExistAbsorbingly [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExist P Φ] →
  FromExist `[iprop| <absorb> P] (fun a => `[iprop| <absorb> (Φ a)])
where
  from_exist := sorry

instance from_exist_persistently [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExist P Φ] →
  FromExist `[iprop| <pers> P] (fun a => `[iprop| <pers> (Φ a)])
where
  from_exist := sorry

-- FromAnd
instance (priority := default - 10) fromAndAnd [BI PROP] (P1 P2 : PROP) :
  FromAnd `[iprop| P1 ∧ P2] P1 P2
where
  from_and := sorry

instance (priority := default + 30) fromAndSepPersistentL [BI PROP] (P1 P1' P2 : PROP) :
  [Persistent P1] →
  [IntoAbsorbingly P1' P1] →
  FromAnd `[iprop| P1 ∗ P2] P1' P2
where
  from_and := sorry

instance (priority := default + 20) fromAndSepPersistentR [BI PROP] (P1 P2 P2' : PROP) :
  [Persistent P2] →
  [IntoAbsorbingly P2' P2] →
  FromAnd `[iprop| P1 ∗ P2] P1 P2'
where
  from_and := sorry

instance (priority := default + 50) fromAndPure (φ ψ : Prop) [BI PROP] :
  FromAnd (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_and := sorry

instance (priority := default + 40) fromAndPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromAnd P Q1 Q2] →
  FromAnd `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_and := sorry

instance (priority := default + 10) fromAndPersistentlySep [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromAnd `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_and := sorry

-- IntoAnd
instance (priority := default - 10) intoAndAnd (p : Bool) [BI PROP] (P Q : PROP) :
  IntoAnd p `[iprop| P ∧ Q] P Q
where
  into_and := sorry

instance intoAndAndAffineL [BI PROP] (P Q Q' : PROP) :
  [Affine P] →
  [FromAffinely Q' Q] →
  IntoAnd false `[iprop| P ∧ Q] P Q'
where
  into_and := sorry

instance intoAndAndAffineR [BI PROP] (P P' Q : PROP) :
  [Affine Q] →
  [FromAffinely P' P] →
  IntoAnd false `[iprop| P ∧ Q] P' Q
where
  into_and := sorry

instance intoAndSepAffine (p : Bool) [BI PROP] (P Q : PROP) :
  [TCOr (Affine P) (Absorbing Q)] →
  [TCOr (Absorbing P) (Affine Q)] →
  IntoAnd p `[iprop| P ∗ Q] P Q
where
  into_and := sorry

instance intoAndPure (p : Bool) (φ ψ : Prop) [BI PROP] :
  IntoAnd (PROP := PROP) p `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_and := sorry

instance intoAndAffinely (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  into_and := sorry

instance intoAndIntuitionistically (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_and := sorry

instance intoAndPersistently (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_and := sorry

-- FromSep
instance (priority := default - 10) fromSepSep [BI PROP] (P1 P2 : PROP) :
  FromSep `[iprop| P1 ∗ P2] P1 P2
where
  from_sep := sorry

instance (priority := default - 20) fromSepAnd [BI PROP] (P1 P2 : PROP) :
  [TCOr (Affine P1) (Absorbing P2)] →
  [TCOr (Absorbing P1) (Affine P2)] →
  FromSep `[iprop| P1 ∧ P2] P1 P2
where
  from_sep := sorry

instance (priority := default + 20) fromSepPure (φ ψ : Prop) [BI PROP] :
  FromSep (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_sep := sorry

instance (priority := default + 10) fromSepAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  from_sep := sorry

instance (priority := default + 10) fromSepIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  from_sep := sorry

instance (priority := default + 10) fromSepAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  from_sep := sorry

instance (priority := default + 10) fromSepPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_sep := sorry

-- AndIntoSep (private)
private class AndIntoSep [BI PROP] (P Q : PROP) (P' Q' : outParam PROP) where
  and_into_sep : P' ∗ Q' ⊢ P ∧ Q

instance (priority := default + 10) andIntoSepAffine [BI PROP] (P Q Q' : PROP) :
  [Affine P] →
  [FromAffinely Q' Q] →
  AndIntoSep P Q P Q'
where
  and_into_sep := sorry

instance andIntoSep [BI PROP] (P Q : PROP) :
  AndIntoSep P Q `[iprop| <affine> P] Q
where
  and_into_sep := sorry

-- IntoSep
instance intoSepSep [BI PROP] (P Q : PROP) :
  IntoSep `[iprop| P ∗ Q] P Q
where
  into_sep := sorry

instance intoSepAndPersistentL [BI PROP] (P Q P' Q' : PROP) :
  [Persistent P] →
  [AndIntoSep P Q P' Q'] →
  IntoSep `[iprop| P ∧ Q] P' Q'
where
  into_sep := sorry

instance intoSepAndPersistentR [BI PROP] (P Q P' Q' : PROP) :
  [Persistent Q] →
  [AndIntoSep Q P Q' P'] →
  IntoSep `[iprop| P ∧ Q] P' Q'
where
  into_sep := sorry

instance intoSepPure (φ ψ : Prop) [BI PROP] :
  IntoSep (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_sep := sorry

instance (priority := default - 10) intoSepAffinelyTrim [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  IntoSep `[iprop| <affine> P] Q1 Q2
where
  into_sep := sorry

instance intoSepPersistentlyAffine [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  [TCOr (Affine Q1) (Absorbing Q2)] →
  [TCOr (Absorbing Q1) (Affine Q2)] →
  IntoSep `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_sep := sorry

instance intoSepIntuitionisticallyAffine [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  [TCOr (Affine Q1) (Absorbing Q2)] →
  [TCOr (Absorbing Q1) (Affine Q2)] →
  IntoSep `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_sep := sorry

-- FromOr
instance fromOrOr [BI PROP] (P1 P2 : PROP) :
  FromOr `[iprop| P1 ∨ P2] P1 P2
where
  from_or := sorry

instance fromOrPure (φ ψ : Prop) [BI PROP] :
  FromOr (PROP := PROP) `[iprop| ⌜φ ∨ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_or := sorry

instance fromOrAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  from_or := sorry

instance fromOrIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  from_or := sorry

instance fromOrAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  from_or := sorry

instance fromOrPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_or := sorry

-- IntoOr
instance intoOrOr [BI PROP] (P Q : PROP) :
  IntoOr `[iprop| P ∨ Q] P Q
where
  into_or := sorry

instance intoOrPure (φ ψ : Prop) [BI PROP] :
  IntoOr (PROP := PROP) `[iprop| ⌜φ ∨ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_or := sorry

instance intoOrAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  into_or := sorry

instance intoOrIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_or := sorry

instance intoOrAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  into_or := sorry

instance intoOrPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_or := sorry

-- IntoPersistent
instance (priority := default + 20) intoPersistentPersistently (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent true P Q] →             -- if <pers> P ⊢ <pers> Q
  IntoPersistent p `[iprop| <pers> P] Q   -- then <pers>?p <pers> P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 20) intoPersistentAffinely (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent p P Q] →                -- if <pers>?p P ⊢ <pers> Q
  IntoPersistent p `[iprop| <affine> P] Q -- then <pers>?p <affine> P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 20) intoPersistentIntuitionistically (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent true P Q] →             -- if <pers> P ⊢ <pers> Q
  IntoPersistent p `[iprop| □ P] Q        -- then <pers>?p □ P ⊢ <pers> Q
where
  into_persistent := sorry

instance (priority := default + 10) intoPersistentHere [BI PROP] (P : PROP) :
  IntoPersistent true P P                 -- always <pers> P ⊢ <pers> P
where
  into_persistent := sorry

instance (priority := default - 10) intoPersistentPersistent [BI PROP] (P : PROP) :
  [Persistent P] →                        -- if P is persistent
  IntoPersistent false P P                -- then P ⊢ <pers> P
where
  into_persistent := sorry

-- FromAffinely
instance fromAffinelyAffine [BI PROP] (P : PROP) :
  [Affine P] →                                        -- if P is affine
  FromAffinely P P true                               -- then <affine> P ⊢ P
where
  from_affinely := sorry

instance (priority := default - 10) fromAffinelyDefault [BI PROP] (P : PROP) :
  FromAffinely `[iprop| <affine> P] P true            -- always <affine> P ⊢ <affine> P
where
  from_affinely := sorry

instance (priority := default - 10) fromAffinelyIntuitionistically [BI PROP] (P : PROP) :
  FromAffinely `[iprop| □ P] `[iprop| <pers> P] true  -- always <affine> <pers> P ⊢ □ P
where
  from_affinely := sorry

instance fromAffinelyId [BI PROP] (P : PROP) :
  FromAffinely P P false                              -- always P ⊢ P
where
  from_affinely := sorry

-- IntoAbsorbingly
instance (priority := default + 30) intoAbsorbinglyTrue [BI PROP] :
  IntoAbsorbingly (PROP := PROP) `[iprop| True] `[iprop| emp]
where
  into_absorbingly := sorry

instance (priority := default + 20) intoAbsorbinglyAbsorbing [BI PROP] (P : PROP) :
  [Absorbing P] →
  IntoAbsorbingly P P
where
  into_absorbingly := sorry

instance (priority := default + 10) intoAbsorbinglyIntuitionistically [BI PROP] (P : PROP) :
  IntoAbsorbingly `[iprop| <pers> P] `[iprop| □ P]
where
  into_absorbingly := sorry

instance (priority := default - 10) intoAbsorbinglyDefault [BI PROP] (P : PROP) :
  IntoAbsorbingly `[iprop| <absorb> P] P
where
  into_absorbingly := sorry

-- FromAssumption
instance (priority := default + 100) fromAssumptionExact (p : Bool) [BI PROP] (P : PROP) :
  FromAssumption p P P
where
  from_assumption := sorry

instance (priority := default + 30) fromAssumptionPersistentlyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| <pers> Q]
where
  from_assumption := sorry

instance (priority := default + 30) fromAssumptionAffinelyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| <affine> Q]
where
  from_assumption := sorry

instance (priority := default + 30) fromAssumptionIntuitionisticallyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| □ Q]
where
  from_assumption := sorry

instance (priority := default + 20) fromAssumptionAbsorbinglyR (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p P `[iprop| <absorb> Q]
where
  from_assumption := sorry

instance (priority := default + 20) fromAssumptionIntuitionisticallyL (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption p `[iprop| □ P] Q
where
  from_assumption := sorry

instance (priority := default + 20) fromAssumptionIntuitionisticallyLTrue (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p `[iprop| □ P] Q
where
  from_assumption := sorry

instance (priority := default + 30) FromAssumptionPersistentlyLTrue [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true `[iprop| <pers> P] Q
where
  from_assumption := sorry

instance (priority := default + 30) fromAssumptionPersistentlyLFalse [BI PROP] (P Q : PROP) :
  [BIAffine PROP] →
  [FromAssumption true P Q] →
  FromAssumption false `[iprop| <pers> P] Q
where
  from_assumption := sorry

instance (priority := default + 20) fromAssumptionAffinelyL (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p `[iprop| <affine> P] Q
where
  from_assumption := sorry

instance (priority := default + 10) fromAssumptionForall (p : Bool) [BI PROP] (Φ : α → PROP) (x : α) (Q : PROP) :
  [FromAssumption p (Φ x) Q] →
  FromAssumption p `[iprop| ∀ x, Φ x] Q
where
  from_assumption := sorry

-- IntoPure
instance intoPurePure (φ : Prop) [BI PROP] :
  IntoPure (PROP := PROP) `[iprop| ⌜φ⌝] φ
where
  into_pure := sorry

instance intoPurePureAnd (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∧ P2] (φ1 ∧ φ2)
where
  into_pure := sorry

instance intoPurePureOr (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∨ P2] (φ1 ∨ φ2)
where
  into_pure := sorry

instance intoPureExist [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, IntoPure (Φ x) (φ x)] →
  IntoPure `[iprop| ∃ x, Φ x] (∃ x, φ x)
where
  into_pure := sorry

instance intoPurePureSep (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∗ P2] (φ1 ∧ φ2)
where
  into_pure := sorry

instance intoPureAffinely [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <affine> P] φ
where
  into_pure := sorry

instance intoPureIntuitionistically [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| □ P] φ
where
  into_pure := sorry

instance intoPureAbsorbingly [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <absorb> P] φ
where
  into_pure := sorry

instance intoPurePersistently [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <pers> P] φ
where
  into_pure := sorry

-- FromPure
instance fromPureEmp [BI PROP] :
  FromPure (PROP := PROP) true `[iprop| emp] True
where
  from_pure := sorry

instance fromPurePure [BI PROP] (φ : Prop) :
  FromPure (PROP := PROP) false `[iprop| ⌜φ⌝] φ
where
  from_pure := sorry

instance fromPurePureAnd (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 || a2) `[iprop| P1 ∧ P2] (φ1 ∧ φ2)
where
  from_pure := sorry

instance fromPurePureOr (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 || a2) `[iprop| P1 ∨ P2] (φ1 ∨ φ2)
where
  from_pure := sorry

instance fromPurePureImpl (a : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [FromPure a P2 φ2] →
  FromPure a `[iprop| P1 → P2] (φ1 → φ2)
where
  from_pure := sorry

instance fromPureExist (a : Bool) [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, FromPure a `[iprop| Φ x] (φ x)] →
  FromPure a `[iprop| ∃ x, Φ x] (∃ x, φ x)
where
  from_pure := sorry

instance fromPureForall (a : Bool) [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, FromPure a `[iprop| Φ x] (φ x)] →
  FromPure a `[iprop| ∀ x, Φ x] (∀ x, φ x)
where
  from_pure := sorry

instance fromPurePureSepTrue (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 && a2) `[iprop| P1 ∗ P2] (φ1 ∧ φ2)
where
  from_pure := sorry

instance fromPurePureWand (a : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [FromPure a P2 φ2] →
  [TCIte a (Affine P1) TCTrue] →
  FromPure a `[iprop| P1 -∗ P2] (φ1 → φ2)
where
  from_pure := sorry

instance fromPurePersistently [BI PROP] (P : PROP) (a : Bool) (φ : Prop) :
  [FromPure true P φ] →
  FromPure a `[iprop| <pers> P] φ
where
  from_pure := sorry

instance fromPureAffinelyTrue (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure true `[iprop| <affine> P] φ
where
  from_pure := sorry

instance fromPureIntuitionisticallyTrue (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure true `[iprop| □ P] φ
where
  from_pure := sorry

instance fromPureAbsorbingly (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure false `[iprop| <absorb> P] φ
where
  from_pure := sorry

end Iris.Proofmode
