/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Yunsong Yang
-/
module

public import Iris.BI
public import Iris.ProofMode.ClassesMake

@[expose] public section

namespace Iris.ProofMode
open Iris.BI

/- QuickAffine -/
@[rocq_alias bi_affine_quick_affine]
instance quickAffine_biAffine [BI PROP] (P : PROP) [BIAffine PROP] :
  QuickAffine P where
  quick_affine := inferInstance

@[rocq_alias False_quick_affine]
instance quickAffine_False [BI PROP] :
  QuickAffine (PROP:=PROP) iprop(False) where
  quick_affine := inferInstance

@[rocq_alias emp_quick_affine]
instance quickAffine_emp [BI PROP] :
  QuickAffine (PROP:=PROP) iprop(emp) where
  quick_affine := inferInstance

@[rocq_alias affinely_quick_affine]
instance quickAffine_affinely [BI PROP] (P : PROP) :
  QuickAffine iprop(<affine> P) where
  quick_affine := inferInstance

@[rocq_alias intuitionistically_quick_affine]
instance quickAffine_intuitionistically [BI PROP] (P : PROP) :
  QuickAffine iprop(□ P) where
  quick_affine := inferInstance

/- QuickAbsorbing -/
@[rocq_alias bi_affine_quick_absorbing]
instance quickAbsorbing_biAffine [BI PROP] (P : PROP) [BIAffine PROP] :
  QuickAbsorbing P where
  quick_absorbing := inferInstance

@[rocq_alias pure_quick_absorbing]
instance quickAbsorbing_pure [BI PROP] (P : Prop) :
  QuickAbsorbing (PROP:=PROP) iprop(⌜P⌝) where
  quick_absorbing := inferInstance

@[rocq_alias absorbingly_quick_absorbing]
instance quickAbsorbing_absorbingly [BI PROP] (P : PROP) :
  QuickAbsorbing iprop(<absorb> P) where
  quick_absorbing := inferInstance

@[rocq_alias persistently_quick_absorbing]
instance quickAbsorbing_persistently [BI PROP] (P : PROP) :
  QuickAbsorbing iprop(<pers> P) where
  quick_absorbing := inferInstance

/- MakeSep -/

@[rocq_alias make_sep_emp_l]
instance makeSep_emp_l [BI PROP] (P : PROP) : MakeSep iprop(emp) P P where
  make_sep := emp_sep

@[rocq_alias make_sep_emp_r]
instance makeSep_emp_r [BI PROP] (P : PROP) : MakeSep P iprop(emp) P where
  make_sep := sep_emp

@[rocq_alias make_sep_true_l]
instance makeSep_true_l [BI PROP] (P : PROP) [h : QuickAbsorbing P] : MakeSep iprop(True) P P where
  make_sep := have := h.1; true_sep

@[rocq_alias make_sep_true_r]
instance makeSep_true_r [BI PROP] (P : PROP) [h : QuickAbsorbing P] : MakeSep P iprop(True) P where
  make_sep := have := h.1; sep_true

@[rocq_alias make_sep_default]
instance (priority:=low) makeSep_default [BI PROP] (P Q : PROP) : MakeSep P Q iprop(P ∗ Q) where
  make_sep := .rfl

/- MakeAnd -/

@[rocq_alias make_and_true_l]
instance makeAnd_true_l [BI PROP] (P : PROP) : MakeAnd iprop(True) P P where
  make_and := true_and

@[rocq_alias make_and_true_r]
instance makeAnd_true_r [BI PROP] (P : PROP) : MakeAnd P iprop(True) P where
  make_and := and_true

@[rocq_alias make_and_emp_l]
instance makeAnd_emp_l [BI PROP] (P : PROP) [h : QuickAffine P] : MakeAnd iprop(emp) P P where
  make_and := have := h.1; emp_and

@[rocq_alias make_and_emp_r]
instance makeAnd_emp_r [BI PROP] (P : PROP) [h : QuickAffine P] : MakeAnd P iprop(emp) P where
  make_and := have := h.1; and_emp

@[rocq_alias make_and_false_l]
instance makeAnd_false_l [BI PROP] (P : PROP) : MakeAnd iprop(False) P iprop(False) where
  make_and := false_and

@[rocq_alias make_and_false_r]
instance makeAnd_false_r [BI PROP] (P : PROP) : MakeAnd P iprop(False) iprop(False) where
  make_and := and_false

@[rocq_alias make_and_default]
instance (priority:=low) makeAnd_default [BI PROP] (P Q : PROP) : MakeAnd P Q iprop(P ∧ Q) where
  make_and := .rfl

/- MakeOr -/

@[rocq_alias make_or_true_l]
instance makeOr_true_l [BI PROP] (P : PROP) : MakeOr iprop(True) P iprop(True) where
  make_or := true_or

@[rocq_alias make_or_true_r]
instance makeOr_true_r [BI PROP] (P : PROP) : MakeOr P iprop(True) iprop(True) where
  make_or := or_true

@[rocq_alias make_or_emp_l]
instance makeOr_emp_l [BI PROP] (P : PROP) [h : QuickAffine P] : MakeOr iprop(emp) P iprop(emp) where
  make_or := have := h.1; emp_or

@[rocq_alias make_or_emp_r]
instance makeOr_emp_r [BI PROP] (P : PROP) [h : QuickAffine P] : MakeOr P iprop(emp) iprop(emp) where
  make_or := have := h.1; or_emp

@[rocq_alias make_or_false_l]
instance makeOr_false_l [BI PROP] (P : PROP) : MakeOr iprop(False) P P where
  make_or := false_or

@[rocq_alias make_or_false_r]
instance makeOr_false_r [BI PROP] (P : PROP) : MakeOr P iprop(False) P where
  make_or := or_false

@[rocq_alias make_or_default]
instance (priority:=low) makeOr_default [BI PROP] (P Q : PROP) : MakeOr P Q iprop(P ∨ Q) where
  make_or := .rfl

/- MakeAffinely -/

@[rocq_alias make_affinely_affine]
instance (priority := high) makeAffinely_affine [BI PROP] (P : PROP) [Affine P] :
    MakeAffinely P P where
  make_affinely := affine_affinely P

@[rocq_alias make_affinely_True]
instance makeAffinely_True [BI PROP] :
    MakeAffinely (PROP := PROP) iprop(True) iprop(emp) where
  make_affinely := affinely_true

@[rocq_alias make_affinely_default]
instance (priority := low) makeAffinely_default [BI PROP] (P : PROP) :
    MakeAffinely P iprop(<affine> P) where
  make_affinely := .rfl

/- MakeAbsorbingly -/
@[rocq_alias make_absorbingly_absorbing]
instance (priority := high) makeAbsorbingly_absorbing [BI PROP] (P : PROP) [Absorbing P] :
    MakeAbsorbingly P P where
  make_absorbingly := absorbing_absorbingly

@[rocq_alias make_absorbingly_emp]
instance makeAbsorbingly_emp [BI PROP] :
    MakeAbsorbingly (PROP := PROP) iprop(emp) iprop(True) where
  make_absorbingly := absorbingly_emp

@[rocq_alias make_absorbingly_default]
instance (priority := low) makeAbsorbingly_default [BI PROP] (P : PROP) :
    MakeAbsorbingly P iprop(<absorb> P) where
  make_absorbingly := .rfl

/- MakePersistently -/
@[rocq_alias make_persistently_emp]
instance (priority := high) makePersistently_emp [BI PROP] :
    MakePersistently (PROP := PROP) iprop(emp) iprop(True) where
  make_persistently := persistently_emp

@[rocq_alias make_persistently_True]
instance (priority := high) makePersistently_True [BI PROP] :
    MakePersistently (PROP := PROP) iprop(True) iprop(True) where
  make_persistently := persistently_true

@[rocq_alias make_persistently_default]
instance (priority := low) makePersistently_default [BI PROP] (P : PROP) :
    MakePersistently P iprop(<pers> P) where
  make_persistently := .rfl

/- MakeIntuitionistically -/

@[rocq_alias make_intuitionistically_emp]
instance (priority := high) makeIntuitionistically_emp [BI PROP] :
    MakeIntuitionistically (PROP := PROP) iprop(emp) iprop(emp) where
  make_intuitionistically := intuitionistically_emp

@[rocq_alias make_intuitionistically_True_affine]
instance (priority := high) makeIntuitionistically_True_affine [BI PROP] [BIAffine PROP] :
    MakeIntuitionistically (PROP := PROP) iprop(True) iprop(True) where
  make_intuitionistically := intuitionistically_true.trans true_emp.symm

@[rocq_alias make_intuitionistically_True]
instance makeIntuitionistically_True [BI PROP] :
    MakeIntuitionistically (PROP := PROP) iprop(True) iprop(emp) where
  make_intuitionistically := intuitionistically_true

@[rocq_alias make_intuitionistically_default]
instance (priority := low) makeIntuitionistically_default [BI PROP] (P : PROP) :
    MakeIntuitionistically P iprop(□ P) where
  make_intuitionistically := .rfl

/- MakeLaterN -/

instance makeLaterN_0 [BI PROP] (P : PROP) : MakeLaterN 0 P P where
  make_laterN := .rfl

instance makeLaterN_1 [BI PROP] (P : PROP) : MakeLaterN 1 P iprop(▷ P) where
  make_laterN := .rfl

@[rocq_alias make_laterN_default]
instance (priority := low) makeLaterN_default [BI PROP] n (P : PROP) :
    MakeLaterN n P iprop(▷^[n] P) where
  make_laterN := .rfl

@[rocq_alias make_laterN_true]
instance (priority := high) makeLaterN_True [BI PROP] n :
    MakeLaterN (PROP:=PROP) n iprop(True) iprop(True) where
  make_laterN := laterN_true n

@[rocq_alias make_laterN_emp]
instance (priority := high) makeLaterN_emp [BI PROP] [BIAffine PROP] n :
    MakeLaterN (PROP:=PROP) n iprop(emp) iprop(emp) where
  make_laterN := laterN_emp n

/- MakeExcept0 -/

@[rocq_alias make_except_0_True]
instance makeExcept0_True [BI PROP] :
    MakeExcept0 (PROP:=PROP) iprop(True) iprop(True) where
  make_except0 := except0_true

@[rocq_alias make_except_0_default]
instance (priority := low) makeExcept0_default [BI PROP] (P : PROP) :
    MakeExcept0 P iprop(◇ P) where
  make_except0 := .rfl

/- MakeBUpd -/

instance makeBUpd_True [BI PROP] [BIUpdate PROP] :
    MakeBUpd (PROP:=PROP) iprop(True) iprop(True) where
  make_bupd := ⟨true_intro, BIUpdate.intro⟩

instance (priority := low) makeBUpd_default [BI PROP] [BIUpdate PROP] (P : PROP) :
    MakeBUpd P iprop(|==> P) where
  make_bupd := .rfl

/- MakeFUpd -/

instance makeFUpd_True [BI PROP] [BIFUpdate PROP] E :
    MakeFUpd (PROP:=PROP) E E iprop(True) iprop(True) where
  make_fupd := ⟨true_intro, fupd_intro⟩

instance (priority := low) makeFUpd_default [BI PROP] [BIFUpdate PROP] E1 E2 (P : PROP) :
    MakeFUpd E1 E2 P iprop(|={E1, E2}=> P) where
  make_fupd := .rfl
