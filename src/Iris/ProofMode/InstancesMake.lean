/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Yunsong Yang
-/
import Iris.BI
import Iris.ProofMode.ClassesMake

namespace Iris.ProofMode
open Iris.BI

/- MakeAffinely -/

instance (priority := high) makeAffinely_affine [BI PROP] (P : PROP) [Affine P] :
    MakeAffinely P P where
  make_affinely := affine_affinely P

instance makeAffinely_True [BI PROP] :
    MakeAffinely (PROP := PROP) iprop(True) iprop(emp) where
  make_affinely := affinely_true

instance (priority := low) makeAffinely_default [BI PROP] (P : PROP) :
    MakeAffinely P iprop(<affine> P) where
  make_affinely := .rfl

/- MakeAbsorbingly -/
instance (priority := high) makeAbsorbingly_absorbing [BI PROP] (P : PROP) [Absorbing P] :
    MakeAbsorbingly P P where
  make_absorbingly := absorbing_absorbingly

instance makeAbsorbingly_emp [BI PROP] :
    MakeAbsorbingly (PROP := PROP) iprop(emp) iprop(True) where
  make_absorbingly := absorbingly_emp

instance (priority := low) makeAbsorbingly_default [BI PROP] (P : PROP) :
    MakeAbsorbingly P iprop(<absorb> P) where
  make_absorbingly := .rfl

/- MakePersistently -/
instance (priority := high) makePersistently_emp [BI PROP] :
    MakePersistently (PROP := PROP) iprop(emp) iprop(True) where
  make_persistently := persistently_emp

instance (priority := high) makePersistently_True [BI PROP] :
    MakePersistently (PROP := PROP) iprop(True) iprop(True) where
  make_persistently := persistently_true

instance (priority := low) makePersistently_default [BI PROP] (P : PROP) :
    MakePersistently P iprop(<pers> P) where
  make_persistently := .rfl

/- MakeIntuitionistically -/

instance (priority := high) makeIntuitionistically_emp [BI PROP] :
    MakeIntuitionistically (PROP := PROP) iprop(emp) iprop(emp) where
  make_intuitionistically := intuitionistically_emp

instance (priority := high) makeIntuitionistically_True_affine [BI PROP] [BIAffine PROP] :
    MakeIntuitionistically (PROP := PROP) iprop(True) iprop(True) where
  make_intuitionistically := intuitionistically_true.trans true_emp.symm

instance makeIntuitionistically_True [BI PROP] :
    MakeIntuitionistically (PROP := PROP) iprop(True) iprop(emp) where
  make_intuitionistically := intuitionistically_true

instance (priority := low) makeIntuitionistically_default [BI PROP] (P : PROP) :
    MakeIntuitionistically P iprop(□ P) where
  make_intuitionistically := .rfl

/- MakeLaterN -/

instance makeLaterN_0 [BI PROP] (P : PROP) : MakeLaterN 0 P P where
  make_laterN := .rfl

instance makeLaterN_1 [BI PROP] (P : PROP) : MakeLaterN 1 P iprop(▷ P) where
  make_laterN := .rfl

instance (priority := low) makeLaterN_default [BI PROP] n (P : PROP) :
    MakeLaterN n P iprop(▷^[n] P) where
  make_laterN := .rfl

instance (priority := high) makeLaterN_True [BI PROP] n :
    MakeLaterN (PROP:=PROP) n iprop(True) iprop(True) where
  make_laterN := laterN_true n

instance (priority := high) makeLaterN_emp [BI PROP] [BIAffine PROP] n :
    MakeLaterN (PROP:=PROP) n iprop(emp) iprop(emp) where
  make_laterN := laterN_emp n
