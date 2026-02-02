/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode.ClassesMake

namespace Iris.ProofMode
open Iris.BI

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
