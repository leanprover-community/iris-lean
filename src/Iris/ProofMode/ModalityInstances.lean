/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI
import Iris.BI.DerivedLaws
import Iris.ProofMode.Modalities

namespace Iris.ProofMode
open Iris.BI

section Modalities

variable {PROP : Type _} [BI PROP]

instance : IsModal (PROP1 := PROP) persistently (MIEnvId rfl) MIEnvClear where
  spec_intuitionistic _ := persistent
  spec_spatial P := persistently_absorbing P
  emp := persistently_emp_2
  mono := (persistently_mono ·)
  sep := persistently_sep_2

instance : IsModal (PROP1 := PROP) affinely (MIEnvId rfl) (MIEnvForall rfl Affine) where
  spec_intuitionistic _ := affinely_intro .rfl
  spec_spatial _ _ := affinely_intro .rfl
  emp := affinely_intro .rfl
  mono := (affinely_mono ·)
  sep := affinely_sep_2

instance : IsModal (PROP1 := PROP) intuitionistically (MIEnvId rfl) MIEnvIsEmpty where
  spec_intuitionistic _ := intuitionistic
  spec_spatial := trivial
  emp := intuitionistic
  mono := (intuitionistically_mono ·)
  sep := intuitionistically_sep_2

end Modalities
