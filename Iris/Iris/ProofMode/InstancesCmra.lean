/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.Algebra.CMRA
public import Iris.ProofMode.Classes
import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.ProofMode
open Iris

section cmra

variable {PROP} [Sbi PROP]

@[rocq_alias into_pure_internal_cmra_valid]
instance intoPure_internalCmraValid α [CMRA α] [CMRA.Discrete α] (a : α) :
  IntoPure (PROP := PROP) iprop(✓ a) (✓ a) where
  into_pure := internalCmraValid_discrete.1

@[rocq_alias from_pure_internal_cmra_valid]
instance fromPure_internalCmraValid io α [CMRA α] (a : α) :
  FromPure (PROP := PROP) false iprop(✓ a) io (✓ a) where
  from_pure := BI.pure_elim' internalCmraValid_intro

@[rocq_alias into_pure_internal_included]
instance intoPure_internalCmraIncluded α [CMRA α] [CMRA.Discrete α] (a b : α) :
  IntoPure (PROP := PROP) iprop(a ≼ b) (a ≼ b) where
  into_pure := internalCmraIncluded_discrete.1

@[rocq_alias from_pure_internal_included]
instance fromPure_internalCmraIncluded io α [CMRA α] (a b : α) :
  FromPure (PROP := PROP) false iprop(a ≼ b) io (a ≼ b) where
  from_pure := BI.pure_elim' internalCmraIncluded_intro

@[rocq_alias into_exist_internal_included]
instance intoExists_internalCmraIncluded α [CMRA α] (a b : α) :
  IntoExists (PROP := PROP) iprop(a ≼ b) (λ c => iprop(b ≡ (a • c))) where
  into_exists := siPure_exist.1

@[rocq_alias from_exist_internal_included]
instance fromExists_internalCmraIncluded α [CMRA α] (a b : α) :
  FromExists (PROP := PROP) iprop(a ≼ b) (λ c => iprop(b ≡ (a • c))) where
  from_exists := siPure_exist.2

end cmra
