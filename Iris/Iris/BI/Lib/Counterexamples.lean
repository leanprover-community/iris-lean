/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.BI.Extensions
public import Iris.BI.Sbi
public import Iris.ProofMode
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

open Iris.Std BI

/-! ## Excluded middle makes separating conjunction trivial for affine props -/

section AffineEM

variable {PROP : Type _} [BI PROP]
variable (em : ∀ P : PROP, ⊢ P ∨ ¬P)
variable (P Q : PROP)
include em

@[rocq_alias affine_em.sep_dup]
theorem sep_dup [Affine P] : P ⊢ P ∗ P := by
  iintro HP
  icases (em P) with (HP' | HnotP)
  · iframe HP HP'
  · iexfalso
    iapply HnotP $$ HP

@[rocq_alias affine_em.and_sep]
theorem and_sep [BIAffine PROP] : P ∧ Q ⊢ P ∗ Q := by
  iintro HPQ
  icases sep_dup $$ HPQ with ⟨HPQ, HPQ'⟩
  · assumption
  · isplitl [HPQ]
    · icases HPQ with ⟨HP, -⟩
      iassumption
    · icases HPQ' with ⟨-, HQ⟩
      iassumption

end AffineEM
