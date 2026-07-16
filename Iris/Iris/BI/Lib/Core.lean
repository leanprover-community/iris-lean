/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/

module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris

@[rocq_alias coreP]
def coreP [Sbi PROP] (P : PROP) : PROP :=
  iprop(∀ Q, <affine> ■ (Q -∗ <pers> Q) -∗ <affine> ■ (P -∗ Q) -∗ Q)

section Core

variable [Sbi PROP] {P Q : PROP}

@[rocq_alias coreP_intro]
theorem coreP_intro : P -∗ coreP P := by
  unfold coreP
  iintro HP %Q HQ HPQ
  iapply BI.affinely_plainly_elim $$ HPQ HP

end Core
