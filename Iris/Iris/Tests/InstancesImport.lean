/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

import Iris.Tests.Instances

/- This file tests that IPM tactic instances declared in other files are imported and applied correctly. -/

@[expose] public section

namespace Iris.Tests
open Lean Qq BI ProofMode

variable {PROP} [BI PROP] (P : PROP)

/--
info: tac_continue called with TacticTest iprop(∀ x, (emp ∗ P) ∗ P) ?_
---
info: tac_continue called with TacticTest iprop((emp ∗ P) ∗ P) (?_ a)
---
info: tac_continue called with TacticTest iprop(emp ∗ P) ?_
---
info: solution: TacticTest iprop(∀ a, (emp ∗ P) ∗ P) iprop(∀ a, P ∗ P), new goals: []
-/
#guard_msgs in
set_option pp.mvars false in
#ipm_synth (TacticTest iprop(∀ (_ : Nat), (emp ∗ P) ∗ P) _)
