/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode

namespace Iris.Tests
open BI ProofMode

/- Test the backtracking of ipm_synth -/
section backtracking

variable [BI PROP] (P1 P2 Q : PROP) [FromAssumption p .in P1 Q] [FromAssumption p .in P2 Q]

/- Test backtracking with both options. IPM backtracking search will search for right conjuncts before
left conjuncts, because `fromAssumption_and_r` is declared after `fromAssumption_and_l`.
This is the same behavior as regular typeclass search. -/
/-- info: solution: FromAssumption p InOut.in iprop(P1 ∧ P2) Q, new goals: [] -/
#guard_msgs in #ipm_synth (FromAssumption p .in iprop(P1 ∧ P2) Q)

/- Test backtracking picking the left conjunct. -/
/-- info: solution: FromAssumption p InOut.in iprop(P1 ∧ P2) P1, new goals: [] -/
#guard_msgs in #ipm_synth (FromAssumption p .in iprop(P1 ∧ P2) P1)

/- Test backtracking picking the right conjunct. -/
/-- info: solution: FromAssumption p InOut.in iprop(P1 ∧ P2) P2, new goals: [] -/
#guard_msgs in #ipm_synth (FromAssumption p .in iprop(P1 ∧ P2) P2)

end backtracking

/- Test creation and instantiation of mvars using of ipm_synth -/
section mvars

variable [BI PROP] (P1 P2 : Nat → PROP)

/- Test creation of mvars -/
/-- info: solution: IntoWand false false iprop(∀ x, P1 x -∗ P2 x) InOut.out (P1 ?m.24) InOut.out
  (P2 ?m.24), new goals: [?m.24: Nat] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(∀ a, P1 a -∗ P2 a) .out _ .out _)

/- Test instantiation of forall quantifier -/
/-- info: solution: IntoWand false false iprop(∀ x, P1 x -∗ P2 x) InOut.in (P1 1) InOut.out (P2 1), new goals: [] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(∀ a, P1 a -∗ P2 a) .in (P1 1) .out _)

/- Test instantiation of mvar created outside ipm_synth -/
/-- info: solution: IntoWand false false iprop(P1 1 -∗ P2 1) InOut.in (P1 1) InOut.out (P2 1), new goals: [] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(P1 _ -∗ P2 1) .in (P1 1) .out _)

end mvars
