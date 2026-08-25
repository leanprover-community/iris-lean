/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.UPred

@[expose] public section

namespace IrisTest
open Iris BI ProofMode CMRA UPred

section

variable [UCMRA M] (a b : M) (c : M) [CoreId c]

/- Tests `fromSep_ownM`. -/
/-- info:
  solution: FromSep (ownM (a • b)) (ownM a) (ownM b),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth FromSep (ownM (a • b)) _ _

/- Tests `intoSep_ownM`. -/
/-- info:
  solution: IntoSep (ownM (a • b)) (ownM a) (ownM b),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoSep (ownM (a • b)) _ _

/- Tests `intoAnd_ownM`. -/
/-- info:
  solution: IntoAnd p (ownM (a • b)) (ownM a) (ownM b),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (p : Bool) in
#ipm_synth IntoAnd p (ownM (a • b)) _ _

/-
  Using `combineSepGives_ownM` along with `combineSepAs_intuitionistically`.
  The instance `combineSepAs_ownM` has a higher priority than `combineSepAs_default`.
-/
/-- info:
  solution: CombineSepAs iprop(□ ownM a) iprop(□ ownM b) iprop(□ ownM (a • b)),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth CombineSepAs iprop(□ ownM a) iprop(□ ownM b) _

/- Tests `combineSepGives_ownM`. -/
/-- info:
  solution: CombineSepGives (ownM a) (ownM b) iprop(✓ a • b),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth CombineSepGives (ownM a) (ownM b) _

/- Using `combineSepGives_ownM` along with `combineSepGives_intuitionistically`. -/
/-- info:
  solution: CombineSepGives iprop(□ ownM a) iprop(□ ownM b) iprop(✓ a • b),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth CombineSepGives iprop(□ ownM a) iprop(□ ownM b) _

/-
  Tests `intoSep_ownM` with `CoreId c` (and thus `TCOr (CoreId a) (CoreId c)`),
  along with `isOp_pair_core_id_r`.
-/
/-- info:
  solution: IntoSep (ownM (a • b, c)) (ownM (a, c)) (ownM (b, c)),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoSep (ownM ((a • b, c) : M × M)) _ _
-- expect: (ownM (a, c)) ∗ (ownM (b, c))   [isOp_pair_core_id_r]

/- Tests `intoSep_ownM` along with `isOp_pair`. -/
/-- info:
  solution: IntoSep (ownM (a • b, a • b)) (ownM (a, a)) (ownM (b, b)),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoSep (ownM ((a • b, a • b) : M × M)) _ _

end
