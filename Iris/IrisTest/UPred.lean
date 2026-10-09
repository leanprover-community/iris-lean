/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.UPred

@[expose] public section

namespace IrisTest
open Iris BI ProofMode ORA UPred

section

variable [URA M] [UCMRA Nat M] (a b : M) (c : M) [CoreId c]

/- Tests `fromSep_ownM`. -/
/-- info: solution: FromSep (ownM Nat (a • b)) (ownM Nat a) (ownM Nat b), new goals: [] -/
#guard_msgs (whitespace := lax) in
#ipm_synth FromSep (ownM Nat (a • b)) _ _

/- Tests `intoSep_ownM`. -/
/-- info: solution: IntoSep (ownM Nat (a • b)) (ownM Nat a) (ownM Nat b), new goals: [] -/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoSep (ownM Nat (a • b)) _ _

/- Tests `intoAnd_ownM` (which requires an affine algebra). -/
/-- info: solution: IntoAnd p (ownM Nat (a • b)) (ownM Nat a) (ownM Nat b), new goals: [] -/
#guard_msgs (whitespace := lax) in
variable (p : Bool) [ORA.Affine Nat M] in
#ipm_synth IntoAnd p (ownM Nat (a • b)) _ _

/-
  Using `combineSepGives_ownM` along with `combineSepAs_intuitionistically`.
  The instance `combineSepAs_ownM` has a higher priority than `combineSepAs_default`.
-/
/-- info: solution: CombineSepAs iprop(□ ownM Nat a) iprop(□ ownM Nat b) iprop(□ ownM Nat (a • b)), new goals: [] -/
#guard_msgs (whitespace := lax) in
#ipm_synth CombineSepAs iprop(□ ownM Nat a) iprop(□ ownM _ b) _

/- Tests `combineSepGives_ownM`. -/
/-- info: solution: CombineSepGives (ownM Nat a) (ownM Nat b) iprop(✓[Nat] a • b), new goals: [] -/
#guard_msgs (whitespace := lax) in
#ipm_synth CombineSepGives (ownM Nat a) (ownM _ b) _

/- Using `combineSepGives_ownM` along with `combineSepGives_intuitionistically`. -/
/-- info: solution: CombineSepGives iprop(□ ownM Nat a) iprop(□ ownM Nat b) iprop(✓[Nat] a • b), new goals: [] -/
#guard_msgs (whitespace := lax) in
#ipm_synth CombineSepGives iprop(□ ownM Nat a) iprop(□ ownM _ b) _

/-
  Tests `intoSep_ownM` with `CoreId c` (and thus `TCOr (CoreId a) (CoreId c)`),
  along with `isOp_pair_core_id_r`.
-/
/-- info: solution: IntoSep (ownM Nat (a • b, c)) (ownM Nat (a, c)) (ownM Nat (b, c)), new goals: [] -/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoSep (ownM Nat ((a • b, c) : M × M)) _ _
-- expect: (ownM (a, c)) ∗ (ownM (b, c))   [isOp_pair_core_id_r]

/- Tests `intoSep_ownM` along with `isOp_pair`. -/
/-- info: solution: IntoSep (ownM Nat (a • b, a • b)) (ownM Nat (a, a)) (ownM Nat (b, b)), new goals: [] -/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoSep (ownM Nat ((a • b, a • b) : M × M)) _ _

end

end IrisTest
