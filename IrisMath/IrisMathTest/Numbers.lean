/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IrisMath.Numbers

@[expose] public section

local stepindex Nat

namespace Real

open Iris
open scoped CommMonoidLike

/-- info: realUCMRA -/
#guard_msgs in
#synth UCMRA ℝ

/-- info: realDiscrete -/
#guard_msgs in
#synth ORA.Discrete ℝ

/-- info: @realCancelable -/
#guard_msgs in
#synth ∀ x : ℝ, ORA.Cancelable x

/-- info: realCoreIdZero -/
#guard_msgs in
#synth ORA.CoreId (0 : ℝ)

end Real

namespace ENNReal

open Iris
open scoped CommMonoidLike

/-- info: ennrealUCMRA -/
#guard_msgs in
#synth UCMRA ℝ≥0∞

/-- info: ennrealDiscrete -/
#guard_msgs in
#synth ORA.Discrete ℝ≥0∞

/-- info: ennrealCoreIdZero -/
#guard_msgs in
#synth ORA.CoreId (0 : ℝ≥0∞)

end ENNReal
