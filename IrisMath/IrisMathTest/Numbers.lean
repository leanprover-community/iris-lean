module

public import IrisMath.Numbers

@[expose] public section

namespace Real

open Iris
open scoped CommMonoidLike

/-- info: CommMonoidLike.instUCMRA -/
#guard_msgs in
#synth UCMRA ℝ

/-- info: CommMonoidLike.instDiscrete -/
#guard_msgs in
#synth CMRA.Discrete ℝ

/-- info: fun x ↦ CommMonoidLike.instCancelable -/
#guard_msgs in
#synth ∀ x : ℝ, CMRA.Cancelable x

/-- info: CommMonoidLike.instCoreIdZero -/
#guard_msgs in
#synth CMRA.CoreId (0 : ℝ)

end Real

namespace ENNReal

open Iris
open scoped CommMonoidLike

/-- info: CommMonoidLike.instUCMRA -/
#guard_msgs in
#synth UCMRA ℝ≥0∞

/-- info: CommMonoidLike.instDiscrete -/
#guard_msgs in
#synth CMRA.Discrete ℝ≥0∞

/-- info: CommMonoidLike.instCoreIdZero -/
#guard_msgs in
#synth CMRA.CoreId (0 : ℝ≥0∞)

end ENNReal
