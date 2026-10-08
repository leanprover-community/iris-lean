/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
module

public import Iris.BI.BI

@[expose] public section


namespace Iris.BI

/-- Require that the proposition `P` is persistent. -/
@[rocq_alias Persistent]
class Persistent [BI.BIBase PROP] (P : PROP) where
  persistent : P ⊢ <pers> P
export Persistent (persistent)

/-- Require that the proposition `P` is affine. -/
@[rocq_alias Affine]
class Affine [BI.BIBase PROP] (P : PROP) where
  affine : P ⊢ emp
export Affine (affine)

/-- Require that the proposition `P` is absorbing. -/
@[rocq_alias Absorbing]
class Absorbing [BI.BIBase PROP] (P : PROP) where
  absorbing : <absorb> P ⊢ P
export Absorbing (absorbing)

/-- Require that the proposition `P` is intuitionistic. -/
class Intuitionistic [BI.BIBase PROP] (P : PROP) where
  intuitionistic : P ⊢ □ P
export Intuitionistic (intuitionistic)

/-- Require that the proposition `P` does not depend on the step index.

There are two equivalent ways to say this for a step-indexed `P`:
* `<only0> P ⊢ P` (used here): `P` at step-index 0 gives `P` at every index. This works for
  transfinite step indices without further assumptions.
* `▷ P ⊢ ◇ P`: `P` is preserved by each step.

Both are equivalent in the logic using Löb induction and `later_false_em`; see `timeless_alt`,
`timeless_except0` and `Timeless.of_later` in `Iris.BI.DerivedLawsLater`. -/
@[rocq_alias Timeless]
class Timeless [BI.BIBase PROP] (P : PROP) where
  timeless : <only0> P ⊢ P

end Iris.BI
