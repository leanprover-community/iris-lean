/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.StepIndexFinite

@[expose] public section

namespace IrisTest.StepIndexSugar.Left

@[indexed]
def SharedFamily (SI : stepindex (Type)) (A : Type) := SI × A

end IrisTest.StepIndexSugar.Left
