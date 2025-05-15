/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI.BI

namespace Iris.BI

/-- Require that the proposition `P` is persistent. -/
class Persistent [BI PROP] (P : PROP) where
  persistent : P ⊢ <pers> P
export Persistent (persistent)

/-- Require that the proposition `P` is affine. -/
class Affine [BI PROP] (P : PROP) where
  affine : P ⊢ emp
export Affine (affine)

/-- Require that the proposition `P` is absorbing. -/
class Absorbing [BI PROP] (P : PROP) where
  absorbing : <absorb> P ⊢ P
export Absorbing (absorbing)

/-- Require that the proposition `P` is intuitionistic. -/
class Intuitionistic [BI PROP] (P : PROP) where
  intuitionistic : P ⊢ □ P
export Intuitionistic (intuitionistic)

end Iris.BI
