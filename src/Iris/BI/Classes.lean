import Iris.BI.DerivedConnectives
import Iris.BI.Interface

namespace Iris.BI

/-- Require that the proposition `P` is persistent. -/
class Persistent [BI PROP] (P : PROP) : Prop where
  persistent : P ⊢ <pers> P
export Persistent (persistent)

/-- Require that the proposition `P` is affine. -/
class Affine [BI PROP] (P : PROP) : Prop where
  affine : P ⊢ emp
export Affine (affine)

/-- Require that the proposition `P` is absorbing. -/
class Absorbing [BI PROP] (P : PROP) : Prop where
  absorbing : <absorb> P ⊢ P
export Absorbing (absorbing)

end Iris.BI
