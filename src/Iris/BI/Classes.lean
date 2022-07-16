import Iris.BI.DerivedConnectives
import Iris.BI.Interface

namespace Iris.BI

class Persistent [BI PROP] (P : PROP) : Prop where
  persistent : P ⊢ <pers> P
export Persistent (persistent)

class Affine [BI PROP] (P : PROP) : Prop where
  affine : P ⊢ emp
export Affine (affine)

class Absorbing [BI PROP] (P : PROP) : Prop where
  absorbing : <absorb> P ⊢ P
export Absorbing (absorbing)

end Iris.BI
