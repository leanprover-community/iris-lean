import Iris.BI.DerivedConnectives
import Iris.BI.Interface

namespace Iris.BI

class Persistent [BI PROP] (P : PROP) : Prop where
  persistent : P ⊢ <pers> P

class Affine [BI PROP] (P : PROP) : Prop where
  affine : P ⊢ emp

class Absorbing [BI PROP] (P : PROP) : Prop where
  absorbing : <absorb> P ⊢ P

end Iris.BI
