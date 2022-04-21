import Iris.BI.Interface

namespace Iris.BI

class BIAffine (car : Type) extends BI car where
  affine (Q : car) : Q ⊢ emp

end Iris.BI
