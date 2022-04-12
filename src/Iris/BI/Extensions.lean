import Iris.BI.Interface

namespace Iris.BI.Extensions
open Iris.BI.Interface

class BIAffine (car : Type) extends BI car where
  affine (Q : car) : Q ⊢ emp

end Iris.BI.Extensions
