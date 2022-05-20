import Iris.BI.Classes
import Iris.BI.Interface

namespace Iris.BI

class BIAffine (car : Type) extends BI car where
  affine (P : car) : Affine P

instance (priority := default + 100) [BIAffine car] (P : car) : Affine P := BIAffine.affine P

end Iris.BI
