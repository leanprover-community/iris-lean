import Iris.BI.Classes
import Iris.BI.Interface

namespace Iris.BI

class BIAffine (car : Type) extends BI car where
  affine (P : car) : Affine P

attribute [instance (default + 100)] BIAffine.affine

end Iris.BI
