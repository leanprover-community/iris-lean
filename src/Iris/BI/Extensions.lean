import Iris.BI.Classes
import Iris.BI.Interface

namespace Iris.BI

/-- Require that a separation logic with the carrier type `car` is an affine separation logic. -/
class BIAffine (car : Type) extends BI car where
  affine (P : car) : Affine P

attribute [instance (default + 100)] BIAffine.affine

end Iris.BI
