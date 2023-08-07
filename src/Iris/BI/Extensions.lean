/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Classes
import Iris.BI.Interface

namespace Iris.BI

/-- Require that a separation logic with the carrier type `car` is an affine separation logic. -/
class BIAffine (car : Type) extends BI car where
  affine (P : car) : Affine P

attribute [instance (default + 100)] BIAffine.affine

end Iris.BI
