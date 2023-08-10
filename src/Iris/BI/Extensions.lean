/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Classes
import Iris.BI.BI

namespace Iris.BI

/-- Require that a separation logic with the carrier type `PROP` is an affine separation logic. -/
class BIAffine (PROP : Type) extends BI PROP where
  affine (P : PROP) : Affine P

attribute [instance (default + 100)] BIAffine.affine

end Iris.BI
