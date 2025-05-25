/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI.Classes
import Iris.BI.BI

namespace Iris.BI

class Plainly (PROP : Type _) where
  plainly : PROP → PROP

end Iris.BI
