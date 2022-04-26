import Iris.BI
import Iris.Proofmode.Classes
import Iris.Proofmode.Environments

namespace Iris.Proofmode
open Iris.BI

variable [BI PROP]

-- proof mode
theorem tac_start (P : PROP) : envs_entails ⟨[], []⟩ P → ⊢ P := sorry

end Iris.Proofmode
