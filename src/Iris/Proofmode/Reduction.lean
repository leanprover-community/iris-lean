import Iris.BI
import Iris.Proofmode.Init

import Lean

namespace Iris.Proofmode
open Iris.BI

attribute [pm_simp] bigOp

attribute [pm_simp] List.concat
attribute [pm_simp] List.foldl1
attribute [pm_simp] List.foldr1

macro "pmReduce" : tactic => `(tactic| simp only [pm_simp])

end Iris.Proofmode
