import Iris.BI
import Iris.Proofmode.Init
import Iris.Std.List

import Lean

namespace Iris.Proofmode
open Iris.BI

attribute [pm_simp] bigOp

attribute [pm_simp] ite_false
attribute [pm_simp] ite_true

attribute [pm_simp] List.concat
attribute [pm_simp] List.foldl1
attribute [pm_simp] List.foldr1

attribute [pm_simp] Prod.map

macro "pmReduce" : tactic => `(tactic| simp only [pm_simp, List.splitWithSortedIndices.go])

end Iris.Proofmode
