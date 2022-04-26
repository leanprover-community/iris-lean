import Iris.BI
import Iris.Proofmode.Init

import Lean

namespace Iris.Proofmode
open Iris.BI

attribute [pm_simp] bigOp

attribute [pm_simp] List.concat
attribute [pm_simp] List.foldl1
attribute [pm_simp] List.foldr1

-- TODO use `pm_simp` (available with `nightly-2022-04-26`)
macro "pmReduce" : tactic => `(tactic| simp only [bigOp, List.concat, List.foldl1, List.foldr1])

end Iris.Proofmode
