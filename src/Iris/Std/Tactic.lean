import Lean.Elab.Tactic
import Lean.Meta.Tactic.Util

namespace Iris.Std
open Lean Lean.Elab.Tactic Lean.Meta

def findGoalFromTag? (tag : Name) : TacticM <| Option MVarId := do
    (← getUnsolvedGoals).findM? (fun goal => do pure <| (← getMVarTag goal) == tag)

end Iris.Std
