import Lean.Elab.Tactic
import Lean.Meta.Tactic.Util

namespace Iris.Std
open Lean Lean.Elab.Tactic Lean.Meta

def findGoalFromTag? (tag : Name) : TacticM <| Option MVarId := do
  (← getUnsolvedGoals).findM? fun goal => do return (← getMVarTag goal) == tag

def withFocus (goal : MVarId) (f : TacticM α) : TacticM α := do
  let goals ← getUnsolvedGoals
  setGoals [goal]
  let result ← f
  setGoals <| goals ++ (← getUnsolvedGoals)
  return result

end Iris.Std
