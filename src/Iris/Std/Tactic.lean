import Lean.Elab.Tactic
import Lean.Meta.Tactic.Util

namespace Iris.Std
open Lean Lean.Elab.Tactic Lean.Meta

def apply' (goal : MVarId) (name : Name) : TacticM <| Option <| List MVarId := do
  let some ci := (← getEnv).find? name
    | return none
  let some value := ci.value?
    | return none

  let goals ← withoutRecover <| withReducible <| goal.apply value ⟨.nonDependentOnly⟩
  setGoals <| goals ++ (← getUnsolvedGoals)
  return goals

def findGoalFromTag? (tag : Name) : TacticM <| Option MVarId := do
  (← getUnsolvedGoals).findM? fun goal => do return (← goal.getTag) == tag

def withFocus (goal : MVarId) (f : TacticM α) : TacticM α := do
  let goals ← getUnsolvedGoals
  setGoals [goal]
  let result ← f
  setGoals <| goals ++ (← getUnsolvedGoals)
  return result

end Iris.Std
