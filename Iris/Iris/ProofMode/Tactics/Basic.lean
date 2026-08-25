/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

public import Iris.ProofMode.Classes
public import Iris.ProofMode.Expr
public import Iris.ProofMode.SynthInstance
public import Iris.ProofMode.ProofModeM

public section

#rocq_ignore tac_start "Functionality already handled by ProofModeM infrastructure"
#rocq_ignore tac_stop "Functionality already handled by ProofModeM infrastructure"

public meta section

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI Std Lean.Elab Term

/-- `itrivial` collects tactics to solve trivial Iris goals. It is used by the `//` specialization
and introduction patterns. One can add new tactics using
```
macro_rules | `(tactic| itrivial) => `(tactic| mytac)
```
-/
syntax "itrivial" : tactic

/--
  `istart` starts the Iris Proof Mode.
-/
elab "istart" : tactic => do
  let (mvar, _) ← startProofMode (← getMainGoal)
  replaceMainGoal [mvar]

/--
  `istart prop` starts the Iris Proof Mode with a specific BI instance.
-/
elab "istart " colGt prop:term : tactic => do
  let mvar ← getMainGoal
  let customProp ← mvar.withContext do elabType prop >>= (instantiateMVars ·)
  let (mvar, _) ← startProofMode mvar (some customProp)
  replaceMainGoal [mvar]

/--
  `istop` stops the Iris Proof Mode by turning the goal back
  into plain entailment.
-/
elab "istop" : tactic => do
  -- parse goal
  let mvar ← getMainGoal
  mvar.withContext do
    let goal ← instantiateMVars <| ← mvar.getType

    -- check if already in proof mode
    let some irisGoal := parseIrisGoal? goal | throwError "istop: not in proof mode"
    mvar.setType irisGoal.strip

-- TODO: Is there a more efficient way to implement this?
elab "focusLastIrisGoal" colGt tac:tactic : tactic => do
  let goals ← getUnsolvedGoals
  let mut goals_before := []
  let mut iris_goal := []
  let mut goals_after := []
  for g in goals do
    if isIrisGoal (← g.getType) then
      goals_before := goals_before ++ iris_goal ++ goals_after
      iris_goal := [g]
      goals_after := []
    else
      goals_after := goals_after ++ [g]
  let [g] := iris_goal
    | throwError "no remaining Iris goal"
  setGoals [g]
  evalTactic tac
  let goals' ← getUnsolvedGoals
  setGoals (goals_before ++ goals' ++ goals_after)
