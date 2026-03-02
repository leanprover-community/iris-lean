/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

public meta import Iris.ProofMode.Expr
public import Iris.ProofMode.Classes
public meta import Iris.ProofMode.ProofModeM
public meta import Iris.ProofMode.SynthInstance

public meta section

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI Std

def iSolveSideconditionAt (m : MVarId) : ProofModeM Unit := do
  let gs ← evalTacticAt (← `(tactic | trivial)) m
  if !gs.isEmpty then
    throwError "isolvesidecondition: failed to solve sidecondition {← m.getType}"

elab "istart" : tactic => do
  let (mvar, _) ← startProofMode (← getMainGoal)
  replaceMainGoal [mvar]

elab "istop" : tactic => do
  -- parse goal
  let mvar ← getMainGoal
  mvar.withContext do
  let goal ← instantiateMVars <| ← mvar.getType

  -- check if already in proof mode
  let some irisGoal := parseIrisGoal? goal | throwError "not in proof mode"
  mvar.setType irisGoal.strip
