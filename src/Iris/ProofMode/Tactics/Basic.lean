/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes
import Iris.ProofMode.ProofModeM
import Iris.ProofMode.SynthInstance

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI Std

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
