/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

import Iris.ProofMode.Classes
meta import Iris.ProofMode.Expr
meta import Iris.ProofMode.SynthInstance
public meta import Iris.ProofMode.ProofModeM

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

def iSolveSidecondition (target : Q(Prop)) (failOnUnsolved := true) : ProofModeM Q($target) := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar q($target)
  match ← instantiateMVars target with
  | .app (.const ``PMError _) (.lit (.strVal msg)) =>
      throwError "{msg}"
  | _ =>
      let gs ← evalTacticAt (← `(tactic | trivial)) mvar.mvarId!
      if !gs.isEmpty then
        if failOnUnsolved then
          throwError "isolvesidecondition: failed to solve sidecondition {target}"
        else
          for g in gs do addMVarGoal g
      return mvar

/--
  `istart` starts the Iris Proof Mode.
-/
elab "istart" : tactic => do
  let (mvar, _) ← startProofMode (← getMainGoal)
  replaceMainGoal [mvar]

/--
  `istart prop` starts the Iris Proof Mode with a specific `prop`.
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
  let some irisGoal := parseIrisGoal? goal | throwError "not in proof mode"
  mvar.setType irisGoal.strip
