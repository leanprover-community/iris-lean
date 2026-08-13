/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module -- shake: keep-all

public import Iris.Init -- shake: keep
public import Iris.ProofMode.ProofModeM -- shake: keep

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq

/--
  Given that the proof goal is a metavariable, `iaccu` combines all hypotheses
  in the spatial context with the separating conjunction and solves the proof
  goal by unifying the metavariable with the combined proposition.
-/
elab "iaccu" : tactic => do
  ProofModeM.runTactic `iaccu λ mvar { hyps, goal, .. } => do
    unless goal.isMVar do
      throwIPMError "{goal} is not a metavariable"

    let ⟨spatial, pf⟩ := hyps.buildAccuProof

    -- Assign and unify the metavariable
    unless ← isDefEq goal spatial do
      throwIPMError "could not assign goal metavariable to {spatial}"

    mvar.assign pf

#rocq_ignore tac_accu "Using infrastructure provided by Expr.lean to build the proof"
