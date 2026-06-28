/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.ProofModeM

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq

/--
  Given that the proof goal is a metavariable, `iaccu` combines all hypotheses
  in the spatial context with the separating conjunction and solves the proof
  goal by unifying the metavariable with the combined proposition.
-/
elab "iaccu" : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    if !goal.isMVar then
      throwError m!"iaccu: {goal} is not a metavariable"

    let ⟨spatial, pf⟩ := hyps.buildAccuProof

    -- Assign and unify the metavariable
    let defEq ← isDefEq goal spatial
    if !defEq then
      throwError "iaccu: could not assign goal metavariable to {spatial}"

    mvar.assign pf
