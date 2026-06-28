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

elab "iaccu" : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    if !goal.isMVar then
      throwError m!"iaccu: {goal} is not a metavariable"

    let ⟨spatial, pf⟩ := hyps.buildAccuProof

    let defEq ← isDefEq goal spatial
    if !defEq then
      throwError "iaccu: could not assign goal metavariable to {spatial}"

    mvar.assign pf
