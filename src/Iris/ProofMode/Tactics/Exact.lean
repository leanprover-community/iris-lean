/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

elab "iexact" colGt hyp:ident : tactic => do
  -- find hypothesis index
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
  let uniq ← hyps.findWithInfo hyp
  let ⟨e', _, _, out, p, _, pf⟩ := hyps.remove true uniq

  let _ ← synthInstanceQ q(FromAssumption $p $out $goal)
  let _ ← synthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))

  mvar.assign q(assumption (Q := $goal) ($pf).mp)
  replaceMainGoal []
