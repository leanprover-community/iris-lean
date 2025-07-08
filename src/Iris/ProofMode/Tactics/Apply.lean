/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

-- focus on n = 1 case for now

elab "iapply" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { u, prop, bi, e, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
    let uniq ← hyps.findWithInfo hyp
    let ⟨e', hyps, out, out', p, eq, pf⟩ := hyps.remove true uniq

    -- todo
    --let A ← mkFreshExprMVarQ q($prop)



    let _ ← synthInstanceQ q(FromAssumption $p $out' $goal)
    let _ ← synthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))

    --let m : Q($e ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    --  IrisGoal.toExpr { prop, bi, hyps, goal, .. }
    --

    mvar.assign q(assumption (Q := $goal) $pf)
    replaceMainGoal []
