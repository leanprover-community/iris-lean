/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Assumption
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

elab "iexact" colGt hyp:ident : tactic => do
  let (mvar, { bi, hyps, goal, .. }) ← istart (← getMainGoal)
  mvar.withContext do
  let gs ← Goals.new bi
  let uniq ← hyps.findWithInfo hyp
  let ⟨e', _, _, out, p, _, pf⟩ := hyps.remove true uniq

  let some _ ← ProofMode.trySynthInstanceQAddingGoals gs q(FromAssumption $p $out $goal)
    | throwError "iexact: cannot unify {out} and {goal}"
  let _ ← synthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))

  mvar.assign q(assumption (Q := $goal) $pf)
  replaceMainGoal (← gs.getGoals)
