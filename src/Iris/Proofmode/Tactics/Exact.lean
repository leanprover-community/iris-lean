/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.Proofmode.Tactics.Basic
import Iris.Proofmode.Tactics.Remove

namespace Iris.Proofmode
open Lean Elab Tactic Meta Qq BI Std

elab "iexact" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
  let some ⟨hyps', _, out, p, _, pf⟩ := hyps.remove bi true name | throwError "unknown hypothesis"

  let _ ← synthInstanceQ q(FromAssumption $p $out $goal)
  let _ ← synthInstanceQ q(TCOr (Affine $hyps'.strip) (Absorbing $goal))

  mvar.assign q(assumption (Q := $goal) $pf)
  replaceMainGoal []
