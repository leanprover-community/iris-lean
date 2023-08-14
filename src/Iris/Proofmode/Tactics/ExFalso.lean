/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.Proofmode.Expr

namespace Iris.Proofmode
open Lean Elab.Tactic Meta Qq BI

theorem exfalso [BI PROP] {P Q : PROP} (h : P ⊢ False) : P ⊢ Q := h.trans false_elim

elab "iexfalso" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  have ehyps := hyps.strip
  let m : Q($ehyps ⊢ False) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal := q(iprop(False)) }
  mvar.assign q(exfalso (Q := $goal) $m)
  replaceMainGoal [m.mvarId!]
