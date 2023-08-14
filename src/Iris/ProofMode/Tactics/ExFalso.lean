/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Expr

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI

theorem exfalso [BI PROP] {P Q : PROP} (h : P ⊢ False) : P ⊢ Q := h.trans false_elim

elab "iexfalso" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, e, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let m : Q($e ⊢ False) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, e, hyps, goal := q(iprop(False)) }
  mvar.assign q(exfalso (Q := $goal) $m)
  replaceMainGoal [m.mvarId!]
