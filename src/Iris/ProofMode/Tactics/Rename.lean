/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes
import Iris.Std
import Lean.Elab

namespace Iris.ProofMode
open Lean Elab Tactic Qq

variable (old new : Name) {prop : Q(Type)} {bi : Q(BI $prop)} in
def Hyps.rename : ∀ {e}, Hyps bi e → Option (Hyps bi e)
  | _, .emp _ => none
  | _, .sep _ _ _ _ lhs rhs =>
    match rhs.rename with
    | some rhs' => some (.mkSep lhs rhs' _)
    | none => match lhs.rename with
      | some lhs' => some (.mkSep lhs' rhs _)
      | none => none
  | _, .hyp _ name p ty _ => if old == name then some (Hyps.mkHyp bi new p ty _) else none

elab "irename" colGt nameFrom:ident " => " colGt nameTo:ident : tactic => do
  -- parse syntax
  if nameFrom.getId.isAnonymous || nameTo.getId.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let some hyps' := hyps.rename nameFrom.getId nameTo.getId | throwError "unknown hypothesis"

  mvar.setType (IrisGoal.toExpr { prop, bi, hyps := hyps', goal })
