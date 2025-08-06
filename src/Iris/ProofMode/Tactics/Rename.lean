/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes
import Iris.ProofMode.Tactics.Basic
import Iris.Std
import Lean.Elab

namespace Iris.ProofMode
open Lean Elab Tactic Qq

variable (oldUniq new : Name) {prop : Q(Type u)} {bi : Q(BI $prop)} in
def Hyps.rename : ∀ {e}, Hyps bi e → Option (Hyps bi e)
  | _, .emp _ => none
  | _, .sep _ _ _ _ lhs rhs =>
    match rhs.rename with
    | some rhs' => some (.mkSep lhs rhs' _)
    | none => match lhs.rename with
      | some lhs' => some (.mkSep lhs' rhs _)
      | none => none
  | _, .hyp _ _ uniq p ty _ =>
    if oldUniq == uniq then some (Hyps.mkHyp bi new uniq p ty _) else none

elab "irename" colGt nameFrom:ident " => " colGt nameTo:ident : tactic => do
  -- find hypothesis index
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

  let some (uniq, _, ty) := hyps.find? (fun n _ => n == nameFrom.getId) | throwError "unknown hypothesis"
  addHypInfo nameFrom nameFrom.getId uniq prop ty
  let some hyps' := hyps.rename uniq nameTo.getId | unreachable!
  addHypInfo nameTo nameTo.getId uniq prop ty (isBinder := true)

  mvar.setType (IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. })

elab "irename" ":" colGt ty:term " => " colGt nameTo:ident : tactic => do
  -- parse syntax
  if nameTo.getId.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

  let ty ← elabTerm ty prop
  let (uniq, _, ty) ← try selectHyp ty hyps catch _ => throwError "unknown hypothesis"
  let some hyps' := hyps.rename uniq nameTo.getId | unreachable!
  addHypInfo nameTo nameTo.getId uniq prop ty (isBinder := true)

  mvar.setType (IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. })
