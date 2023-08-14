/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI
import Iris.Proofmode.Expr
import Iris.Proofmode.Classes
import Iris.Std
import Lean.Elab

namespace Iris.Proofmode
open Lean Elab Tactic Qq

variable (old new : Name) {prop : Q(Type)} (bi : Q(BI $prop)) in
def Hyps.rename : Hyps prop → Option (Hyps prop)
  | .emp _ => none
  | .sep _ _ lhs rhs =>
    match rhs.rename with
    | some rhs' => some (.mkSep bi lhs rhs')
    | none => match lhs.rename with
      | some lhs' => some (.mkSep bi lhs' rhs)
      | none => none
  | .hyp _ _ kind name ty => if old == name then some (Hyps.mkHyp bi kind new ty) else none

elab "irename" colGt nameFrom:ident " => " colGt nameTo:ident : tactic => do
  -- parse syntax
  if nameFrom.getId.isAnonymous || nameTo.getId.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let some hyps' := hyps.rename nameFrom.getId nameTo.getId bi
    | throwError "unknown hypothesis"

  mvar.setType (IrisGoal.toExpr { prop, bi, hyps := hyps', goal })
