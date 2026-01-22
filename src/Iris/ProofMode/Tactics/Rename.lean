/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Qq

elab "irename" colGt nameFrom:ident " => " colGt nameTo:ident : tactic => do
  ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do

  -- find hypothesis index
  let some (uniq, _, ty) := hyps.find? nameFrom.getId | throwError "irename: unknown hypothesis"
  addHypInfo nameFrom nameFrom.getId uniq prop ty
  let some hyps' := hyps.rename uniq nameTo.getId | unreachable!
  addHypInfo nameTo nameTo.getId uniq prop ty (isBinder := true)

  mvar.setType (IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. })
  addMVarGoal mvar

elab "irename" ":" colGt ty:term " => " colGt nameTo:ident : tactic => do
  -- parse syntax
  if nameTo.getId.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do

  let ty ← elabTerm ty prop
  let (uniq, _, ty) ← try Hyps.select ty hyps catch _ => throwError "irename: unknown hypothesis"
  let some hyps' := hyps.rename uniq nameTo.getId | unreachable!
  addHypInfo nameTo nameTo.getId uniq prop ty (isBinder := true)

  mvar.setType (IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. })
  addMVarGoal mvar
