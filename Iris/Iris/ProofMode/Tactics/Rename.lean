/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Qq

/--
  `irename H => H'` renames the hypothesis `H` as `H'`.
-/
elab "irename" colGt nameFrom:ident " => " colGt nameTo:ident : tactic => do
  ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do

  -- find hypothesis index
  let some (ivar, ty) := hyps.find? nameFrom.getId | throwError "irename: unknown hypothesis"
  addHypInfo nameFrom nameFrom.getId ivar prop ty
  let some hyps' := hyps.rename ivar nameTo.getId | unreachable!
  addHypInfo nameTo nameTo.getId ivar prop ty (isBinder := true)

  mvar.setType (IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. })
  addMVarGoal mvar

/--
  `irename: ty => H'` renames the hypothesis whose statement matches `ty` as `H`.
-/
elab "irename" ":" colGt ty:term " => " colGt nameTo:ident : tactic => do
  -- parse syntax
  if nameTo.getId.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do

  let ty ← elabTerm ty prop
  let (ivar, _, ty) ← try Hyps.select ty hyps catch _ => throwError "irename: unknown hypothesis"
  let some hyps' := hyps.rename ivar nameTo.getId | unreachable!
  addHypInfo nameTo nameTo.getId ivar prop ty (isBinder := true)

  mvar.setType (IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. })
  addMVarGoal mvar
