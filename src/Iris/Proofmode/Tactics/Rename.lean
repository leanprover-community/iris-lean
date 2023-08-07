/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.Proofmode.Expr

import Lean.Elab.Tactic

namespace Iris.Proofmode.Internal
open Lean Lean.Elab.Tactic Lean.Meta

def irenameCore (hypIndex : HypothesisIndex) (name : Name) : TacticM Unit := do
  -- parse goal
  let goal ← getMainGoal
  let expr ← instantiateMVars <| ← goal.getType

  let some (Γₚ, Γₛ, _) ← extractEnvsEntails? expr
    | throwError "not in proof mode"

  -- retrieve goal mvar declaration
  let some decl := (← getMCtx).findDecl? goal
    | throwError "ill-formed proof environment"

  let modifyHypothesis (Γ : Expr) (idx : Nat) : TacticM Expr := do
    -- find hypothesis
    let some h ← EnvExpr.get? Γ idx
      | throwError "invalid index or ill-formed proof environment"

    -- check for unique (or equal) hypothesis name
    let nameFrom? := h.getMDataName?
    if nameFrom? |>.map (· != name) |>.getD true then
      if ← [Γₚ, Γₛ].anyM (fun Γ => do return (← EnvExpr.any? Γ (·.getMDataName?.isEqSome name)) matches some true) then
        throwError "name is already used for another hypothesis"

      if decl.lctx.any (·.userName == name) then
        throwError "name is already used in the Lean context"

    -- rename hypothesis
    let h := h.setMDataName? name

    -- re-insert hypothesis
    let some Γ ← EnvExpr.set? Γ h idx
      | throwError "invalid index or ill-formed proof environment"

    return Γ

  -- modify environment
  let (Γₚ, Γₛ) ← match hypIndex with
    | ⟨.intuitionistic, index, _⟩ => do
      pure (← modifyHypothesis Γₚ index, Γₛ)
    | ⟨.spatial, index, _⟩ => do
      pure (Γₚ, ← modifyHypothesis Γₛ index)

  -- update goal
  let some expr ← modifyEnvsEntails? expr Γₚ Γₛ none
    | throwError "ill-formed proof environment"

  goal.setType expr

end Iris.Proofmode.Internal
