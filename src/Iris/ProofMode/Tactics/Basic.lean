/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes
import Iris.ProofMode.Goals
import Iris.ProofMode.SynthInstance

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI Std

def istart (mvar : MVarId) : MetaM (MVarId × IrisGoal) := mvar.withContext do
  -- parse goal
  let goal ← instantiateMVars <| ← mvar.getType

  -- check if already in proof mode
  if let some irisGoal := parseIrisGoal? goal then
    return (mvar, irisGoal)

  let some goal ← checkTypeQ goal q(Prop)
    | throwError "type mismatch\n{← mkHasTypeButIsExpectedMsg (← inferType goal) q(Prop)}"
  let u ← mkFreshLevelMVar
  let prop ← mkFreshExprMVarQ q(Type u)
  let P ← mkFreshExprMVarQ q($prop)
  let bi ← mkFreshExprMVarQ q(BI $prop)
  let _ ← synthInstanceQ q(ProofMode.AsEmpValid .from $goal $P)

  let irisGoal := { u, prop, bi, hyps := .mkEmp bi, goal := P, .. }
  let subgoal : Quoted q(⊢ $P) ←
    mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) (← mvar.getTag)
  mvar.assign q(ProofMode.as_emp_valid_2 $goal $subgoal)
  pure (subgoal.mvarId!, irisGoal)

elab "istart" : tactic => do
  let (mvar, _) ← istart (← getMainGoal)
  replaceMainGoal [mvar]

elab "istop" : tactic => do
  -- parse goal
  let mvar ← getMainGoal
  mvar.withContext do
  let goal ← instantiateMVars <| ← mvar.getType

  -- check if already in proof mode
  let some irisGoal := parseIrisGoal? goal | throwError "not in proof mode"
  mvar.setType irisGoal.strip

def selectHyp (ty : Expr) : ∀ {s}, @Hyps u prop bi s → MetaM (Name × Q(Bool) × Q($prop))
  | _, .emp _ => failure
  | _, .hyp _ _ uniq p ty' _ => do
    let .true ← isDefEq ty ty' | failure
    pure (uniq, p, ty')
  | _, .sep _ _ _ _ lhs rhs => try selectHyp ty rhs catch _ => selectHyp ty lhs
