/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.Proofmode.Expr
import Iris.Proofmode.Classes

namespace Iris.Proofmode
open Lean Elab.Tactic Meta Qq BI Std

def istart (mvar : MVarId) : MetaM (MVarId × IrisGoal) := mvar.withContext do
  -- parse goal
  let goal ← instantiateMVars <| ← mvar.getType

  -- check if already in proof mode
  if let some irisGoal := parseIrisGoal? goal then
    return (mvar, irisGoal)

  let some goal ← checkTypeQ goal q(Prop)
    | throwError "type mismatch\n{← mkHasTypeButIsExpectedMsg (← inferType goal) q(Prop)}"
  let prop ← mkFreshExprMVarQ q(Type)
  let P ← mkFreshExprMVarQ q($prop)
  let bi ← mkFreshExprMVarQ q(BI $prop)
  let _ ← synthInstanceQ q(Proofmode.AsEmpValid2 $goal $P)

  let irisGoal := { prop, bi, hyps := .mkEmp bi, goal := P }
  let subgoal : Quoted q(⊢ $P) ←
    mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) (← mvar.getTag)
  mvar.assign q(Proofmode.as_emp_valid_2 $goal $subgoal)
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

theorem assumption [BI PROP] {p : Bool} {P P' A Q : PROP} [inst : FromAssumption p A Q]
  [TCOr (Affine P') (Absorbing Q)] (h : P ⊣⊢ P' ∗ □?p A) : P ⊢ Q :=
  h.1.trans <| (sep_mono_r inst.1).trans sep_elim_r

def getFreshName : Option Name → CoreM Name
  | none => mkFreshUserName `x
  | some name => pure name
