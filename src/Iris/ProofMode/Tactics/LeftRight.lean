/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI Std

theorem from_or_l [BI PROP] {P Q A1 A2 : PROP} [inst : FromOr Q A1 A2]
    (h1 : P ⊢ A1) : P ⊢ Q :=
  (or_intro_l' h1).trans inst.1

elab "ileft" : tactic => do
  let (mvar, { u, prop, bi, e, hyps, goal }) ← istart (← getMainGoal)
  mvar.withContext do
  let gs ← Goals.new bi

  -- choose left side of disjunction
  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let some _ ← ProofMode.trySynthInstanceQAddingGoals gs q(FromOr $goal $A1 $A2)
    | throwError "ileft: {goal} is not a disjunction"

  let m : Q($e ⊢ $A1) ← gs.addGoal hyps A1
  mvar.assign q(from_or_l (Q := $goal) $m)
  replaceMainGoal (← gs.getGoals)

theorem from_or_r [BI PROP] {P Q A1 A2 : PROP} [inst : FromOr Q A1 A2]
    (h1 : P ⊢ A2) : P ⊢ Q :=
  (or_intro_r' h1).trans inst.1

elab "iright" : tactic => do
  let (mvar, { u, prop, bi, e, hyps, goal }) ← istart (← getMainGoal)
  mvar.withContext do
  let gs ← Goals.new bi

  -- choose right side of disjunction
  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let some _ ← ProofMode.trySynthInstanceQAddingGoals gs q(FromOr $goal $A1 $A2)
    | throwError "ileft: {goal} is not a disjunction"
  let m : Q($e ⊢ $A2) ← gs.addGoal hyps A2
  mvar.assign q(from_or_r (Q := $goal) $m)
  replaceMainGoal (← gs.getGoals)
