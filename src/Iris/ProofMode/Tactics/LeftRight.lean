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
  ProofModeM.runTactic λ mvar { prop, e, hyps, goal, .. } => do
  -- choose left side of disjunction
  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let some _ ← ProofModeM.trySynthInstanceQ q(FromOr $goal $A1 $A2)
    | throwError "ileft: {goal} is not a disjunction"

  let m : Q($e ⊢ $A1) ← addBIGoal hyps A1
  mvar.assign q(from_or_l (Q := $goal) $m)

theorem from_or_r [BI PROP] {P Q A1 A2 : PROP} [inst : FromOr Q A1 A2]
    (h1 : P ⊢ A2) : P ⊢ Q :=
  (or_intro_r' h1).trans inst.1

elab "iright" : tactic => do
  ProofModeM.runTactic λ mvar { prop, e, hyps, goal, .. } => do
  -- choose right side of disjunction
  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let some _ ← ProofModeM.trySynthInstanceQ q(FromOr $goal $A1 $A2)
    | throwError "ileft: {goal} is not a disjunction"
  let m : Q($e ⊢ $A2) ← addBIGoal hyps A2
  mvar.assign q(from_or_r (Q := $goal) $m)
