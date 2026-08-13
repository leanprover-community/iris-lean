/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module -- shake: keep-all

public import Iris.Init -- shake: keep
public import Iris.ProofMode.ProofModeM -- shake: keep

namespace Iris.ProofMode

public section
open BI

@[rocq_alias tac_or_l]
theorem from_or_left [BI PROP] {P Q A1 A2 : PROP} [inst : FromOr Q A1 A2]
    (h1 : P ⊢ A1) : P ⊢ Q :=
  (or_intro_left_trans h1).trans inst.1

@[rocq_alias tac_or_r]
theorem from_or_right [BI PROP] {P Q A1 A2 : PROP} [inst : FromOr Q A1 A2]
    (h1 : P ⊢ A2) : P ⊢ Q :=
  (or_intro_right_trans h1).trans inst.1

public meta section
open Lean Elab.Tactic Meta Qq Std

/--
  `ileft` choose the left side of the disjunction in the goal.
  Given a goal of the form `P ∨ Q`, the new goal is `P`.
-/
elab "ileft" : tactic => do
  ProofModeM.runTactic `ileft λ mvar { prop, e, hyps, goal, .. } => do
  -- choose left side of disjunction
  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let some _ ← ProofModeM.trySynthInstanceQ q(FromOr $goal $A1 $A2)
    | throwIPMError "{goal} is not a disjunction"

  let m : Q($e ⊢ $A1) ← addBIGoal hyps A1
  mvar.assign q(from_or_left (Q := $goal) $m)

/--
  `iright` choose the right side of the disjunction in the goal.
  Given a goal of the form `P ∨ Q`, the new goal is `Q`.
-/
elab "iright" : tactic => do
  ProofModeM.runTactic `iright λ mvar { prop, e, hyps, goal, .. } => do
  -- choose right side of disjunction
  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let some _ ← ProofModeM.trySynthInstanceQ q(FromOr $goal $A1 $A2)
    | throwIPMError "{goal} is not a disjunction"
  let m : Q($e ⊢ $A2) ← addBIGoal hyps A2
  mvar.assign q(from_or_right (Q := $goal) $m)
