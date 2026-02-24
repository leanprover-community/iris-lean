/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI

private theorem exists_intro' [BI PROP] {Φ : α → PROP} {P Q : PROP} [inst : FromExists P Φ]
    (a : α) (h : P ⊢ Q) : Φ a ⊢ Q :=
  ((exists_intro a).trans inst.1).trans h

elab "iexists" xs:term,+ : tactic => do
  -- resolve existential quantifier with the given argument
  ProofModeM.runTactic λ mvar { prop, e, hyps, goal, .. } => do

  let mut new_goal_and_pf : ((g : Q($prop)) × Q($g ⊢ $goal)) := ⟨goal, q(.rfl)⟩

  for x in xs.getElems do
    have new_goal : Q($prop) := new_goal_and_pf.1
    let new_goal_pf : Q($new_goal ⊢ $goal) := new_goal_and_pf.2
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVarQ q(Sort v)
    let Φ ← mkFreshExprMVarQ q($α → $prop)
    let some _ ← ProofModeM.trySynthInstanceQ q(FromExists $(new_goal) $Φ)
      | throwError "iexists: cannot turn {new_goal} into an existential quantifier"
    let x ← elabTermEnsuringTypeQ (u := .succ .zero) x α
    let newMVarIds ← getMVarsNoDelayed x
    for mvar in newMVarIds do addMVarGoal mvar
    let new_goal' : Q($prop) := Expr.headBeta q($Φ $x)
    let new_goal_pf' : Q($Φ $x ⊢ $goal) := q(exists_intro' _ $(new_goal_pf))
    new_goal_and_pf := ⟨new_goal', new_goal_pf'⟩

  let m : Q($e ⊢ $(new_goal_and_pf.1)) ← addBIGoal hyps new_goal_and_pf.1
  mvar.assign q($(m).trans $(new_goal_and_pf.2))
