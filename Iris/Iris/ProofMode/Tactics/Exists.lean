/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module -- shake: keep-all

public import Iris.Init -- shake: keep
public import Iris.BI -- shake: keep
public import Iris.ProofMode.Classes -- shake: keep
public import Iris.ProofMode.ProofModeM -- shake: keep

namespace Iris.ProofMode

public section
open BI

@[rocq_alias tac_exist]
theorem from_exists_intro [BI PROP] {Φ : α → PROP} {P Q : PROP} [inst : FromExists P Φ]
    (a : α) (h : P ⊢ Q) : Φ a ⊢ Q := calc
  _ ⊢ ∃ a, Φ a := exists_intro a
  _ ⊢ P := inst.from_exists
  _ ⊢ Q := h

public meta section
open Lean Elab Tactic Meta Qq

/--
  `iexists x₁, …, xₙ` instantiates existential quantifiers in the goal with
  the terms `x₁, …, xₙ`. For each term, one can also use named metavariables
  `?m` or holes (`_`) for unnamed metavariables.
-/
elab "iexists " xs:term,+ : tactic => do
  -- resolve existential quantifier with the given argument
  ProofModeM.runTactic `iexists λ mvar { prop, e, hyps, goal, .. } => do

    let mut new_goal_and_pf : ((g : Q($prop)) × Q($g ⊢ $goal)) := ⟨goal, q(.rfl)⟩

    for x in xs.getElems do
      have new_goal : Q($prop) := new_goal_and_pf.1
      let new_goal_pf : Q($new_goal ⊢ $goal) := new_goal_and_pf.2
      let v ← mkFreshLevelMVar
      let α ← mkFreshExprMVarQ q(Sort v)
      let Φ ← mkFreshExprMVarQ q($α → $prop)
      let some _ ← ProofModeM.trySynthInstanceQ q(FromExists $(new_goal) $Φ)
        | throwIPMError "cannot turn {new_goal} into an existential quantifier"
      let x ← elabTermEnsuringTypeQ (u := .succ .zero) x α
      let newMVarIds ← getMVarsNoDelayed x
      for mvar in newMVarIds do addMVarGoal mvar
      let new_goal' : Q($prop) := Expr.headBeta q($Φ $x)
      let new_goal_pf' : Q($Φ $x ⊢ $goal) := q(from_exists_intro _ $(new_goal_pf))
      new_goal_and_pf := ⟨new_goal', new_goal_pf'⟩

    let m : Q($e ⊢ $(new_goal_and_pf.1)) ← addBIGoal hyps new_goal_and_pf.1
    mvar.assign q($(m).trans $(new_goal_and_pf.2))
