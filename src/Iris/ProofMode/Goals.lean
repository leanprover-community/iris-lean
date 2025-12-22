/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Expr

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

structure Goals {prop : Q(Type u)} (bi : Q(BI $prop)) where
  goals : IO.Ref (Array MVarId)

def Goals.new {prop : Q(Type u)} (bi : Q(BI $prop)) : BaseIO (Goals bi) :=
  do return {goals := ← IO.mkRef #[]}

def Goals.addGoal {prop : Q(Type u)} {bi : Q(BI $prop)} (g : Goals bi)
    {e} (hyps : Hyps bi e) (goal : Q($prop)) (name : Name := .anonymous) : MetaM Q($e ⊢ $goal) := do
  let m : Q($e ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal, .. }
  m.mvarId!.setUserName name
  g.goals.modify (·.push m.mvarId!)
  pure m

def Goals.addPureGoal {prop : Q(Type u)} {bi : Q(BI $prop)} (g : Goals bi)
    (m : MVarId) (name : Name := .anonymous) : MetaM Unit := do
  if ← m.isAssignedOrDelayedAssigned then
    return
  if (← g.goals.get).contains m then
    return
  -- don't override an existing name, e.g. for ?_
  if !name.isAnonymous then
    m.setUserName name
  g.goals.modify (·.push m)

-- TODO: change this to replace main goal that deduplicates goals
def Goals.getGoals {prop : Q(Type u)} {bi : Q(BI $prop)} (g : Goals bi) : MetaM (List MVarId) := do
  let goals ← g.goals.get
  -- put the goals that depend on other goals last
  let mvars ← goals.foldlM (λ m g => do
    return m ∪ (← g.getMVarDependencies)) ∅
  let (dep, nonDep) := goals.partition (λ x => mvars.contains x)
  return (nonDep ++ dep).toList
