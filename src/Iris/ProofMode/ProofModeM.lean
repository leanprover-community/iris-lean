/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Zongyuan Liu
-/
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

structure ProofModeM.State where
  goals : Array MVarId := #[]

abbrev ProofModeM := StateRefT ProofModeM.State TacticM

/-
Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
whole monad stack at every use site. May eventually be covered by `deriving`.
-/
@[always_inline]
instance : Monad ProofModeM :=
  let i := inferInstanceAs (Monad ProofModeM)
  { pure := i.pure, bind := i.bind }

instance : Inhabited (ProofModeM α) where
  default := throw default

/-- Create a new BI goal with the given hypotheses and goal, and add it to the proof mode state. -/
def addBIGoal {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (goal : Q($prop)) (name : Name := .anonymous) : ProofModeM Q($e ⊢ $goal) := do
  let m : Q($e ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal, .. }
  m.mvarId!.setUserName name
  modify ({goals := ·.goals.push m.mvarId!})
  pure m

/-- Add an existing metavariable as a goal to the proof mode state if it is not already assigned or present. -/
def addMVarGoal (m : MVarId) (name : Name := .anonymous) : ProofModeM Unit := do
  if ← m.isAssignedOrDelayedAssigned then
    return
  if (← getThe ProofModeM.State).goals.contains m then
    return
  -- don't override an existing name, e.g. for ?_
  if !name.isAnonymous then
    m.setUserName name
  modify ({goals := ·.goals.push m})

/-- Try to synthesize a typeclass instance, adding any created metavariables as proof mode goals. -/
def ProofModeM.trySynthInstanceQ (α : Q(Sort v)) : ProofModeM (Option Q($α)) := do
  let LOption.some (e, mvars) ← ProofMode.trySynthInstance α | return none
  mvars.forM addMVarGoal
  return some e

/-- Synthesize a typeclass instance, adding any created metavariables as proof mode goals. -/
def ProofModeM.synthInstanceQ (α : Q(Sort v)) : ProofModeM Q($α) := do
  let (e, mvars) ← ProofMode.synthInstance α
  mvars.forM addMVarGoal
  return e

/-- Initialize proof mode for a metavariable, converting it to an Iris goal. -/
def startProofMode (mvar : MVarId) : MetaM (MVarId × IrisGoal) := mvar.withContext do
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
  let .some (_, mvars) ← ProofMode.trySynthInstanceQ q(AsEmpValid .from $goal $P) | throwError "istart: {goal} is not an emp valid"
  if !mvars.isEmpty then throwError "istart does not support creating mvars"

  let irisGoal := { u, prop, bi, hyps := .mkEmp bi, goal := P, .. }
  let subgoal : Quoted q(⊢ $P) ←
    mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) (← mvar.getTag)
  mvar.assign q(asEmpValid_2 $goal $subgoal)
  pure (subgoal.mvarId!, irisGoal)

/-- Run a ProofModeM computation on the main goal, ordering resulting goals with dependencies last. -/
def ProofModeM.runTactic (x : MVarId → IrisGoal → ProofModeM α) (s : ProofModeM.State := {}) : TacticM α := do
  let (mvar, g) ← startProofMode (← getMainGoal)
  mvar.withContext do

  let (res, {goals}) ← StateRefT'.run (x mvar g) s

  -- make sure to synthesize everything postponed
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)

  -- put the goals that depend on other goals last
  let dependees ← goals.foldlM (λ m g => do
    return m ∪ (← g.getMVarDependencies)) ∅
  let (dep, nonDep) := goals.partition dependees.contains

  replaceMainGoal (nonDep ++ dep).toList
  return res
