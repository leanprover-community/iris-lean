/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Zongyuan Liu, Yunsong Yang
-/
module

public meta import Iris.ProofMode.Expr
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesInit

public meta section

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

structure ProofModeM.State where
  goals : Array MVarId := #[]

abbrev ProofModeM := StateRefT ProofModeM.State TacticM

structure ProofModeM.SavedState where
  tactic : Tactic.SavedState
  ipmState : State

def ProofModeM.SavedState.restore (b : SavedState) (restoreInfo := false) : ProofModeM Unit := do
  b.tactic.restore restoreInfo
  set b.ipmState

protected def ProofModeM.saveState : ProofModeM SavedState :=
  return { tactic := (← Tactic.saveState), ipmState := (← get) }

instance : MonadBacktrack ProofModeM.SavedState ProofModeM where
  saveState := ProofModeM.saveState
  restoreState b := b.restore

/-
Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
whole monad stack at every use site. May eventually be covered by `deriving`.
-/
@[always_inline]
instance : Monad ProofModeM :=
  letI i : Monad ProofModeM := inferInstance
  { pure := i.pure, bind := i.bind }

instance : Inhabited (ProofModeM α) where
  default := throw default

/-- Create a new BI goal without registering it in the proof mode state. -/
def mkBIGoal {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (goal : Q($prop)) (name : Name := .anonymous) : ProofModeM Q($e ⊢ $goal) := do
  let m : Q($e ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal, .. }
  m.mvarId!.setUserName name
  pure m

/-- Create a new BI goal with the given hypotheses and goal, and add it to the proof mode state. -/
def addBIGoal {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (goal : Q($prop)) (name : Name := .anonymous) : ProofModeM Q($e ⊢ $goal) := do
  let m ← mkBIGoal hyps goal name
  modify ({goals := ·.goals.push m.mvarId!})
  pure m

/-- Run `k` in a context where `fvarIds` are removed from the context.
The user should check whether the fvars can be cleared using `Hyps.checkRemovableFVar`.
TODO: calling this function requires specifying `u`. Not clear why.
-/
def withoutFVars {α : Q(Sort u)} (fvarIds : Array FVarId) (k : ProofModeM Q($α)) :
  ProofModeM Q($α) := do
  -- TODO: Is there a better way of doing this that does not require
  -- creating an mvar, using another function than MVarId.clear?
  let m := (← mkFreshExprSyntheticOpaqueMVar α).mvarId!
  let expr ← m.withContext do
    -- see Lean.MVarId.tryClearMany'
    -- sort to ensure that the fvars can be given in an arbitrary order
    let fvarIds := (← getLCtx).sortFVarsByContextOrder fvarIds
    let m ← fvarIds.foldrM (init := m) (λ h m => m.clear h)
    m.withContext k
  m.assign expr
  return expr

/-- Create a new BI goal with the given hypotheses and goal, but without some fvars, and add it to the proof mode state.
It is the responsibility of the user of this function to check that the variables to clear can actually be cleared (e.g. using
`Hyps.checkRemovableFVar`). -/
def addBIGoalWithoutFVars {prop : Q(Type u)} {bi : Q(BI $prop)}
  {e} (hyps : Hyps bi e) (goal : Q($prop)) (toClear : Array FVarId) (name : Name := .anonymous) : ProofModeM Q($e ⊢ $goal) := do
  withoutFVars (u:=0) toClear (addBIGoal hyps goal name)

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

/--
  Create a new proof goal with the hypotheses `hyps` and the conclusion `goal`,
  run a tactic (`tac`) and add all resultant subgoals into the proof state.
  If the tactic fails, add the proof goal directly.
-/
def addBIGoalRunTactic {u} {prop : Q(Type u)} {bi} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (tac : ProofModeM <| TSyntax `tactic) :
    ProofModeM Q($e ⊢ $goal) := do
  let mvar ← mkBIGoal hyps goal
  let gs ← (observing? <| evalTacticAt (← tac) mvar.mvarId!) <&> (·.getD [mvar.mvarId!])
  if !gs.isEmpty then
    for g in gs do addMVarGoal g
  return mvar

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
  let .some (_, mvars) ← ProofMode.trySynthInstanceQ q(AsEmpValid .from $goal .out $prop .out $bi $P)
    | throwError "istart: {goal} is not an emp valid"
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
