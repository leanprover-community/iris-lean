/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes

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
  let _ ← synthInstanceQ q(ProofMode.AsEmpValid2 $goal $P)

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

theorem assumption [BI PROP] {p : Bool} {P P' A Q : PROP} [inst : FromAssumption p A Q]
  [TCOr (Affine P') (Absorbing Q)] (h : P ⊣⊢ P' ∗ □?p A) : P ⊢ Q :=
  h.1.trans <| (sep_mono_r inst.1).trans sep_elim_r

def binderIdentHasName (name : Name) (id : TSyntax ``binderIdent) : Bool :=
  match id with
  | `(binderIdent| $name':ident) => name'.getId == name
  | _ => false

def selectHyp (ty : Expr) : ∀ {s}, @Hyps u prop bi s → MetaM (Name × Q(Bool) × Q($prop))
  | _, .emp _ => failure
  | _, .hyp _ _ uniq p ty' _ => do
    let .true ← isDefEq ty ty' | failure
    pure (uniq, p, ty')
  | _, .sep _ _ _ _ lhs rhs => try selectHyp ty rhs catch _ => selectHyp ty lhs

structure Goals {prop : Q(Type u)} (bi : Q(BI $prop)) where
  goals : IO.Ref (Array MVarId)

def Goals.new {prop : Q(Type u)} (bi : Q(BI $prop)) : BaseIO (Goals bi) :=
  do return { goals := ← IO.mkRef #[] }

def Goals.addGoal {prop : Q(Type u)} {bi : Q(BI $prop)} (g : Goals bi)
    {e} (hyps : Hyps bi e) (goal : Q($prop)) (name : Name := .anonymous) : MetaM Q($e ⊢ $goal) := do
  let m : Q($e ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal, .. }
  m.mvarId!.setUserName name
  g.goals.modify (·.push m.mvarId!)
  pure m

def Goals.addPureGoal {prop : Q(Type u)} {bi : Q(BI $prop)} (g : Goals bi)
    (m : MVarId) (name : Name := .anonymous) : MetaM Unit := do
  -- don't override an existing name, e.g. for ?_
  if !name.isAnonymous then
    m.setUserName name
  g.goals.modify (·.push m)

def Goals.getGoals {prop : Q(Type u)} {bi : Q(BI $prop)} (g : Goals bi) : MetaM (List MVarId) := do
  let goals ← g.goals.get
  -- put the goals that depend on other goals last
  let mvars ← goals.foldlM (λ m g => do
    return m ∪ (← g.getMVarDependencies)) ∅
  let (dep, nonDep) := goals.partition (λ x => mvars.contains x)
  return (nonDep ++ dep).toList
