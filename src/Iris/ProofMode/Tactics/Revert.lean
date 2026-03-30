/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Yunsong Yang
-/
module

public import Iris.ProofMode.ClassesMake
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open BI Std

theorem wand_revert [BI PROP] {Δ Δ' P Q : PROP}
    (h1 : Δ ⊣⊢ Δ' ∗ P) (h2 : Δ' ⊢ P -∗ Q) : Δ ⊢ Q :=
  h1.mp.trans (wand_elim h2)

theorem forall_revert {α} [BI PROP] {Δ : PROP} {Ψ : α → PROP}
    (h : Δ ⊢ BI.forall Ψ) : ∀ x, Δ ⊢ Ψ x :=
  λ x => h.trans (forall_elim x)

theorem pure_revert [BI PROP] {Δ P Q : PROP} {φ : Prop}
    [hA : MakeAffinely iprop(⌜φ⌝) P]
    (h : Δ ⊢ P -∗ Q) : φ → Δ ⊢ Q := by
  intro hp
  have hA : (emp : PROP) ⊢ P :=
    (affinely_emp.mpr.trans <| affinely_mono <| pure_intro hp).trans (hA.make_affinely.mp)
  exact (sep_emp.mpr.trans (sep_mono .rfl hA)).trans (wand_elim h)

public meta section
open Lean Elab Tactic Meta Qq

/--
  `reverted` collects lean variables already reverted. This is necessary for dependency checks
  since they are only cleared from the Lean context for the final goal.
-/
private structure RevertState {prop : Q(Type u)} (bi : Q(BI $prop)) (origE origGoal : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e) (goal : Q($prop))
  (reverted : Array FVarId := #[])
  pf : Q(($e ⊢ $goal) → ($origE ⊢ $origGoal))

/-- Revert a proofmode hypothesis by turning it into a wand premise. -/
private def RevertState.revertProofModeHyp
    : @RevertState u prop bi origE origGoal → TSyntax `ident →
      ProofModeM (RevertState bi origE origGoal)
  | { hyps, goal, reverted, pf, .. }, hyp => do
    let uniq ← hyps.findWithInfo hyp
    let ⟨e', hyps', out, _, _, _, hΔ⟩ := hyps.remove true uniq
    return { e := e', hyps := hyps', goal := q(wand $out $goal), reverted,
             pf := q(fun h => $pf (wand_revert $hΔ h)) }

/-- Check that reverting the Lean local named by `hyp` will not leave dangling dependencies. -/
private def RevertState.checkLeanDependencies
    : @RevertState u prop bi origE origGoal → TSyntax `ident → MetaM LocalDecl
  | { hyps, reverted, .. }, hyp => do
    let ldecl ← getLocalDeclFromUserName hyp.getId
    let f := ldecl.fvarId
    if let some (name, _, _, _) := hyps.findDependencyOnFVar f then
      throwError "irevert: proofmode hypothesis {name} depends on {hyp.getId}"
    let deps ← collectForwardDeps #[mkFVar f] false
    -- check if there is a dependency on a variable that has not been reverted before
    if let some dep := deps.find? (fun e => e.fvarId! != f && !reverted.contains e.fvarId!) then
      let depDecl := (← getLCtx).getFVar! dep
      throwError "irevert: Lean hypothesis {depDecl.userName} depends on {hyp.getId}"
    return ldecl

/-- Revert a Lean proposition by turning it into the `MakeAffinely` pure premise. -/
private def RevertState.revertLeanPropHyp
    (st : @RevertState u prop bi origE origGoal) (f : FVarId) (φ : Q(Prop)) :
    ProofModeM (RevertState bi origE origGoal) := do
  let { e, hyps, goal, reverted, pf } := st
  let P ← mkFreshExprMVarQ prop
  let _hA : Q(MakeAffinely iprop(⌜$φ⌝) $P) ← synthInstanceQ q(MakeAffinely iprop(⌜$φ⌝) $P)
  let hp : Q($φ) := mkFVar f
  let goal' : Q($prop) := q(iprop($P -∗ $goal))
  let pf' : Q(($e ⊢ $goal') → ($origE ⊢ $origGoal)) := q(fun h => $pf (pure_revert h $hp))
  return { e, hyps, goal := goal', reverted := reverted.push f, pf := pf' }

/-- Revert a Lean non-`Prop` local by turning the current goal into a forall. -/
private def RevertState.revertLeanForallHyp
    (st : @RevertState u prop bi origE origGoal) (f : FVarId) (α : Q(Sort v)) :
    ProofModeM (RevertState bi origE origGoal) := do
  let { e, hyps, goal, reverted, pf } := st
  let x : Q($α) := mkFVar f
  have Φ : Q($α → $prop) := ← mkLambdaFVars #[x] goal
  let goal' : Q($prop) := q(BI.forall $Φ)
  have pf' : Q(($e ⊢ $goal') → ($origE ⊢ $origGoal)) :=
    ← withLocalDeclDQ `h q($e ⊢ BI.forall $Φ) fun h => do
      mkLambdaFVars #[h] (mkApp pf (← mkAppM ``forall_revert #[h, x]))
  return { e, hyps, goal := goal', reverted := reverted.push f, pf := pf' }

/-- Revert a Lean local after checking proofmode and local-context dependencies. -/
private def RevertState.revertLeanHyp
    (st : @RevertState u prop bi origE origGoal) (hyp : TSyntax `ident) :
    ProofModeM (RevertState bi origE origGoal) := do
  let ldecl ← st.checkLeanDependencies hyp
  let f := ldecl.fvarId
  let v : Level ← Meta.getLevel ldecl.type
  have α : Q(Sort v) := ldecl.type
  if ← Meta.isProp α then
    have φ : Q(Prop) := α
    st.revertLeanPropHyp f φ
  else
    st.revertLeanForallHyp f α

-- TODO: when extending this to selection patterns, consider adding a selection pattern %x for pure hypotheses such that it is syntactically clear whether an argument of irevert refers to a pure or an Iris hypothesis
elab "irevert" hs:(colGt ident)+ : tactic => do
  ProofModeM.runTactic fun mvar { bi, e, hyps, goal, .. } => do
    let init : RevertState bi e goal := { e, hyps, goal, pf := q(id) }
    let st ← hs.reverse.toList.foldlM (init := init) fun st hyp => do
      if let some _ := st.hyps.find? hyp.getId then
        st.revertProofModeHyp hyp
      else
        st.revertLeanHyp hyp

    -- Clear Lean locals already reverted into the accumulated BI goal from the final generated subgoal.
    let finalGoalId ← (← mkBIGoal st.hyps st.goal).mvarId!.tryClearMany st.reverted.reverse
    addMVarGoal finalGoalId
    mvar.assign (mkApp st.pf (Expr.mvar finalGoalId))
