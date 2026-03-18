/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Yunsong Yang
-/
import Iris.ProofMode.Tactics.Cases
import Iris.ProofMode.ClassesMake
import Iris.ProofMode.InstancesMake

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

private theorem wand_revert [BI PROP] {Δ Δ' P Q : PROP}
    (h1 : Δ ⊣⊢ Δ' ∗ P) (h2 : Δ' ⊢ P -∗ Q) : Δ ⊢ Q :=
  h1.mp.trans (wand_elim h2)

private theorem forall_revert [BI PROP] {Δ : PROP} {Ψ : α → PROP}
    (h : Δ ⊢ BI.forall Ψ) : ∀ x, Δ ⊢ Ψ x :=
  λ x => h.trans (forall_elim x)

private theorem pure_revert [BI PROP] {Δ P Q : PROP} {φ : Prop}
    [hA : MakeAffinely iprop(⌜φ⌝) P ]
    (h : Δ ⊢ P -∗ Q) : φ → Δ ⊢ Q := by
  intro hp
  have hA : (emp : PROP) ⊢ P :=
    (affinely_emp.mpr.trans <| affinely_mono <| pure_intro hp).trans (hA.make_affinely.mp)
  exact (sep_emp.mpr.trans (sep_mono .rfl hA)).trans (wand_elim h)

private structure RevertState {prop : Q(Type u)} (bi : Q(BI $prop)) (origE origGoal : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e) (goal : Q($prop))
  (reverted : Array FVarId := #[])
  pf : Q(($e ⊢ $goal) → ($origE ⊢ $origGoal))

/-- Revert a proofmode hypothesis by turning it into a wand premise. -/
private def RevertState.revertProofModeHyp
    : @RevertState u prop bi origE origGoal → TSyntax `ident →
      ProofModeM (RevertState bi origE origGoal)
  | { hyps, goal, reverted, pf := pf0, .. }, hyp => do
      let uniq ← hyps.findWithInfo hyp
      let ⟨e', hyps', out, _, _, _, hΔ⟩ := hyps.remove true uniq
      return { e := e'
             , hyps := hyps'
             , goal := q(wand $out $goal)
             , reverted := reverted
             , pf := q(fun h => $pf0 (wand_revert $hΔ h)) }

/-- Check that reverting the Lean local named by `hyp` will not leave dangling dependencies. -/
private def RevertState.checkLeanDependencies
    : @RevertState u prop bi origE origGoal → TSyntax `ident → MetaM LocalDecl
  | { hyps, reverted, .. }, hyp => do
      let ldecl ← getLocalDeclFromUserName hyp.getId
      let f := ldecl.fvarId
      if let some (name, _, _, _) := hyps.findDependencyOnFVar f then
        throwError "irevert: proofmode hypothesis {name} depends on {hyp.getId}"
      let lctx ← getLCtx
      let toRevert ← collectForwardDeps #[mkFVar f] false
      if let some dep := toRevert.find? (fun e => e.fvarId! != f && !reverted.contains e.fvarId!) then
        let depDecl := lctx.getFVar! dep
        throwError "irevert: Lean hypothesis {depDecl.userName} depends on {hyp.getId}"
      return ldecl

/-- Revert a Lean proposition by turning it into the `MakeAffinely` pure premise. -/
private def RevertState.revertLeanPropHyp
    (st : @RevertState u prop bi origE origGoal) (f : FVarId) (φ : Q(Prop)) :
    ProofModeM (RevertState bi origE origGoal) := do
  let { e, hyps, goal, reverted, pf := pf0 } := st
  let P ← mkFreshExprMVarQ prop
  let _hA : Q(MakeAffinely iprop(⌜$φ⌝) $P) ← synthInstanceQ q(MakeAffinely iprop(⌜$φ⌝) $P)
  let hp : Q($φ) := mkFVar f
  let goal' : Q($prop) := q(iprop($P -∗ $goal))
  let pf' : Q(($e ⊢ $goal') → ($origE ⊢ $origGoal)) := q(fun h =>$pf0 ((pure_revert h) $hp))
  return { e := e
         , hyps := hyps
         , goal := goal'
         , reverted := reverted.push f
         , pf := pf' }

/-- Revert a Lean non-`Prop` local by turning the current goal into a forall. -/
private def RevertState.revertLeanForallHyp
    (st : @RevertState u prop bi origE origGoal) (f : FVarId) (α : Q(Sort v)) :
    ProofModeM (RevertState bi origE origGoal) := do
  let { e, hyps, goal, reverted, pf := pf0 } := st
  let x : Q($α) := mkFVar f
  have Φ : Q($α → $prop) := ← mkLambdaFVars #[x] goal
  let goal' : Q($prop) := q(BI.forall $Φ)
  have pf' : Q(($e ⊢ $goal') → ($origE ⊢ $origGoal)) :=
    ← withLocalDeclDQ `h q($e ⊢ BI.forall $Φ) fun h => do
      mkLambdaFVars #[h] (mkApp pf0 (← mkAppM ``forall_revert #[h, x]))
  return { e := e
         , hyps := hyps
         , goal := goal'
         , reverted := reverted.push f
         , pf := pf' }

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

elab "irevert" hs:(colGt ident)+ : tactic => do
  ProofModeM.runTactic fun mvar { bi, e, hyps, goal, .. } => do
    let init : RevertState bi e goal := { e, hyps, goal, pf := q(id) }
    let st ← hs.reverse.toList.foldlM (init := init) fun st hyp => do
      if let some _ := st.hyps.find? hyp.getId then
        st.revertProofModeHyp hyp
      else
        st.revertLeanHyp hyp
    let finalGoal0 : Q($st.e ⊢ $st.goal) ← addBIGoal st.hyps st.goal
    -- Clear the reverted variables from the context
    let finalGoalId ← finalGoal0.mvarId!.withContext do
      st.reverted.reverse.foldrM (init := finalGoal0.mvarId!) fun fvarId goal => goal.clear fvarId
    modify fun s => { s with goals := s.goals.map (fun goal => if goal == finalGoal0.mvarId! then finalGoalId else goal) }
    have finalGoal : Q($st.e ⊢ $st.goal) := Expr.mvar finalGoalId
    mvar.assign q($st.pf $finalGoal)
