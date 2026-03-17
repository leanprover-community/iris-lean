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

/-
  `IntoIH φ P Q` describes how to turn a pure induction hypothesis `φ` into a proofmode
  hypothesis `Q` under an intuitionistic BI context `□ P`.
  This class is intended for implementing `iinduction`
-/
@[ipm_class]
class IntoIH [BI PROP] (φ : Prop) (P : PROP) (Q : outParam PROP) where
  into_ih : φ → □ P ⊢ Q

-- TODO: two more instances [into_ih_Forall] and [into_ih_Forall2]
-- have not been implemented
instance intoIH_entails [BI PROP] (P Q : PROP) : IntoIH (P ⊢ Q) P Q where
  into_ih := λ hpq => intuitionistically_elim.trans hpq
instance intoIH_forall [BI PROP] (φ : α → Prop) (P : PROP) (Φ : α → PROP)
    [h : ∀ x, IntoIH (φ x) P (Φ x)] :
    IntoIH (∀ x, φ x) P (BI.forall Φ) where
  into_ih := by
    intro hφ
    apply forall_intro
    intro x
    exact (h x).into_ih (hφ x)
instance intoIH_imp [BI PROP] (φ ψ : Prop) (Δ P Q : PROP)
    [h1 : MakeAffinely iprop(⌜φ⌝) P]
    [h2 : IntoIH ψ Δ Q] :
    IntoIH (φ → ψ) Δ iprop(P -∗ Q) where
  into_ih := by
    intro hImp
    apply wand_intro
    refine (sep_mono_r h1.make_affinely.mpr).trans ?_
    refine persistent_and_affinely_sep_r.2.trans ?_
    exact pure_elim_r (fun hφ => h2.into_ih (hImp hφ))

private theorem ih_revert [BI PROP] {Δ P Q : PROP} {φ : Prop} (hφ : φ)
    [hP : IntoIH φ Δ P]
    (hΔ : Δ ⊢ □ Δ)
    (hPQ : Δ ⊢ iprop(<pers> P → Q)) :
    Δ ⊢ Q := by
  have hP' : □ Δ ⊢ <pers> P :=
    (intuitionistically_intro' (hP.into_ih hφ)).trans persistently_of_intuitionistically
  have hAnd : □ Δ ⊢ iprop(<pers> P ∧ (<pers> P → Q)) :=
    and_intro hP' <| intuitionistically_elim.trans hPQ
  exact hΔ.trans <| hAnd.trans (imp_elim_r (P := iprop(<pers> P)) (Q := Q))

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
  let hA : Q(MakeAffinely iprop(⌜$φ⌝) $P) ← synthInstanceQ q(MakeAffinely iprop(⌜$φ⌝) $P)
  let hp : Q($φ) := mkFVar f
  let goal' : Q($prop) := q(iprop($P -∗ $goal))
  let pf' : Q(($e ⊢ $goal') → ($origE ⊢ $origGoal)) :=
    q(fun h =>$pf0 ((@pure_revert $prop $bi $e $P $goal $φ $hA h) $hp))
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
  let ΦExpr ← mkLambdaFVars #[x] goal
  let some Φ ← checkTypeQ ΦExpr q($α → $prop)
    | throwError "irevert: failed to construct forall body"
  let goal' : Q($prop) := q(BI.forall $Φ)
  let pf'Expr ← withLocalDeclDQ `h q($e ⊢ BI.forall $Φ) fun h => do
    let step ← mkAppM ``forall_revert #[h]
    let oldGoalProof ← mkExpectedTypeHint (mkApp step x) q($e ⊢ $goal)
    mkLambdaFVars #[h] (mkApp pf0 oldGoalProof)
  let some pf' ← checkTypeQ pf'Expr q(($e ⊢ $goal') → ($origE ⊢ $origGoal))
    | throwError "irevert: failed to construct forall revert proof"
  return { e := e
         , hyps := hyps
         , goal := goal'
         , reverted := reverted.push f
         , pf := pf' }

/-- Revert a Lean local after checking proofmode and local-context dependencies. -/
private def RevertState.revertLeanHyp
    (mvar : MVarId) (st : @RevertState u prop bi origE origGoal) (hyp : TSyntax `ident) :
    ProofModeM (RevertState bi origE origGoal) := do
  mvar.withContext do
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
    let init : RevertState bi e goal :=
      { e := e, hyps := hyps, goal := goal, reverted := #[], pf := q(id) }
    let st ← hs.reverse.toList.foldlM (init := init) fun st hyp => do
      if let some _ := st.hyps.find? hyp.getId then
        st.revertProofModeHyp hyp
      else
        st.revertLeanHyp mvar hyp
    let finalGoal : Q($st.e ⊢ $st.goal) ← addBIGoal st.hyps st.goal
    mvar.assign q($st.pf $finalGoal)
