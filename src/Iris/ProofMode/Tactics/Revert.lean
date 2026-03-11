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

private theorem wand_revert [BI PROP] {Δ Δ' P Q : PROP}
    (h1 : Δ ⊣⊢ Δ' ∗ P) (h2 : Δ' ⊢ P -∗ Q) : Δ ⊢ Q :=
  h1.mp.trans (wand_elim h2)

private theorem forall_revert [BI PROP] {Δ : PROP} {Ψ : α → PROP}
    (h : Δ ⊢ ∀ x, Ψ x) : ∀ x, Δ ⊢ Ψ x :=
  λ x => h.trans (forall_elim x)

private theorem pure_revert [BI PROP] {Δ P Q : PROP} {φ : Prop}
    [hA : MakeAffinely iprop(⌜φ⌝) P ]
    (h : Δ ⊢ P -∗ Q) : φ → Δ ⊢ Q := by
  intro hp
  have hA : (emp : PROP) ⊢ P :=
    (affinely_emp.mpr.trans <| affinely_mono <| pure_intro hp).trans (hA.make_affinely.mp)
  exact (sep_emp.mpr.trans (sep_mono .rfl hA)).trans (wand_elim h)

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

private def iRevertHypCore {prop : Q(Type u)} {bi : Q(BI $prop)} {e e' : Q($prop)}
    (out goal : Q($prop)) (pf : Q($e ⊣⊢ $e' ∗ $out)) :
    ProofModeM (Q(($e' ⊢ iprop($out -∗ $goal)) → ($e ⊢ $goal))) := do
  return q(wand_revert (Q:=$goal) $pf)

private def iRevertOne (mvar : MVarId) (hyp : TSyntax `ident) : ProofModeM MVarId := do
  let (mvar, { u, prop, bi, e, hyps, goal, .. }) ← startProofMode mvar
  mvar.withContext do
    if let some (uniq, _, _) := hyps.find? hyp.getId then
      -- Remove current goal
      modify fun s => { s with goals := s.goals.filter (· != mvar) }

      -- Target lives in proofmode context
      let ⟨e', hyps', out, _, _, _, pf⟩ := hyps.remove true uniq
      let subgoal : Q($e' ⊢ $out -∗ $goal) ← addBIGoal hyps' q(wand $out $goal)
      mvar.assign q(wand_revert $pf $subgoal)
      return subgoal.mvarId!
    else
      -- Target lives in Lean context (two cases: Prop / non-Prop)
      let f ← getFVarId hyp
      let some ldecl := (← getLCtx).find? f
        | throwError "irevert: {hyp.getId} not in scope"

      let v : Level ← Meta.getLevel ldecl.type
      have α : Q(Sort v) := ldecl.type

      let (_, mvarId) ← mvar.revert #[f]
      mvarId.withContext do
        -- Prop case
        -- TODO: add [ih_revert] case we need to check whether spatial context is empty
        if ← Meta.isProp α then
          have φ : Q(Prop) := α
          let p : Q($prop) := q(iprop(<affine> ⌜$φ⌝))
          let hA : Q(MakeAffinely iprop(⌜$φ⌝) $p) ←
            synthInstanceQ q(MakeAffinely iprop(⌜$φ⌝) $p)
          let subgoal : Q($e ⊢ iprop($p -∗ $goal)) ← addBIGoal hyps q(iprop($p -∗ $goal))
          mvarId.assign q(@pure_revert $prop $bi $e iprop(<affine> ⌜$φ⌝) $goal $φ $hA $subgoal)
          return subgoal.mvarId!
        else
        -- Non-Prop case
          let Φ : Q($α → $prop) ← mapForallTelescope' (λ t _ => do
              let some ig := parseIrisGoal? t
                | throwError "irevert: not in proof mode"
              pure ig.goal
            ) (Expr.mvar mvarId)

          let subgoal : Q($e ⊢ BI.forall $Φ) ← addBIGoal hyps q(BI.forall $Φ)
          mvarId.assign q(@forall_revert $prop _ $bi $e $Φ $subgoal)
          return subgoal.mvarId!

elab "irevert" hyps:(colGt ident)+ : tactic => do
  ProofModeM.runTactic λ mvar _ => do
    let mut mvar := mvar
    for hyp in hyps.reverse do
      mvar ← iRevertOne mvar hyp
