/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Yunsong Yang
-/
module

import Iris.BI
import Iris.ProofMode.Classes
public meta import Iris.ProofMode.Patterns.SelPattern
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open BI Std

theorem clear_spatial [BI PROP] {P P' A Q : PROP} [TCOr (Affine A) (Absorbing Q)]
    (h_rem : P ⊣⊢ P' ∗ A) (h : P' ⊢ Q) : P ⊢ Q :=
  h_rem.1.trans <| (sep_mono_l h).trans sep_elim_l

theorem clear_intuitionistic [BI PROP] {P P' A Q : PROP}
    (h_rem : P ⊣⊢ P' ∗ □ A) (h : P' ⊢ Q) : P ⊢ Q := clear_spatial h_rem h

public meta section
open Lean Elab Tactic Meta Qq

def iClearCore {prop : Q(Type u)} (_bi : Q(BI $prop)) (e e' : Q($prop))
    (p : Q(Bool)) (out goal : Q($prop))
    (pf : Q($e ⊣⊢ $e' ∗ □?$p $out)) : ProofModeM Q(($e' ⊢ $goal) → $e ⊢ $goal) := do
    match matchBool p with
    | .inl _ => return q(clear_intuitionistic (Q := $goal) $pf)
    | .inr _ =>
      let .some _ ← trySynthInstanceQ q(TCOr (Affine $out) (Absorbing $goal))
        | throwError "iclear: {out} is not affine and the goal not absorbing"
      return q(clear_spatial (A:=$out) $pf)

private structure ClearState {prop : Q(Type u)} {bi : Q(BI $prop)} (origE goal : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e)
  pf : Q(($e ⊢ $goal) → ($origE ⊢ $goal))

private def ClearState.clearProofModeHyp {origE goal} :
    @ClearState u prop bi origE goal → Name →
    ProofModeM (@ClearState u prop bi origE goal)
  | { e, hyps, pf }, uniq => do
      let ⟨e', hyps', _, out', p, _, hrem⟩ := hyps.remove true uniq
      let step ← iClearCore bi e e' p out' goal hrem
      let pf' : Q(($e' ⊢ $goal) → ($origE ⊢ $goal)) :=
        ← withLocalDeclDQ `h q($e' ⊢ $goal) fun h => do
          mkLambdaFVars #[h] <| mkApp pf <| mkApp step h
      return { e := e', hyps := hyps', pf := pf' }

elab "iclear" pats:(colGt selPat)+ : tactic => do
  let pats ← liftMacroM <| pats.mapM <| SelPat.parse

  ProofModeM.runTactic λ mvar { e, hyps, goal, .. } => do
  let (uniqs, fvars) := splitSelTargets (← resolveSelTargets hyps pats.toList)

  -- Clear the selected Iris hypotheses first, updating the proof-mode context and proof term.
  let init : ClearState e goal := { e, hyps, pf := q(fun h => h) }
  let st ← uniqs.foldlM (init := init)
    fun st uniq => st.clearProofModeHyp uniq

  -- Lean locals are cleared afterwards; first ensure no remaining hypothesis or goal depends on them.
  for fvar in fvars do
    let _ ← st.hyps.checkRemovableFVar "iclear" fvar (some goal) fvars.contains

  let finalGoal ← mkBIGoal st.hyps goal
  -- Sanity check: after the dependency precheck, all selected Lean locals should clear.
  let fvars := fvars.reverse.toArray
  let (finalGoalId, cleared) ← finalGoal.mvarId!.tryClearMany' fvars
  unless cleared.size == fvars.size do
    throwError "iclear: internal error: failed to clear all selected Lean hypotheses"
  addMVarGoal finalGoalId
  mvar.assign (mkApp st.pf (Expr.mvar finalGoalId))
