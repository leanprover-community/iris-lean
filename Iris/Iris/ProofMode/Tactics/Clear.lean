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
  h_rem.1.trans <| (sep_mono_left h).trans sep_elim_left

theorem clear_intuitionistic [BI PROP] {P P' A Q : PROP}
    (h_rem : P ⊣⊢ P' ∗ □ A) (h : P' ⊢ Q) : P ⊢ Q := clear_spatial h_rem h

public meta section
open Lean Elab Tactic Meta Qq

def iClearCoreOne {prop : Q(Type u)} (_bi : Q(BI $prop)) (e e' : Q($prop))
    (p : Q(Bool)) (out goal : Q($prop)) (pf : Q($e ⊣⊢ $e' ∗ □?$p $out))
    (tacName : String := "iclear") : ProofModeM Q(($e' ⊢ $goal) → $e ⊢ $goal) := do
    match matchBool p with
    | .inl _ => return q(clear_intuitionistic (Q := $goal) $pf)
    | .inr _ =>
      let .some _ ← trySynthInstanceQ q(TCOr (Affine $out) (Absorbing $goal))
        | throwError "{tacName}: {out} is not affine and the goal not absorbing"
      return q(clear_spatial (A:=$out) $pf)

private structure ClearState {u} {prop : Q(Type u)} {bi : Q(BI $prop)} (origE goal : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e)
  pf : Q(($e ⊢ $goal) → ($origE ⊢ $goal))

private def ClearState.clearProofModeHyp {u prop bi origE goal} :
    @ClearState u prop bi origE goal → IVarId →
    ProofModeM (@ClearState u prop bi origE goal)
  | { e, hyps, pf }, ivar => do
      let ⟨e', hyps', _, out', p, _, hrem⟩ := hyps.remove true ivar
      let step ← iClearCoreOne bi e e' p out' goal hrem
      let pf' : Q(($e' ⊢ $goal) → ($origE ⊢ $goal)) := q(λ h => $pf ($step h))
      return {  e := e', hyps := hyps', pf := pf' }

def iClearCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (pats : List SelPat)
    (k : ∀ {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
      (_ : Hyps bi e) (goal : Q($prop)) (_ : Array FVarId), ProofModeM Q($e ⊢ $goal)) :
    ProofModeM Q($e ⊢ $goal) := do
  let (ivars, fvars) := (← SelPat.resolve hyps pats).partitionMap fun
  | {kind := .ipm ivar, ..} => .inl ivar
  | {kind := .pure id,  ..} => .inr id

  -- Clear the selected Iris hypotheses first, updating the proof-mode context and proof term.
  let mut st : ClearState e goal := { e, hyps, pf := q(id) }
  for ivar in ivars do st ← st.clearProofModeHyp ivar

  -- Lean locals are cleared afterwards; first ensure no remaining hypothesis or goal depends on them.
  for fvar in fvars do
    let _ ← st.hyps.checkRemovableFVar "iclear" fvar (some goal) fvars.contains

  let pf' ← k st.hyps goal fvars.reverse.toArray
  return q($(st.pf) $pf')

/--
  `iclear pats` discards the hypotheses selected by the selection pattern `pats`.
-/
elab "iclear " pats:(colGt ppSpace selPat)+ : tactic => do
  let pats ← liftMacroM <| SelPat.parse pats

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let pf ← iClearCore hyps goal pats (addBIGoalWithoutFVars · ·)
    mvar.assign pf
