/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

import Iris.BI
import Iris.ProofMode.Classes
public meta import Iris.ProofMode.Patterns.SelPattern
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open BI

theorem frame [BI PROP] {p} {e e' P Q R : PROP}
    [h1 : Frame p R P Q]
    (h2 : e ⊣⊢ e' ∗ □?p R) :
    (e' ⊢ Q) →
    e ⊢ P := λ h =>
  h2.1.trans <| sep_comm.1.trans <| (sep_mono_r h).trans h1.1

theorem frame_pure [BI PROP] {e P Q : PROP} (φ : Prop)
    [h1 : Frame true iprop(⌜φ⌝) P Q] (h : φ) :
    (e ⊢ Q) →
    e ⊢ P := fun hQ =>
  have h_box : emp ⊢ □?true iprop(⌜φ⌝) := affinely_intro ((pure_intro h).trans persistent)
  emp_sep.2.trans <| (sep_mono_l h_box).trans <| (sep_mono_r hQ).trans h1.1

theorem frame_true_done [BI PROP] (P : PROP) : P ⊢ True :=
  pure_intro .intro

public meta section
open Lean Elab Tactic Meta Qq Std

private def iFrameSingle {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop))
    (hyps : Hyps bi e) (goal : Q($prop)) (sel : SelTarget) :
    ProofModeM ((e' : Q($prop)) × (_ : Hyps bi e')
      × (goal' : Q($prop)) × Q(($e' ⊢ $goal') → $e ⊢ $goal)) := do
    match sel.target with
    | .inl uniq =>
      let ⟨e', hyps', _, out', p, _, hrem⟩ := hyps.remove false uniq
      let goal' ← mkFreshExprMVarQ q($prop)
      if let .some _ ← ProofModeM.trySynthInstanceQ q(Frame $p $out' $goal $goal') then
        return ⟨e', hyps', goal', q(frame $hrem)⟩
      if sel.explicit then
         throwError "iframe: cannot frame {out'}"
      else
        return ⟨e, hyps, goal, q(λ x => x)⟩
    | .inr fvar =>
      let ty ← fvar.getType
      if ! (← Meta.isProp ty) then
        throwError "iframe: {← fvar.getUserName} is not a Prop"
      have φ : Q(Prop) := ty
      have t : Q($φ) := Expr.fvar fvar
      let goal' ← mkFreshExprMVarQ q($prop)
      if let .some _ ← ProofModeM.trySynthInstanceQ q(Frame true iprop(⌜$φ⌝) $goal $goal') then
        return ⟨e, hyps, goal', q(frame_pure $φ $t)⟩
      if sel.explicit then
        throwError "iframe: cannot frame ⌜{φ}⌝"
      else
        return ⟨e, hyps, goal, q(λ x => x)⟩



private structure FrameState {u} {prop : Q(Type u)} (bi : Q(BI $prop)) (origE origGoal : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e) (goal : Q($prop))
  pf : Q(($e ⊢ $goal) → ($origE ⊢ $origGoal))

private def FrameState.frame {u prop bi origE origGoal} :
    @FrameState u prop bi origE origGoal → SelTarget →
    ProofModeM (FrameState bi origE origGoal) := λ st sel => do
    let ⟨e', hyps', goal', pf⟩ ← iFrameSingle bi st.e st.hyps st.goal sel
    return { e := e', hyps := hyps', goal := goal', pf := q(λ h => $st.pf ($pf h)) }

def iFrame {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop))
    (hyps : Hyps bi e) (goal : Q($prop)) (sels : List SelTarget) :
    ProofModeM ((e' : Q($prop)) × (_ : Hyps bi e')
      × (goal' : Q($prop)) × (Q(($e' ⊢ $goal') → $e ⊢ $goal) ⊕ Q($e ⊢ $goal))) := do
  let mut st : FrameState bi e goal := { e, hyps, goal, pf := q(fun h => h) }
  for sel in sels do st ← st.frame sel

  -- try closing the goal for emp or True
  let pf' ← match st.goal with
    | ~q(iprop(emp)) =>
      have e := st.e
      if let .some _ ← trySynthInstanceQ q(Affine $e) then
        return some (q(affine (P := $e)) : Q($e ⊢ $(st.goal)))
      else
        return none
    | ~q(iprop(True)) =>
      have e := st.e
      return some (q(frame_true_done $e) : Q($e ⊢ $(st.goal)))
    | _ => return none
  if let some pf' := pf' then
    have pf' : Q($st.e ⊢ $(st.goal)) := pf'
    return ⟨_, st.hyps, st.goal, .inr q($(st.pf) $pf')⟩
  return ⟨_, st.hyps, st.goal, .inl st.pf⟩


elab "iframe" pats:(colGt selPat)+ : tactic => do
  let pats ← liftMacroM <| SelPat.parse pats

  ProofModeM.runTactic λ mvar { bi, e, hyps, goal, .. } => do
  let pats ← SelPat.resolve hyps pats

  let ⟨_, hyps', goal', pf⟩ ← iFrame bi e hyps goal pats
  match pf with
  | .inl pf =>
    let pf' ← addBIGoal hyps' goal'
    mvar.assign q($pf $pf')
  | .inr pf =>
    mvar.assign q($pf)

macro "iframe" : tactic => `(tactic | iframe ∗)
