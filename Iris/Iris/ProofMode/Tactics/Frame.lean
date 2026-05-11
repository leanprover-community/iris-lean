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

theorem frame_init [BI PROP] {e goal : PROP} :
    e ⊢ e ∗ (goal -∗ goal) :=
  sep_emp.2.trans (sep_mono_r (wand_intro emp_sep.1))

theorem frame_hyp [BI PROP] {p} {e e' origE goal goal' origGoal R : PROP}
    (h1 : origE ⊢ e ∗ (goal -∗ origGoal))
    [h2 : Frame p R goal goal']
    (h3 : e ⊣⊢ e' ∗ □?p R) :
    origE ⊢ e' ∗ (goal' -∗ origGoal) :=
  h1.trans <| (sep_mono_l h3.1).trans <| sep_assoc.1.trans <|
  sep_mono_r (wand_intro (sep_assoc.1.trans <| (sep_mono_r sep_comm.1).trans <|
    sep_assoc.2.trans <| (sep_mono_l h2.frame).trans wand_elim_r))

theorem frame_pure [BI PROP] {origE e goal goal' origGoal : PROP} (φ : Prop)
    (h1 : origE ⊢ e ∗ (goal -∗ origGoal))
    [h2 : Frame true iprop(⌜φ⌝) goal goal'] (h : φ) :
    origE ⊢ e ∗ (goal' -∗ origGoal) :=
  have h_box : emp ⊢ □?true iprop(⌜φ⌝) := affinely_intro ((pure_intro h).trans persistent)
  h1.trans <| sep_mono_r <| wand_intro <|
    emp_sep.2.trans <| (sep_mono_l h_box).trans <|
    (sep_mono_r sep_comm.1).trans <| sep_assoc.2.trans <|
    (sep_mono_l h2.frame).trans wand_elim_r

theorem frame_finish [BI PROP] {e origE goal origGoal : PROP}
    (h1 : origE ⊢ e ∗ (goal -∗ origGoal)) (h2 : e ⊢ goal) :
    origE ⊢ origGoal :=
  h1.trans ((sep_mono_l h2).trans wand_elim_r)

theorem frame_true_done [BI PROP] (P : PROP) : P ⊢ True :=
  pure_intro .intro

theorem frame_finish_close_true [BI PROP] {e origE origGoal : PROP}
    (h1 : origE ⊢ e ∗ (True -∗ origGoal)) :
    origE ⊢ e ∗ origGoal := h1.trans (sep_mono_r <| true_sep_2.trans wand_elim_r)

theorem frame_finish_close_emp [BI PROP] {e origE origGoal : PROP}
    (h1 : origE ⊢ e ∗ (emp -∗ origGoal)) :
    origE ⊢ e ∗ origGoal := h1.trans (sep_mono_r <| emp_sep.2.trans wand_elim_r)

public meta section
open Lean Elab Tactic Meta Qq Std

structure FrameResult {u} {prop : Q(Type u)} (bi : Q(BI $prop)) (origE origGoal : Q($prop)) where
  (progress : Bool) (e : Q($prop)) (hyps : Hyps bi e) (goal : Q($prop))
  pf : Q($origE ⊢ $e ∗ ($goal -∗ $origGoal))

private def FrameResult.step {u prop bi origE origGoal} :
    @FrameResult u prop bi origE origGoal → SelTarget →
    ProofModeM (FrameResult bi origE origGoal)
    | st@{progress:= _, e:=_, hyps, goal, pf}, {explicit, target := .inl uniq} => do
      let ⟨e', hyps', _, out', p, _, hrem⟩ := hyps.remove false uniq
      let goal' ← mkFreshExprMVarQ q($prop)
      if let .some _ ← ProofModeM.trySynthInstanceQ q(Frame $p $out' $goal $goal') then
        return ⟨true, e', hyps', goal', q(frame_hyp $pf $hrem)⟩
      if explicit then
         throwError "iframe: cannot frame {out'}"
      else
        return st
    | st@{progress:= _, e, hyps, goal, pf}, {explicit, target := .inr fvar} => do
      let ty ← fvar.getType
      if ! (← Meta.isProp ty) then
        throwError "iframe: {← fvar.getUserName} is not a Prop"
      have φ : Q(Prop) := ty
      have t : Q($φ) := Expr.fvar fvar
      let goal' ← mkFreshExprMVarQ q($prop)
      if let .some _ ← ProofModeM.trySynthInstanceQ q(Frame true iprop(⌜$φ⌝) $goal $goal') then
        return ⟨true, e, hyps, goal', q(frame_pure $φ $pf $t)⟩
      if explicit then
        throwError "iframe: cannot frame ⌜{φ}⌝"
      else
        return st

def iFrame {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop))
    (hyps : Hyps bi e) (goal : Q($prop)) (sels : List SelTarget) :
    ProofModeM (FrameResult bi e goal) := do
  let mut st : FrameResult bi e goal := { progress := false, e, hyps, goal, pf := q(frame_init) }
  for sel in sels do st ← st.step sel
  return st

/-- FrameResult.finish turns a FrameResult into a proof of the original goal given a function k that
  handles the subgoal remaining after framing. This function k might not be called if the framing
  made the goal trivial. -/
def FrameResult.finish {u prop bi origE origGoal} (res : @FrameResult u prop bi origE origGoal)
  (k : ∀ {e}, Hyps bi e → (goal : Q($prop)) → ProofModeM Q($e ⊢ $goal)) :
  ProofModeM Q($origE ⊢ $origGoal) := do
  let {progress, e, hyps, goal, pf} := res
  if !progress then
    return q(frame_finish $pf $(← k hyps goal))
  -- try closing the goal for emp or True without calling k
  match goal with
  | ~q(iprop(emp)) =>
    if let .some _ ← trySynthInstanceQ q(Affine $e) then
      return q(frame_finish $pf (affine (P := $e)))
    else
      return q(frame_finish $pf $(← k hyps goal))
    | ~q(iprop(True)) =>
      return q(frame_finish $pf (frame_true_done $e))
    | _ => return q(frame_finish $pf $(← k hyps goal))

/-- FrameResult.finishClose check that the original goal was fully solved by framing and gives it
  back with the remaining hypotheses. -/
def FrameResult.finishClose {u prop bi origE origGoal} (res : @FrameResult u prop bi origE origGoal) :
  ProofModeM ((e : Q($prop)) × (_ : Hyps bi e) × Q($origE ⊢ $e ∗ $origGoal)) := do
  let {progress, e, hyps, goal, pf} := res
  if !progress then
    throwError "iframe: cannot solve {origGoal} by framing"
  -- try closing the goal for emp or True without calling k
  match goal with
  | ~q(iprop(emp)) =>
    return ⟨e, hyps, q(frame_finish_close_emp $pf)⟩
  | ~q(iprop(True)) =>
    return ⟨e, hyps, q(frame_finish_close_true $pf)⟩
  | _ => throwError "iframe: cannot solve {origGoal} by framing"


elab "iframe" pats:(colGt selPat)+ : tactic => do
  let pats ← liftMacroM <| SelPat.parse pats

  ProofModeM.runTactic λ mvar { bi, e, hyps, goal, .. } => do
  let pats ← SelPat.resolve hyps pats

  let res ← iFrame bi e hyps goal pats
  mvar.assign (← res.finish (addBIGoal · ·))

macro "iframe" : tactic => `(tactic | iframe ∗)
