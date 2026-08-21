/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Michael Sammler
-/
module

public import Iris.BI
public import Iris.ProofMode.Tactics.HaveCore

namespace Iris.ProofMode

public section
open BI

@[rocq_alias tac_apply]
theorem apply [BI PROP] {p} {P Q Q1 R : PROP}
    (h1 : P ⊢ Q1)
    [h2 : IntoWand p false Q (.matching .result) Q1 R] : P ∗ □?p Q ⊢ R :=
  Entails.trans (sep_mono_left h1) (wand_elim_swap h2.into_wand)

public meta section
open Lean Elab Tactic Meta Qq Std

/--  Like `ProofMode.assumption`, but specialized for the `iapply` case. -/
theorem apply_assumption [BI PROP] {p : Bool} {P A Q : PROP}
    [inst : FromAssumption p .in A Q] [TCOr (Affine P) (Absorbing Q)] :
    P ∗ □?p A ⊢ Q :=
  (sep_mono_right inst.from_assumption).trans sep_elim_right

private partial def iApplyCore {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (p : Q(Bool)) (A : Q($prop)) (goal : Q($prop)) :
    ProofModeM Q($e ∗ □?$p $A ⊢ $goal) := do
  let B ← mkFreshExprMVarQ q($prop)
  -- if `A := ?B -∗ goal`, add `B` as a new subgoal and conclude `goal`
  if let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $A (.matching .result) $B $goal) then
     let pf ← addBIGoal hyps B
     return q(apply $pf)

  -- otherwise, if `A` has the form `?P -∗ ?B`, create a subgoal for `P` and continue with `?B`
  let some ⟨_, hyps', pb, B, pf⟩ ← try? <| iSpecializeCore hyps p A goal
    [⟨← getRef, .goal {kind := .spatial, negate := false, trivial := false, frame := [], hyps := []} .anonymous⟩]
    | throwIPMError "cannot apply {A} to {goal}"
  let pf' ← iApplyCore hyps' pb B goal
  return q($pf $pf')


/-- Apply a hypothesis `A` to the `goal` by eliminating the wands recursively. -/
def iApply {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (p : Q(Bool)) (A : Q($prop)) (goal : Q($prop)) :
    ProofModeM Q($e ∗ □?$p $A ⊢ $goal) := do
  -- if `□?p A` directly matches goal, behave like `iexact`
  if let some _ ← ProofModeM.trySynthInstanceQ q(FromAssumption $p .in $A $goal) then
    -- ensure the context can be discarded
    let .some _ ← trySynthInstanceQ q(TCOr (Affine $e) (Absorbing $goal))
      | throwIPMError "the context {e} is not affine and goal not absorbing"
    return q(apply_assumption)
  -- otherwise, `A` should be a wand, handled by `iApplyCore`
  iApplyCore hyps p A goal

/--
  `iapply pmt` matches the conclusion of `pmt : pmTerm` against the goal and
  generate goals for each premise. For example, given a goal `R` and
  a hypothesis `H : P -∗ Q -∗ R`, `iapply H` generates two new goals,
  one with the conclusion `P` and another with the conclusion `Q`.

  `iapply pmt H $$ pat1 pat2` uses the specialisation patterns `pat1`
  and `pat2`, which specifies how the wand premises of `H` are discharged.
  This is analogous to `iApply (H with "pat1 pat2")` in Rocq. For example,
  given hypotheses `∗HP: □ P` and `∗H : P -∗ Q`, as well as the goal `Q`,
  `iapply H $$ HP` solves the goal.
-/
elab "iapply " colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic `iapply λ mvar { hyps, goal, .. } => do
  -- elaborate the proof mode term `pmt` to the hypothesis `out`
  let ⟨_, hyps', p, out, pf⟩ ← iHave hyps goal pmt true
  let pf' ← iApply hyps' p out goal
  mvar.assign q($pf $pf')
