/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Michael Sammler
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Assumption
import Iris.ProofMode.Tactics.HaveCore

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

private theorem apply [BI PROP] {p} {P Q Q1 R : PROP}
    (h1 : P ⊢ Q1)
    [h2 : IntoWand p false Q .out Q1 .in R] : P ∗ □?p Q ⊢ R :=
      (Entails.trans (sep_mono_l h1) (wand_elim' h2.1))

/--
Apply a hypothesis `A` to the `goal` by eliminating the wands recursively

## Parameters
- `hyps`: The current proof mode hypothesis context
- `p`: Persistence flag for `A`

## Returns
The proof of `hyps ∗ □?p A ⊢ goal`
-/
partial def iApplyCore {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e) (p : Q(Bool)) (A : Q($prop)) (goal : Q($prop)) : ProofModeM Q($e ∗ □?$p $A ⊢ $goal) := do
  let B ← mkFreshExprMVarQ q($prop)
  -- if `A := ?B -∗ goal`, add `B` as a new subgoal and conclude `goal`
  if let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $A .out $B .in $goal) then
     let pf ← addBIGoal hyps B
     return q(apply $pf)

  -- otherwise, if `A` has the form `?P -∗ ?B`, create a subgoal for `P` and continue with ?B
  let some ⟨_, hyps', pb, B, pf⟩ ← try? <| iSpecializeCore hyps p A [.goal [] .anonymous]
    | throwError m!"iapply: cannot apply {A} to {goal}"
  let pf' ← iApplyCore hyps' pb B goal
  return q($(pf).trans $pf')

elab "iapply" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  -- elaborate the proof mode term `pmt` to the hypothesis `out`
  let ⟨e, hyps', p, out, pf⟩ ← iHave hyps pmt true (mayPostpone := true)
  -- if `□?p out` directly matches goal, behave like `iexact`
  if let some _ ← ProofModeM.trySynthInstanceQ q(FromAssumption $p .in $out $goal) then
    -- ensure the context can be discarded
    let LOption.some _ ← trySynthInstanceQ q(TCOr (Affine $e) (Absorbing $goal))
      | throwError "iapply: the context {e} is not affine and goal not absorbing"
    have rfl : Q($e ∗ □?$p $out ⊣⊢ $e ∗ □?$p $out) := q(.rfl)
    mvar.assign q($(pf).trans (assumption (Q := $goal) $(rfl)))
    return
  -- otherwise, `out` should be a wand, handled by `iApplyCore`
  let pf' ← iApplyCore hyps' p out goal
  mvar.assign q($(pf).trans $pf')
