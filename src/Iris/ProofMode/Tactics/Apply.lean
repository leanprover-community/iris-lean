/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Michael Sammler
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Assumption
import Iris.ProofMode.Tactics.Have

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

private theorem apply [BI PROP] {p} {P Q Q1 R : PROP}
    (h1 : P ⊢ Q1)
    [h2 : IntoWand p false Q .out Q1 .in R] : P ∗ □?p Q ⊢ R :=
      (Entails.trans (sep_mono_l h1) (wand_elim' h2.1))

partial def iApplyCore {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e) (p : Q(Bool)) (A : Q($prop)) (goal : Q($prop)) : ProofModeM Q($e ∗ □?$p $A ⊢ $goal) := do
  let B ← mkFreshExprMVarQ q($prop)
  if let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $A .out $B .in $goal) then
     let pf ← addBIGoal hyps B
     return q(apply $pf)

  let some ⟨_, hyps', pb, B, pf⟩ ← try? <| iSpecializeCore hyps p A [.goal [] .anonymous]
    | throwError m!"iapply: cannot apply {A} to {goal}"
  let pf' ← iApplyCore hyps' pb B goal
  return q($(pf).trans $pf')

elab "iapply" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let ⟨e, hyps, p, out, pf⟩ ← iHave hyps pmt true (mayPostpone := true)
  if let some _ ← ProofModeM.trySynthInstanceQ q(FromAssumption $p .in $out $goal) then
    let LOption.some _ ← trySynthInstanceQ q(TCOr (Affine $e) (Absorbing $goal))
      | throwError "iapply: the context {e} is not affine and goal not absorbing"
    -- behave like iexact
    have rfl : Q($e ∗ □?$p $out ⊣⊢ $e ∗ □?$p $out) := q(.rfl)
    mvar.assign q($(pf).trans (assumption (Q := $goal) $(rfl)))
    return
  let pf' ← iApplyCore hyps p out goal
  mvar.assign q($(pf).trans $pf')
