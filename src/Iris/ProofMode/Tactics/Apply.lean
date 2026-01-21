/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Michael Sammler
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Assumption
import Iris.ProofMode.Tactics.Split
import Iris.ProofMode.Tactics.Have

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply [BI PROP] {p} {P Q P' Q1 R : PROP}
    (h1 : P ⊣⊢ P' ∗ □?p Q) (h2 : P' ⊢ Q1)
    [h3 : IntoWand p false Q .out Q1 .in R] : P ⊢ R :=
      h1.1.trans (Entails.trans (sep_mono_l h2) (wand_elim' h3.1))

partial def iApplyCore {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e) (goal : Q($prop)) (uniq : Name) : ProofModeM Q($e ⊢ $goal) := do
  let ⟨_, hyps', _, out, p, _, pf⟩ := hyps.remove true uniq
  let A ← mkFreshExprMVarQ q($prop)
  if let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $A .in $goal) then
     let pf' ← addBIGoal hyps' A
     return q(apply $pf $pf')

  let some ⟨_, hyps'', pf''⟩ ← try? <| iSpecializeCore hyps uniq [.goal [] .anonymous] | throwError m!"iapply: cannot apply {out} to {goal}"
  let pf''' ← iApplyCore hyps'' goal uniq
  return q($(pf'').trans $pf''')

elab "iapply" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let ⟨uniq, _, hyps, pf⟩ ← iHave hyps pmt (← `(binderIdent|_)) true (mayPostpone := true)
  let ⟨e', _, _, out, p, _, pf'⟩ := hyps.remove true uniq
  if let some _ ← ProofModeM.trySynthInstanceQ q(FromAssumption $p .in $out $goal) then
    if let LOption.some _ ← trySynthInstanceQ q(TCOr (Affine $e') (Absorbing $goal)) then
      -- behave like iexact
      mvar.assign q($(pf).trans (assumption (Q := $goal) $pf'))
      return
  let pf' ← iApplyCore hyps goal uniq
  mvar.assign q($(pf).trans $pf')
