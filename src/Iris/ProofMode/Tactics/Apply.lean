/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply [BI PROP] {P P' Q O A1 : PROP}
    (h1 : P ⊣⊢ P' ∗ O) (h2 : P' ⊢ A1) [h3 : IntoWand' false false O A1 A2]
    [h4 : FromAssumption false A2 Q] : P ⊢ Q :=
  h1.mp.trans (wand_elim (h2.trans (wand_intro ((sep_mono_r h3.1).trans (wand_elim_r.trans h4.1)))))

variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
partial def iApplyCore {P} (hyps : Hyps bi P) (Q : Q($prop)) : MetaM (Q($P ⊢ $Q)) :=
  sorry

elab "iapply" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { u, prop, bi, e, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
    let uniq ← hyps.findWithInfo hyp
    let ⟨e', hyps', out, out', p, eq, pf⟩ := hyps.remove true uniq

    let A1 ← mkFreshExprMVarQ prop
    let A2 ← mkFreshExprMVarQ prop

    let intoWand' ← try? do
      synthInstanceQ q(IntoWand' false false $out $A1 $A2)

    if let some _ := intoWand' then
      let _ ← synthInstanceQ q(FromAssumption false $A2 $goal)

      let m : Q($e' ⊢ $A1) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { u, prop, bi, e := e', hyps := hyps', goal := q($A1), .. }

      mvar.assign q(apply (Q := $goal) $pf $m)
      replaceMainGoal [m.mvarId!]
    else
      let _ ← synthInstanceQ q(FromAssumption $p $out' $goal)
      let _ ← synthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))

      mvar.assign q(assumption (Q := $goal) $pf)
      replaceMainGoal []
