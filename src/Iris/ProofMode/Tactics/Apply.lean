/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

-- focus on n = 1 case for now

#check assumption

/-
Lemma tac_apply Δ i p R P1 P2 :
  envs_lookup i Δ = Some (p, R) →
  IntoWand p false R P1 P2 →
  envs_entails (envs_delete true i p Δ) P1 → envs_entails Δ P2.
-/

-- New goal : P' ⊢ A1
/-theorem apply [BI PROP] {p : Bool} {P P' Q O A1 : PROP}
    (h1 : P ⊣⊢ P' ∗ O) [h2 : IntoWand p false O A1 A2] (h3 : P' ⊢ A1)
    (h4 : A2 ⊢ Q) : P ⊢ Q :=
  h1.mp.trans (wand_elim (h3.trans sorry))

variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
partial def iApplyCore {P} (hyps : Hyps bi P) (Q : Q($prop)) : MetaM (Q($P ⊢ $Q)) :=
  sorry-/

elab "iapply" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { u, prop, bi, e, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
    let uniq ← hyps.findWithInfo hyp
    let ⟨e', hyps', out, out', p, eq, pf⟩ := hyps.remove true uniq

    let A1 ← mkFreshExprMVarQ prop
    let A2 ← mkFreshExprMVarQ prop

    let fromWand ← try? do -- todo: is this the correct typeclass to use?
      synthInstanceQ q(FromWand $out $A1 $A2)

    if let none := fromWand then
      let _ ← synthInstanceQ q(FromAssumption $p $out' $goal)
      let _ ← synthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))

      mvar.assign q(assumption (Q := $goal) $pf)
      replaceMainGoal []
    else
      -- have : A1 -∗ A2 ⊢ out

      let m : Q($e' ⊢ $A1) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { u, prop, bi, e := e', hyps := hyps', goal := q($A1), .. }

      --mvar.assign q(assumption (Q := $goal) $m)
      replaceMainGoal [m.mvarId!]
