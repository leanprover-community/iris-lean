/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

private theorem clear_spatial [BI PROP] {P P' A Q : PROP} [TCOr (Affine A) (Absorbing Q)]
    (h_rem : P ⊣⊢ P' ∗ A) (h : P' ⊢ Q) : P ⊢ Q :=
  h_rem.1.trans <| (sep_mono_l h).trans sep_elim_l

private theorem clear_intuitionistic [BI PROP] {P P' A Q : PROP}
    (h_rem : P ⊣⊢ P' ∗ □ A) (h : P' ⊢ Q) : P ⊢ Q := clear_spatial h_rem h

def iClearCore {prop : Q(Type u)} (_bi : Q(BI $prop)) (e e' : Q($prop))
    (p : Q(Bool)) (out goal : Q($prop))
    (pf : Q($e ⊣⊢ $e' ∗ □?$p $out)) : ProofModeM Q(($e' ⊢ $goal) → $e ⊢ $goal) := do
    match matchBool p with
    | .inl _ => return q(clear_intuitionistic (Q := $goal) $pf)
    | .inr _ =>
      let .some _ ← trySynthInstanceQ q(TCOr (Affine $out) (Absorbing $goal))
        | throwError "iclear: {out} is not affine and the goal not absorbing"
      return q(clear_spatial (A:=$out) $pf)

elab "iclear" colGt hyp:ident : tactic => do
  ProofModeM.runTactic λ mvar { bi, e, hyps, goal, .. } => do

  let uniq ← hyps.findWithInfo hyp
  let ⟨e', hyps', _, out', p, _, pf⟩ := hyps.remove true uniq
  let m ← addBIGoal hyps' goal
  mvar.assign ((← iClearCore bi e e' p out' goal pf).app m)
