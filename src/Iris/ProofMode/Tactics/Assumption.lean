/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem assumption [BI PROP] {p : Bool} {P P' A Q : PROP} [inst : FromAssumption p .in A Q]
  [TCOr (Affine P') (Absorbing Q)] (h : P ⊣⊢ P' ∗ □?p A) : P ⊢ Q :=
  h.1.trans <| (sep_mono_r inst.1).trans sep_elim_r

elab "iassumption" : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do

  let some ⟨inst, e', _, out, ty, b, _, pf⟩ ←
    hyps.removeG true fun _ _ b ty => do
      ProofModeM.trySynthInstanceQ q(FromAssumption $b .in $ty $goal)
    | throwError "iassumption: no matching assumption"
  let _ : Q(FromAssumption $b .in $ty $goal) := inst
  have : $out =Q iprop(□?$b $ty) := ⟨⟩
  let .some _ ← trySynthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))
    | throwError "iassumption: context is not affine or goal is not absorbing"
  mvar.assign q(assumption (Q := $goal) $pf)
