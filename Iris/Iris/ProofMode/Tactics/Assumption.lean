/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

import Iris.BI
import Iris.ProofMode.Classes
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
public section
open BI Std

@[rocq_alias tac_assumption]
theorem assumption [BI PROP] {p : Bool} {P P' A Q : PROP} [inst : FromAssumption p .in A Q]
    [TCOr (Affine P') (Absorbing Q)] (h : P ⊣⊢ P' ∗ □?p A) : P ⊢ Q := calc
  P ⊢ P' ∗ □?p A := h.mp
  _ ⊢ P' ∗ Q     := sep_mono_right inst.from_assumption
  _ ⊢ Q          := sep_elim_right

#rocq_ignore tac_assumption_rocq "iAssumptionCoq is not ported to Lean"

public meta section
open Lean Elab Tactic Meta Qq

/--
  `iassumption` solves the goal with a matching hypothesis from the
  intuitionistic or spatial context.
-/
elab "iassumption" : tactic => do
  ProofModeM.runTactic `iassumption λ mvar { hyps, goal, .. } => do

  if goal.isMVar then
    throwIPMError "goal is a mvar, use iaccu instead"

  let some ⟨inst, e', _, out, ty, b, _, pf⟩ ←
    hyps.removeG true fun _ _ b ty => do
      ProofModeM.trySynthInstanceQ q(FromAssumption $b .in $ty $goal)
    | throwIPMError "no matching assumption"
  let _ : Q(FromAssumption $b .in $ty $goal) := inst
  have : $out =Q iprop(□?$b $ty) := ⟨⟩
  let .some _ ← trySynthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))
    | throwIPMError "context is not affine or goal is not absorbing"
  mvar.assign q(assumption (Q := $goal) $pf)

macro_rules | `(tactic| itrivial) => `(tactic| (try iassumption) <;> done)
