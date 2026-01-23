/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Assumption

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

elab "iexact" colGt hyp:ident : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let uniq ← hyps.findWithInfo hyp
  let ⟨e', _, _, out, p, _, pf⟩ := hyps.remove true uniq

  let some _ ← ProofModeM.trySynthInstanceQ q(FromAssumption $p .in $out $goal)
    | throwError "iexact: cannot unify {out} and {goal}"
  let .some _ ← trySynthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))
    | throwError "iexact: context is not affine or goal is not absorbing"

  mvar.assign q(assumption (Q := $goal) $pf)
