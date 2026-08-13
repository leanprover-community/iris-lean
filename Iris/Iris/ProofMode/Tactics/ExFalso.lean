/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module -- shake: keep-all

public import Iris.ProofMode.Tactics.Basic -- shake: keep

namespace Iris.ProofMode

public section
open BI

@[rocq_alias tac_ex_falso]
theorem exfalso [BI PROP] {P Q : PROP} (h : P ⊢ False) : P ⊢ Q := h.trans false_elim

public meta section
open Lean Elab.Tactic Meta Qq

/--
  `iexfalso` changes the goal to `False`.
-/
elab "iexfalso" : tactic => do
  ProofModeM.runTactic `iexfalso λ mvar { hyps, goal, .. } => do
    let m ← addBIGoal hyps q(iprop(False))
    mvar.assign q(exfalso (Q := $goal) $m)
