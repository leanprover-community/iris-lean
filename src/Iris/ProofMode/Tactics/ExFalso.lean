/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

public import Iris.BI
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open BI

theorem exfalso [BI PROP] {P Q : PROP} (h : P ⊢ False) : P ⊢ Q := h.trans false_elim

public meta section
open Lean Elab.Tactic Meta Qq

elab "iexfalso" : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let m ← addBIGoal hyps q(iprop(False))
  mvar.assign q(exfalso (Q := $goal) $m)
