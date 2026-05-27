/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

import Iris.BI
public import Iris.ProofMode.Classes
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public meta section
open BI Lean Elab Tactic Meta Qq Std

/--
Try to solve the provided goal using `itrivial`.
-/
def iTrivial {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e)
  (goal : Q($prop)) : ProofModeM (Option Q($e ⊢ $goal)) := do
  let m ← mkBIGoal hyps goal
  try
    let gs ← withSuppressedMessages <| evalTacticAt (← `(tactic | itrivial)) m.mvarId!
    -- itrivial succeed
    if gs.length == 0 then return some m
  catch _ =>
    -- itrivial failed, so we fail
    return none
  -- itrivial succeed, but did not fully solve the goal. This should not happen.
  throwError "itrivial: itrivial should not make partial progress"
