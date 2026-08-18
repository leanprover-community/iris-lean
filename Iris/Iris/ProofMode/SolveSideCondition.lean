/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.SynthInstance

@[expose] public section

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Term Meta Qq

/-- Check for `PMError` and create the goal for `target`. Throws on `PMError`. -/
def mkSideConditionGoal (target : Q(Prop)) : MetaM Q($target) := do
  match ← instantiateMVars target with
  | .app (.const ``PMError _) (.lit (.strVal msg)) => throwError "{msg}"
  | _ => mkFreshExprSyntheticOpaqueMVar q($target)

/--
  Attempts to solve the side condition `target`.

  When `failOnUnsolved` is set as `true`, this function throws an error when
  the side condition cannot be solved automatically.

  Otherwise, when `failOnUnsolved` is set as `false`, the unsolved subgoals
  are added to the proof state for the user.
-/
def iSolveSidecondition (target : Q(Prop)) (failOnUnsolved := true) : ProofModeM Q($target) := do
  let pf ← mkSideConditionGoal target
  let tac ← `(tactic| (and_intros <;> (first | trivial | infer_instance | (simp [*] <;> done))))
  let gs ← (observing? <| evalTacticAt tac pf.mvarId!) <&> (·.getD [pf.mvarId!])
  if !gs.isEmpty then
    if failOnUnsolved then
      throwIPMError "failed to solve side condition {target}"
    else
      for g in gs do addMVarGoal g
  return pf

end

public meta section
open Lean Elab Tactic Term Meta Qq

/-- For side conditions in IPM type classes to be discharged automatically. -/
@[ipm_class]
class TCSideCondition (φ : Prop) : Prop where
  sidecondition : φ

def runTacticOn (mvarId : MVarId) (tac : TSyntax `tactic) : MetaM (List MVarId) :=
  TermElabM.run' (Lean.Elab.Tactic.run mvarId (evalTactic tac))

@[ipm_tactic_instance TCSideCondition _]
def solveTCSideCondition : SynthTactic := fun e => do
  let_expr TCSideCondition φ := e | return .continue
  have φ : Q(Prop) := φ
  if (← instantiateMVars φ).hasExprMVar then
    return .continue
  let s ← saveState
  let pf ← mkSideConditionGoal φ
  let tac ← `(tactic| (and_intros <;> (first | trivial | infer_instance | (simp [*] <;> done))))
  let gs ← (observing? <| runTacticOn pf.mvarId! tac) <&> (·.getD [pf.mvarId!])
  -- Successful TC synthesis if and only if the side condition is completely solved
  if gs.isEmpty then
    return .success q(⟨$pf⟩ : TCSideCondition $φ)
  else
    s.restore
    return .continue

end
