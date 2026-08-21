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

def sideconditionTactic : MetaM (TSyntax `tactic) :=
  `(tactic| (and_intros <;>
     (first | trivial | infer_instance | (simp [*] <;> done))))

/--
  Attempts to solve the side condition `target`.

  When `failOnUnsolved` is set as `true`, this function throws an error when
  the side condition cannot be solved automatically.

  Otherwise, when `failOnUnsolved` is set as `false`, the unsolved subgoals
  are added to the proof state for the user.
-/
def iSolveSidecondition (target : Q(Prop)) (failOnUnsolved := true) : ProofModeM Q($target) := do
  let pf ← mkSideConditionGoal target
  let tac ← sideconditionTactic
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
  TermElabM.run' <| run mvarId (withoutRecover <| evalTactic tac)

@[ipm_tactic_instance TCSideCondition _]
def solveTCSideCondition : SynthTactic := fun e => do
  let_expr TCSideCondition φ := e | return .continue
  have φ : Q(Prop) := φ
  -- The side condition may contain metavariables but not itself be one
  if (← instantiateMVars φ).getAppFn.isMVar then
    return .continue
  let s ← saveState
  -- new context depth to prevent instantiation of mvars
  let res ← withNewMCtxDepth do
    let pf ← mkSideConditionGoal φ
    let tac ← sideconditionTactic
    let some gs ← observing? <| runTacticOn pf.mvarId! tac
      | return none
    if gs.isEmpty then
      return some <| ← instantiateMVars pf
    else
      return none
  match res with
  | some pf =>
    have pf : Q($φ) := pf
    return .success q(⟨$pf⟩ : TCSideCondition $φ)
  | none => s.restore; return .continue

end
