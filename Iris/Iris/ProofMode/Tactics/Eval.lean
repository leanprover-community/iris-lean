/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Patterns.SelPattern
public meta import Iris.ProofMode.ProofModeM

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI

private structure EvalState {u} {prop : Q(Type u)} {bi : Q(BI $prop)} (e : Q($prop)) where
  {newE : Q($prop)}
  (newHyps : Hyps bi newE)
  (pf : Q($e ⊢ $newE))

/-- Iteratively apply the supplied tactic sequence to the selection targets -/
private def iEvalHyps {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
    (hyps : Hyps bi e)
    (selTargets : List SelTarget) :
    ProofModeM <| @EvalState u prop bi e := do
  let mut evalState : EvalState e := { newHyps := hyps, pf := q(.rfl) }
  for selTarget in selTargets do
    evalState ← match selTarget.kind with
    | .pure _ =>
      throwError "ieval: pure hypotheses in the selection pattern is not supported"
    | .ipm ivar =>
      let some ⟨newE, newHyps, pf⟩ ← evalState.newHyps.evalReplace ivar <| fun ty => do
        -- Find the new hypothesis obtained upon applying the tactic sequence
        let newTy : Q($prop) ←
          withLocalDeclDQ (← mkFreshUserName .anonymous) q($prop) fun newTy => do
            let [g] ← mkFreshExprSyntheticOpaqueMVar q($ty ⊢ $newTy) >>= (evalTacticAt tac ·.mvarId!)
            | throwError "ieval: the supplied tactic does not produce exactly one subgoal"
            let some #[_, _, newTy, _] ← g.getType <&> (·.appM? ``Entails)
            | throwError m!"ieval: the goal is not Iris entailment upon applying the supplied tactic"
            return newTy

        -- The tactic sequence results in the proof goal being *weakened*
        let pf : Q($ty ⊢ $newTy) ← mkFreshExprSyntheticOpaqueMVar q($ty ⊢ $newTy)
        match ← evalTacticAt tac pf.mvarId! with
        | [] => pure ()
        | [g] => g.assign (q(.rfl) : Q($newTy ⊢ $newTy))
        | _ => throwError "ieval: the supplied tactic does not produce exactly one subgoal"

        return ⟨newTy, pf⟩
      | throwError m!"ieval: unable to find the hypothesis {ivar.name} in the context"
      pure { newE, newHyps, pf := q($(evalState.pf).trans $pf) }

  return evalState

/-- Apply the supplied tactic sequence to the proof goal -/
private def iEvalGoal {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (goal : Q($prop)) :
    ProofModeM <| (newGoal : Q($prop)) × Q($newGoal ⊢ $goal) := do
  -- Find the new proof goal obtained upon applying the tactic sequence
  let newGoal : Q($prop) ←
    withLocalDeclDQ (← mkFreshUserName .anonymous) q($prop) fun newGoal => do
      let m ← mkFreshExprSyntheticOpaqueMVar q($newGoal ⊢ $goal)
      let [g] ← evalTacticAt tac m.mvarId!
      | throwError "ieval: the supplied tactic does not produce exactly one subgoal"
      let some #[_, _, _, newGoal] ← g.getType <&> (·.appM? ``Entails)
      | throwError m!"ieval: the goal is not Iris entailment upon applying the supplied tactic"
      return newGoal

  -- The tactic sequence results in the proof goal being *strengthened*
  let pf : Q($newGoal ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar q($newGoal ⊢ $goal)
  match ← evalTacticAt tac pf.mvarId! with
  | [] => pure ()
  | [g] => g.assign (q(.rfl) : Q($newGoal ⊢ $newGoal))
  | _ => throwError "ieval: the supplied tactic does not produce exactly one subgoal"

  return ⟨newGoal, pf⟩

private def iEvalCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
    (selTargets : Option <| List SelTarget) : ProofModeM Q($e ⊢ $goal) := do
  match selTargets with
  -- No selection pattern given, apply the tactics to the proof goal
  | none =>
    let ⟨newGoal, pf⟩ ← iEvalGoal tac goal
    let pf' ← addBIGoal hyps newGoal
    return q($(pf').trans $pf)
  -- Selection patterns given, apply the tactics to the chosen hypotheses
  | some selTargets =>
    let evalState ← iEvalHyps tac hyps selTargets
    let pf' ← addBIGoal evalState.newHyps goal
    return q($(evalState.pf).trans $pf')

elab "ieval " "(" tac:tacticSeq ")" : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let pf ← iEvalCore hyps goal tac none
    mvar.assign pf

elab "ieval " "(" tacs:tacticSeq ")" " in " spats:(colGt ppSpace selPat)+ : tactic => do
  let selPats ← liftMacroM <| SelPat.parse spats

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let selTargets ← SelPat.resolve hyps selPats
    let pf ← iEvalCore hyps goal tacs selTargets
    mvar.assign pf

macro "isimp" : tactic => `(tactic| ieval (simp))

macro "isimp" " in " spats:(colGt ppSpace selPat)+ : tactic =>
  `(tactic| ieval (simp) in $spats*)

macro "iunfold " hs:ident,+ : tactic => `(tactic| ieval (unfold $hs*))

macro "iunfold " hs:ident,+ " in " spats:(colGt ppSpace selPat)* : tactic =>
  `(tactic| ieval (unfold $hs*) in $spats*)
