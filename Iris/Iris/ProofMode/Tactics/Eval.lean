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

theorem eval_refl [BI PROP] (P : PROP) : P ⊢ P := .rfl

private structure EvalState {u} {prop : Q(Type u)} {bi : Q(BI $prop)} (e : Q($prop)) where
  {newE : Q($prop)}
  (newHyps : Hyps bi newE)
  (pf : Q($e ⊢ $newE))

private def iEvalHypsOne {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
    (evalState : @EvalState u prop bi e)
    (selTarget : SelTarget) :
    ProofModeM <| @EvalState u prop bi e := do
  match selTarget.kind with
  | .pure fvar =>
    return evalState
  | .ipm ivar =>
    let some ⟨newE, newHyps, pf⟩ ← evalState.newHyps.evalReplace ivar <|
      fun ty => do
        let newTy : Q($prop) ←
          withLocalDeclDQ (← mkFreshUserName .anonymous) q($prop) fun newTy => do
            let m ← mkFreshExprSyntheticOpaqueMVar q($ty ⊢ $newTy)
            let [g] ← evalTacticAt tac m.mvarId!
            | throwError "ieval: error"
            let some #[_, _, _, newTy] ← g.getType <&> (·.appM? ``Entails)
            | throwError "ieval: error"
            return newTy

        let pf : Q($ty ⊢ $newTy) ← mkFreshExprSyntheticOpaqueMVar q($ty ⊢ $newTy)
        match ← evalTacticAt tac pf.mvarId! with
        | [] => pure ()
        | [g] => g.assign q(eval_refl $newTy)
        | _ => throwError "ieval: error"

        return ⟨newTy, pf⟩
    | throwError "ieval: error"

    return { newE, newHyps, pf := q($(evalState.pf).trans $pf) }

private def iEvalHyps {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
    (hyps : Hyps bi e)
    (selTargets : List SelTarget) :
    ProofModeM <| @EvalState u prop bi e := do
  let mut evalState : EvalState e := { newHyps := hyps, pf := q(.rfl) }
  for selTarget in selTargets do
    evalState ← iEvalHypsOne tac evalState selTarget
  return evalState

private def iEvalGoal {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (goal : Q($prop)) :
    ProofModeM <| (newGoal : Q($prop)) × Q($newGoal ⊢ $goal) := do
  let newGoal : Q($prop) ←
    withLocalDeclDQ (← mkFreshUserName .anonymous) q($prop) fun newGoal => do
      let m ← mkFreshExprSyntheticOpaqueMVar q($newGoal ⊢ $goal)
      let [g] ← evalTacticAt tac m.mvarId!
      | throwError "ieval: error"
      let some #[_, _, _, newGoal] ← g.getType <&> (·.appM? ``Entails)
      | throwError "ieval: error"
      return newGoal

  let pf : Q($newGoal ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar q($newGoal ⊢ $goal)
  match ← evalTacticAt tac pf.mvarId! with
  | [] => pure ()
  | [g] => g.assign q(eval_refl $newGoal)
  | _ => throwError "ieval: error"

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

elab "ieval " tac:tacticSeq : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let pf ← iEvalCore hyps goal tac none
    mvar.assign pf

elab "ieval " tacs:tacticSeq " in " spats:(colGt ppSpace selPat)+ : tactic => do
  let selPats ← liftMacroM <| SelPat.parse spats

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let selTargets ← SelPat.resolve hyps selPats
    let pf ← iEvalCore hyps goal tacs selTargets
    mvar.assign pf

macro "isimp" : tactic => `(tactic| ieval simp)

macro "isimp" " in " spats:(colGt ppSpace selPat)+ : tactic =>
  `(tactic| ieval simp in $spats*)

macro "iunfold " hs:ident,+ : tactic => `(tactic| ieval (unfold $hs*))

macro "iunfold " hs:ident,+ " in " spats:(colGt ppSpace selPat)* : tactic =>
  `(tactic| ieval (unfold $hs*) in $spats*)
