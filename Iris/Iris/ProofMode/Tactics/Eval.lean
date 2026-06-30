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
open Lean Elab Tactic Meta Qq

private def iEvalHyps {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
    (hyps : Hyps bi e)
    (selTargets : List SelTarget) :
    ProofModeM <| (newE : Q($prop)) × (newHyps : Hyps bi newE) × Q($e ⊢ $newE) := do
  sorry

private def iEvalGoal {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (goal : Q($prop)) :
    ProofModeM <| (newGoal : Q($prop)) × Q($newGoal ⊢ $goal) := do
  sorry

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
    let ⟨_, newHyps, pf⟩ ← iEvalHyps tac hyps selTargets
    let pf' ← addBIGoal newHyps goal
    return q($(pf).trans $pf')

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
