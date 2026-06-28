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

private def iEvalCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
    (selPats : Option <| List SelPat) : ProofModeM Q($e ⊢ $goal) := do
  sorry

elab "ieval " tac:tacticSeq : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let pf ← iEvalCore hyps goal tac none
    mvar.assign pf

elab "ieval " tacs:tacticSeq " in " spats:(colGt ppSpace selPat)* : tactic => do
  let selPats ← liftMacroM <| SelPat.parse spats
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let pf ← iEvalCore hyps goal tacs selPats
    mvar.assign pf

macro "isimp" : tactic => `(tactic| ieval simp)

macro "isimp" " in " spats:(colGt ppSpace selPat)* : tactic =>
  `(tactic| ieval simp in $spats*)

macro "iunfold " hs:ident,+ : tactic => `(tactic| ieval (unfold $hs*))

macro "iunfold " hs:ident,+ " in " spats:(colGt ppSpace selPat)* : tactic =>
  `(tactic| ieval (unfold $hs*) in $spats*)
