/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal
-/
module
public import Iris.ProofMode.Tactics.RevertIntro

namespace Iris.ProofMode

open Lean Meta Elab.Tactic Qq

public meta section

/--
  Apply Löb induction in the current goal.

  All spatial hypothesis are generalized in the induction hypothesis so that
  this one can be included in the intuitionistic context.

  Optionally, other variables can be generalized over through the
  `generalizing selPat*` syntax.
-/
elab  "iloeb" "as" IH:binderIdent "generalizing" hs:(colGt selPat)* : tactic => do
  let pats ← Elab.liftMacroM <| SelPat.parse hs
  ProofModeM.runTactic fun mvid {hyps, goal, ..} => do
    let targets : List SelTarget ← SelPat.resolve hyps (pats ++ [.spatial])
    let expr ← iRevertIntro hyps goal targets fun {prop _ _} hyps goal k => do
      let some _ ← ProofModeM.trySynthInstanceQ q(BI.BILoeb $prop)
        | throwError m!"iloeb: no `{←ppExpr q(BI.BILoeb $prop)}` instance found"
      let pf := q(BI.loeb_wand_intuitionistically (P := $goal))
      let pf' ← do
        -- We have applied BI.loeb_wand_intuitionistically
        let goal := q(iprop(□ (□ ▷ $goal -∗ $goal)))
        iModIntroCore hyps goal (← `(_)) fun hyps goal => do
        iIntroCore hyps goal [(IH, .intro <| .intuitionistic <| .one IH)] (k · · addBIGoal)
      return q($(pf').trans $pf)

    mvid.assign expr

macro "iloeb" "as" IH:binderIdent : tactic => `(tactic | iloeb as $IH generalizing)
