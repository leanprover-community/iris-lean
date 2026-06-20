/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal
-/
module

public import Iris.ProofMode.Tactics.Revert
public import Iris.ProofMode.Tactics.RevertIntro

namespace Iris.ProofMode

open Lean Meta Elab.Tactic Qq

public meta section

syntax (name := iloeb) "iloeb" " as " binderIdent (generalizingSelPats)? : tactic

/--
  `iloeb as IH generalizing hs` applies Löb induction in the current goal
  using the induction hypothesis `IH`, optionally with other variables can be
  generalised over through the `generalizing selPat*` syntax. All spatial
  hypothesis are generalised in the induction hypothesis. Hypotheses dependent
  on those included in the selection pattern `hs` must also themselves be
  included in `hs`.

  `iloeb as IH generalizing! hs` is the same as `iloeb as IH generalizing hs`,
  except that all hypotheses dependent on any hypothesis in the selection
  pattern `hs` are implicitly reverted.
-/
elab_rules : tactic
  | `(tactic| iloeb as $IH:binderIdent generalizing $hs:selPat*) => do
    let pats ← Elab.liftMacroM <| SelPat.parse hs

    ProofModeM.runTactic fun mvid { hyps, goal, .. } => do
      -- Parse the selection patterns provided by the tactic user
      let targets : List SelTarget ← SelPat.resolve hyps (pats ++ [.spatial])

      -- Check for dependencies with the hypotheses in the selection targets
      checkDependentHyps "iloeb" hyps targets none hs
        (fun pats => `(tactic| iloeb as $IH generalizing $pats*))
        (fun pats => `(tactic| iloeb as $IH generalizing! $pats*))

      let expr ← iRevertIntro hyps goal targets fun {prop _ _} hyps goal k => do
        let some _ ← ProofModeM.trySynthInstanceQ q(BI.BILoeb $prop)
          | throwError m!"iloeb: no `{←ppExpr q(BI.BILoeb $prop)}` instance found"
        let pf := q(BI.loeb_wand_intuitionistically (P := $goal))
        let pf' ← do
          -- We have applied `BI.loeb_wand_intuitionistically`
          let goal := q(iprop(□ (□ ▷ $goal -∗ $goal)))
          iModIntroCore hyps goal (← `(_)) fun hyps goal => do
          iIntroCore hyps goal [(IH, .intro <| .intuitionistic <| .one IH)] (k · · addBIGoal)

        return q($(pf').trans $pf)

      mvid.assign expr
  | `(tactic| iloeb as $IH:binderIdent $[generalizing! $hs:selPat*]?) => do
    ProofModeM.runTactic fun mvid { hyps, goal, .. } => do
      let targets ← do match hs with
      | none =>
        SelPat.resolve hyps [.spatial]
      | some hs =>
        -- Parse the selection patterns provided by the tactic user
        let pats ← Elab.liftMacroM <| SelPat.parse hs
        let targets ← SelPat.resolve hyps (pats ++ [.spatial])
        -- Find all dependent hypotheses
        let ⟨_, missingIrisHyps, allPureFVarsSorted⟩ ← getDependentHyps hyps targets none false
        -- Obtain the selection targets, including dependent ones
        pure <| getCompleteSelTargets targets missingIrisHyps allPureFVarsSorted

      let expr ← iRevertIntro hyps goal targets fun {prop _ _} hyps goal k => do
        let some _ ← ProofModeM.trySynthInstanceQ q(BI.BILoeb $prop)
          | throwError m!"iloeb: no `{←ppExpr q(BI.BILoeb $prop)}` instance found"
        let pf := q(BI.loeb_wand_intuitionistically (P := $goal))
        let pf' ← do
          -- We have applied `BI.loeb_wand_intuitionistically`
          let goal := q(iprop(□ (□ ▷ $goal -∗ $goal)))
          iModIntroCore hyps goal (← `(_)) fun hyps goal => do
          iIntroCore hyps goal [(IH, .intro <| .intuitionistic <| .one IH)] (k · · addBIGoal)

        return q($(pf').trans $pf)

      mvid.assign expr
