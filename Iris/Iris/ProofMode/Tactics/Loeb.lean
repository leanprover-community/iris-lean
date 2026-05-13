/-
Copyright (c) 2025 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal
-/
module
public import Iris.ProofMode.Tactics.Apply
public import Iris.ProofMode.Tactics.Intro
public import Iris.ProofMode.Tactics.Revert

namespace Iris.ProofMode

open Lean Meta Elab.Tactic Qq

public meta section

abbrev ProofModeContinuation(u : Level) := ∀ {prop : Q(Type u)}{bi : Q(BI $prop)}{e : Q($prop)}(_hyps : Hyps bi e)(goal: Q($prop)),
  ProofModeM Q($e ⊢ $goal)

def ProofModeM.revertingTelescope
  {u : Level}{prop: Q(Type $u)}{bi : Q(BI $prop)}{e : Q($prop)}(hyps : Hyps bi e)(goal: Q($prop))
  (hs : List SelTarget)
  (k : ∀ {prop : Q(Type u)}{bi : Q(BI $prop)}{e : Q($prop)}(_hyps : Hyps bi e)(goal: Q($prop)), ProofModeContinuation u → ProofModeM Q($e ⊢ $goal))
   : ProofModeM Q($e ⊢ $goal) := do
  let names : List (Syntax × IntroPat) ← hs.mapM fun
    | {target := .pure id, ..} => do
      let name ← Lean.mkIdent <$> id.getUserName
      let ident ← `(binderIdent| $name:ident)
      return (name, .intro <| .pure ident)
    | {target := .ipm ivar, persistent?, ..} =>  do
      let name ← Lean.mkIdent <$> (hyps.getUserName? ivar).getM
      let ident ← `(binderIdent| $name:ident)
      return (name, .intro <| (if persistent? then .intuitionistic else id) <| .one ident)
  trace[iloeb] s!"Calling reverting telescope with {names.map (·.1)} on context {←ppExpr hyps.tm}\n⊢\n{←ppExpr goal}"

  iRevertCore hs hyps goal fun hyps goal => do
  k hyps goal fun hyps goal => do
  iIntroCore hyps goal names

/--
  Apply Löb induction in the current goal.

  All spatial hypothesis are generalized in the induction hypothesis so that
  this one can be included in the intuitionistic context.

  Optionally, other variables can be generalized over through the
  `generalizing selPat*` syntax.
-/
syntax (name := iloeb) "iloeb " " as " binderIdent (" generalizing " (ppSpace colGt selPat)+)? : tactic

@[inherit_doc iloeb]
elab_rules : tactic
| `(tactic| iloeb as $IH:binderIdent $[generalizing $[$hs:selPat]*]? ) => do
  ProofModeM.runTactic fun mvid {hyps, goal, ..} => do
    let spatialCtx := hyps.spatialIVarIds.map ({target := .ipm ·, explicit := false, persistent? := false})
    let generalizedHs ← do
      let hs := hs.getD #[]
      let pats ← Elab.liftMacroM <| SelPat.parse hs
      let generalizedHs ← SelPat.resolve hyps pats
      generalizedHs.zip hs.toList
        |>.filterMapM fun (tgt, ref) =>
          match tgt.target with
          | .ipm ivar => do
            if spatialCtx.map (·.target) |>.contains (.ipm ivar) then
              logWarningAt ref m!"Spatial hypothesis are generalized automatically by iloeb"
              return none
            else
              return some ({target := .ipm ivar, explicit := false, persistent? := true})
          | .pure id => return some ({target := .pure id, explicit := false, persistent? := true})

    let expr ← ProofModeM.revertingTelescope hyps goal (generalizedHs ++ spatialCtx) fun {prop _ _} hyps goal k => do
      let some _ ← ProofModeM.trySynthInstanceQ q(BI.BILoeb $prop)
        | throwError m!"Cannot use `iloeb` if there is no `{←ppExpr q(BI.BILoeb $prop)}` instance available"
      let pf := q(BI.loeb_wand_intuitionistically (P := $goal))
      let pf' ← do
        -- We have applied BI.loeb_wand_intuitionistically
        let goal := q(iprop(□ (□ ▷ $goal -∗ $goal)))
        iModIntroCore hyps goal (← `(_)) fun hyps goal => do
        iIntroCore hyps goal [(IH, .intro <| .intuitionistic <| .one IH)] fun hyps goal =>
        k hyps goal
      return q($(pf').trans $pf)

    mvid.assign expr

initialize registerTraceClass `iloeb
