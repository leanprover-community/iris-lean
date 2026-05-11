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

inductive RevertTarget where
| lean (id : FVarId)
| pm (persistent? : Bool) (ivar : IVarId)
deriving BEq, Hashable, Repr

def RevertTarget.toSelTarget : RevertTarget → SelTarget
  | .lean id => .lean id
  | .pm _ ivar => .pm ivar

def ProofModeM.revertingTelescope {α} (mvar : MVarId)(g : IrisGoal)(hs : List RevertTarget) (k : MVarId → IrisGoal → ProofModeM (IrisGoal × α)) :
    ProofModeM (IrisGoal × α) :=
  withTraceNode `iloeb (fun _ => return s!"Reverting telescope") do
  let names : List (Syntax × IntroPat) ← hs.mapM fun
    | .lean id => do
      let name ← Lean.mkIdent <$> id.getUserName
      let ident ← `(binderIdent| $name:ident)
      return (name, .intro <| .pure ident)
    | .pm persistent? ivar =>  do
      let name ← Lean.mkIdent <$> (hyps.getUserName? ivar).getM
      let ident ← `(binderIdent| $name:ident)
      return (name, .intro <| (if persistent? then .intuitionistic else id) <| .one ident)

  -- revert hypothesis in `hs`
  let (g, mvar) ← withTraceNode `iloeb (fun _ => return m!"Reverting hypothesis {names.map (·.1.getId)}") do
    trace[iloeb] s!"Before revert: {← (liftMetaM ∘ ppExpr =<< inferType (.mvar mvar))}"
    let (g, expr) ← iRevertCore mvar g (hs.map RevertTarget.toSelTarget)
    ProofModeM.pruneSolvedGoals
    trace[iloeb] s!"After revert: {← (←ProofModeM.getUnsolvedGoals).mapM (liftMetaM ∘ ppExpr =<< MVarId.getType ·)}"
    trace[iloeb] s!"Revert returned: {←ppExpr expr}"
    pure (g, expr.mvarId!)

  -- Run tactic
  let ({hyps, goal, ..}, res) ← withTraceNode `iloeb (fun _ => return s!"Running tactic") do
    let (g, res) ← k mvar g
    ProofModeM.pruneSolvedGoals
    pure (g, res)

  -- introduce back the hypethesis in `hs`
  withTraceNode `iloeb (fun _ => return m!"Re-introducing hypothesis with {names.map (·.1.getId)}") do
    trace[iloeb] s!"Before intros: {← (←ProofModeM.getUnsolvedGoals).mapM (liftMetaM ∘ ppExpr =<< MVarId.getType ·)}"
    let mvar ← getMainGoal
    let expr ← iIntroCore hyps goal names
    ProofModeM.pruneSolvedGoals
    mvar.assign expr
    trace[iloeb] s!"After intros: {← (←ProofModeM.getUnsolvedGoals).mapM (liftMetaM ∘ ppExpr =<< MVarId.getType ·)}"
  return (g, res)

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
  ProofModeM.runTactic fun mvid g@{hyps, ..} => do
    let spatialCtx := hyps.spatialIVarIds.map (RevertTarget.pm false)
    let generalizedHs ← do
      let hs := hs.getD #[]
      let pats ← Elab.liftMacroM <| SelPat.parse hs
      let generalizedHs ← SelPat.resolve hyps pats
      generalizedHs.zip hs.toList
        |>.filterMapM fun
          | (.pm ivar, ref) => do
            if spatialCtx.contains (.pm false ivar) then
              logWarningAt ref m!"Spatial hypothesis are generalized automatically"
              return none
            else
              return some (RevertTarget.pm true ivar)
          | (.lean id, _) => return some (.lean id)

    let _ ← ProofModeM.revertingTelescope mvid g (generalizedHs ++ spatialCtx) fun mvid {u, prop, goal, hyps, ..} => do
      trace[iloeb] s!"Goals before tactic : {←(liftM ∘ ppExpr =<< MVarId.getType (←ProofModeM.getMainGoal))}"
      let x : Term := ←`(term| @BI.loeb_wand_intuitionistically _)
      let ⟨_, hyps', p, out, pf⟩ ← iHave hyps ⟨x, []⟩ true
      let pf' ← iApplyCore hyps' p out goal
      mvid.assign q($(pf).trans $pf')
      trace[iloeb] s!"Goals after applying iloeb: {←(liftM ∘ ppExpr =<< MVarId.getType (←ProofModeM.getMainGoal))}"

      let .some biloeb ← ProofModeM.trySynthInstanceQ q(BI.BILoeb $prop)
        | throwError m!"Cannot use `iloeb` if there is no `{←ppExpr q(BI.BILoeb $prop)}` instance available"
      (←ProofModeM.getMainGoal).assign biloeb
      trace[iloeb] s!"Goals after BILoeb condition dispatch: {← ((←ProofModeM.getUnsolvedGoals).mapM (liftM ∘ ppExpr =<< MVarId.getType ·))}\n{repr (←ProofModeM.getUnsolvedGoals)}"

      let pf ← iModIntroCore hyps' q(iprop(□ (□ ▷ $goal -∗ $goal))) (← `(_)) fun hyps goal => do
        addBIGoal hyps goal
      let imodGoalId ← ProofModeM.getMainGoal
      imodGoalId.assign pf
      trace[iloeb] s!"Goals after imodintro: {← ((←ProofModeM.getUnsolvedGoals).mapM (liftM ∘ ppExpr =<< MVarId.getType ·))}\n{repr (←ProofModeM.getUnsolvedGoals)}"

      let introGoalId ← ProofModeM.getMainGoal
      let some {goal, hyps, ..} := parseIrisGoal? (←introGoalId.getType)
        | throwError "Expected resulting goal to be an Iris goal"
      let expr ← iIntroCore hyps goal [(IH, .intro <| .intuitionistic <| .one IH)]
      introGoalId.assign expr
      trace[iloeb] s!"Goals after introducing {IH}: {← ((←ProofModeM.getUnsolvedGoals).mapM (liftM ∘ ppExpr =<< MVarId.getType ·))}\n{repr (←ProofModeM.getUnsolvedGoals)}"

      let some g := parseIrisGoal? (←MVarId.getType <| ←ProofModeM.getMainGoal)
        | throwError "Expected resulting goal to be an Iris goal"
      return ⟨g, ()⟩

initialize registerTraceClass `iloeb
