/-
Copyright (c) 2026 Yunsong Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Basic
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.ClassesMake
public meta import Iris.ProofMode.Tactics.RevertIntro

namespace Iris.ProofMode

public meta section
open BI Std Lean Elab Tactic Meta Qq

private def iInductionCore {u} {prop : Q(Type $u)} {bi} {e : Q($prop)}
    (hyps : Hyps bi e) (goal : Q($prop)) :
    ProofModeM (Q($e ⊢ $goal)) := sorry

/--
  Given a collection of hypotheses (`hyps`) and a free variable `fvar`, return
  the subset of hypotheses in `hyps` that contains the `fvar`.
-/
private def iHypsContaining {u} {prop : Q(Type $u)} {bi} {e : Q($prop)}
    (hyps : Hyps bi e) (fvar : FVarId) : List SelTarget :=
  let ivars := hyps.spatialIVarIds ++ hyps.intuitionisticIVarIds

  let containing := ivars.filter fun ivar =>
    match hyps.getDecl? ivar with
    | some (_, _, _, ty) => ty.containsFVar fvar
    | none => false

  containing.map (fun ivar => { kind := .ipm ivar, explicit := false })

elab "iinduction" colGt x:ident : tactic => do
  -- Get the ID of the variable on which induction is being performed
  let fvar ← getFVarId x

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    -- Find all hypotheses that contain the variable being performed induction on
    let targets := iHypsContaining hyps fvar

    -- Revert all hypotheses in the list
    let pf ← iRevertCore targets hyps goal (

      let names : List (Syntax × IntroPat) := ← targets.mapM (fun
      | {kind := .pure id, ..} => do
          let name ← Lean.mkIdent <$> id.getUserName
          let ident ← `(binderIdent| $name:ident)
          return (name, IntroPat.intro <| .pure ident)
      | {kind := .ipm ivar, ..} => do
          let name ← Lean.mkIdent <$> (hyps.getUserName? ivar).getM
          let ident ← `(binderIdent| $name:ident)
          return (name, IntroPat.intro <| (if ivar.persistent? then iCasesPat.intuitionistic else id) <| .one ident)
      )

      -- The function takes the hypotheses and goal after reverting
      fun hyps' goal' => do
        -- Create a new metavariable for the proof goal upon reverting hypotheses
        let m ← mkBIGoal hyps' goal'

        -- Use built-in induction in Lean to generate the subgoals for induction
        let subgoals ← evalTacticAt (← `(tactic| induction $x:ident)) m.mvarId!

        for s in subgoals do
          s.withContext do
            let sType ← instantiateMVars (← s.getType)

            let some irisGoal := parseIrisGoal? sType
            -- This should not happen
            | throwError "iinduction: fail to parse induction subgoal"

            let casePf ← iIntroCore irisGoal.hyps irisGoal.goal names
            s.assign casePf

        return m
    )

    mvar.assign pf
