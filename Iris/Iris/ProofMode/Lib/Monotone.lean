/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.Instances.Lib.Monotone
public meta import Iris.ProofMode
meta import Lean.Meta.Tactic.Split
meta import Lean.Meta.Tactic.Repeat

namespace Iris

open Lean Elab Tactic Meta Iris.Std ProofMode Term Macro

meta partial def etaExpand (e : Expr) : TacticM Unit := do
  let ty ← whnf (← instantiateMVars (← inferType e))
  if ty.isAppOf ``Prod then
    let stx ← exprToSyntax e
    evalTactic (← `(tactic| rw [← Prod.eta $stx]))
    etaExpand (← mkAppM ``Prod.fst #[e])
    etaExpand (← mkAppM ``Prod.snd #[e])

/-- The RHS of the goal's entailment. -/
meta def goalRHS? (goal : MVarId) : MetaM (Option Expr) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  target.withApp fun _ args => pure args[3]?

/-- If the goal contains a pattern match, case on the discriminant. -/
meta def splitStep (xType : Expr) (name : Name) (goal : MVarId) : TacticM (List MVarId) := do
  let some wandGoal ← goalRHS? goal | throwError "monotone: no match to split"

  -- find discriminants
  let some e ← findSplit? wandGoal .match | throwError "monotone: no match to split"
  let some app ← matchMatcherApp? e | throwError "monotone: no match to split"
  if app.discrs.isEmpty then throwError "monotone: no match to split"
  let stxs ← goal.withContext (app.discrs.mapM exprToSyntax : TermElabM (Array Term))

  let goals ← Elab.Tactic.run goal <| evalTactic <| ← `(tactic| cases $[$stxs:term],*)
  let goals ← (goals.mapM Split.simpMatchTarget : MetaM (List MVarId))

  -- keep `x` available for use by `irevert` by renaming
  goals.mapM fun g => g.withContext do
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && (← isDefEq decl.type xType) then
        return ← g.rename decl.fvarId name
    return g

/-- Check if `fn` is a primitive connective that can be dealt with by typeclass search. -/
meta def isPrimitiveConnective (fn : Name) : MetaM Bool := do
  return (`Iris.BI.BIBase).isPrefixOf fn || (← getProjectionFnInfo? fn).any (·.fromClass)

meta def unfoldStep (goal : MVarId) : TacticM (List MVarId) := do
  let some wandGoal ← goalRHS? goal | throwError "monotone: nothing to unfold"
  let some fn := wandGoal.withApp fun _ args => (args[2]?.map (·.getAppFn)).bind (·.constName?)
    | throwError "monotone: nothing to unfold"
  if ← isPrimitiveConnective fn then
    throwError "monotone: {fn} is a primitive connective"
  run goal <| evalTactic <| ← `(tactic|unfold $(mkIdent fn); try simp)

/-- Split if possible, otherwise unfold the goal -/
meta def monotoneStep (xType : Expr) (name : Name) (goal : MVarId) : TacticM (List MVarId) := do
  if let some goals ← observing? (splitStep xType name goal) then
    return goals
  else
    unfoldStep goal

elab "monotone" : tactic => do
  let H ← `(icasesPat| H)
  let H' ← `(selPat| H)
  let x ← `(ident| x)

  -- introduce hypotheses
  evalTactic <| ← `(tactic|intros; iintro #$H %$x)

  let xType ← withMainContext <| inferType (mkFVar (← getFVarId x))

  -- eta-expand the argument
  withMainContext do
    let e := mkFVar (← getFVarId x)
    etaExpand e

  -- unfold and split as much as possible
  let newGoals ← repeat' (monotoneStep xType x.getId) [← getMainGoal]
  setGoals newGoals

  -- get the goal in the right form and use typeclass search
  evalTactic <| ← `(tactic|all_goals (irevert $H' %$x; apply MonoInstances.MonotonePred.monotone))
