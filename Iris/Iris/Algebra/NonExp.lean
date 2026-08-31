/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.Algebra.OFE

namespace Iris

open Lean Elab Tactic Meta Iris.Std

meta def nonexpLemmas : MetaM (Array Name) := do
  let env ← getEnv
  return (nonexpExt.getState env).reverse

/-- Does `e` use the pointwise (`∀`) OFE instance? -/
meta def distIsForall (e : Expr) : MetaM Bool := do
  let some inst := e.getAppArgs[1]? | return false
  return inst.getAppFn.getLambdaBody.getAppFn.isConstOf ``OFE.instForallOfOFEFun

/-- Applying a hypothesis of a given type. -/
meta def applyHypStep (type : Name) (goal : MVarId) : MetaM (Option (List MVarId)) :=
  goal.withContext do
    for decl? in (← getLCtx).decls do
      if let some decl := decl? then
        if decl.type.isAppOf type then try
            match ← goal.apply decl.toExpr with
            | [] => return some []
            | head :: tail =>
              head.assumption
              return some tail
          catch _ => continue
    return none

meta def distLaterStep (goal : MVarId) : MetaM (Option (List MVarId)) :=
  applyHypStep ``OFE.DistLater goal

meta def distStep (goal : MVarId) : MetaM (Option (List MVarId)) :=
  applyHypStep ``OFE.Dist goal

meta def distInstanceStep (goal : MVarId) : MetaM (Option (List MVarId)) := do try
    match ← goal.applyConst ``OFE.Contractive.distLater_dist with
    | [] => return some []
    | head :: tail =>
      let (_, head) ← head.introN 2
      return some (head :: tail)
  catch _ => return none

meta def nonexpStep (goal : MVarId) : MetaM (Option (List MVarId)) := do
  for neLem in ← nonexpLemmas do try
      match ← goal.applyConst neLem with
      | [] => return some []
      | head :: tail =>
        let (_, head) ← head.intros
        return some (head :: tail)
    catch _ => continue
  return none

meta def tryUnfoldFn : TacticM Unit := do
  let _ ← observing? do
    let some fnArg := (← getMainTarget).getAppArgs[3]? | return
    match fnArg.getAppFn with
    | .const fn _ =>
      -- don't unfold primitives
      if not <| (`Iris.BI.BIBase).isPrefixOf fn then
        evalTactic <| ← `(tactic|unfold $(mkIdent fn); try split)
    | _ => return

meta def makeMainGoal (goal : MVarId) : TacticM Unit := do
  let goals ← getGoals
  let goals := goal :: goals.erase goal
  setGoals goals

meta def tryStep (recurse : MVarId → TacticM Unit)
    (step : MVarId → MetaM (Option (List MVarId))) (goal : MVarId) : TacticM Bool := do
  match ← step goal with
  | some newGoals =>
    replaceMainGoal newGoals
    withTraceNode `NonExp (λ _ => return m!"step succeeded") do
      discard <| newGoals.mapM recurse
    return true
  | none => return false

meta def simpThenRecurse (k : MVarId → TacticM Unit) : TacticM Bool := do
  if let some _ ← observing? (evalTactic <| ← `(tactic|simp)) then
    if let some newGoal ← observing? getMainGoal then
      k newGoal
    return true
  return false

meta partial def contractiveMain (goal : MVarId) (guarded : Bool) : TacticM Unit := do
  if ← goal.isAssigned then return
  trace[NonExp] "Goal: {← goal.getType}"
  makeMainGoal goal

  -- simplification step (includes application of Dist.rfl)
  if ← simpThenRecurse (contractiveMain · guarded) then return

  -- uses an OFE.Contractive instance
  if not guarded then
    if ← tryStep (contractiveMain · true) distInstanceStep goal then return

  -- applies an OFE.DistLater hypothesis
  if ← tryStep (contractiveMain · guarded) distLaterStep goal then return

  -- applies a non-expansive lemma
  if ← tryStep (contractiveMain · guarded) nonexpStep goal then return

  throwError "tactic 'contractive' failed"

meta partial def nonexpMain (goal : MVarId) : TacticM Unit := do
  if ← goal.isAssigned then return
  trace[NonExp] "Goal: {← goal.getType}"
  makeMainGoal goal

  -- simplification step (includes application of Dist.rfl)
  if ← simpThenRecurse nonexpMain then return

  -- applies an OFE.Dist hypothesis
  if ← tryStep nonexpMain distStep goal then return

  -- applies a non-expansive lemma
  if ← tryStep nonexpMain nonexpStep goal then return

  throwError "tactic 'nonexp' failed"

meta def contractiveSetup : TacticM Unit := do
  evalTactic <| ← `(tactic|intros)

  while ← distIsForall <| ← getMainTarget do
    evalTactic <| ← `(tactic|intro)

  tryUnfoldFn

elab "contractive" : tactic => do
  contractiveSetup
  contractiveMain (← getMainGoal) false

elab "nonexp" : tactic => do
  contractiveSetup
  nonexpMain (← getMainGoal)

meta initialize registerTraceClass `NonExp

end Iris
