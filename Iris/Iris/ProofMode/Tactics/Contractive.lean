/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.Algebra.OFE

namespace Iris

open Lean Elab Tactic Meta Iris.Std

meta def nonexpLemmas : MetaM (Array Name) := do
  let env ← getEnv
  return (nonexpExt.getState env).reverse

meta def distIsForall (expr : Expr) : MetaM Bool := do
  expr.withApp <| λ _ distArgs =>
    distArgs[1]!.withApp <| λ ofeFn _ => do
      return ofeFn.getLambdaBody.getAppFn.isConstOf ``OFE.instForallOfOFEFun

meta def nonexpStep (goal : MVarId) : MetaM (Option (List MVarId)) := do
  for neLem in ← nonexpLemmas do try
      let newGoals ← goal.applyConst neLem
      return (← newGoals[0]!.intros).snd :: newGoals.tail!
    catch _ => continue
  return none

meta def distInstanceStep (goal : MVarId) : MetaM (Option (List MVarId)) := do try
    let mut newGoals ← goal.applyConst ``OFE.Contractive.distLater_dist
    return (← newGoals[0]!.introN 2).snd :: newGoals.tail!
  catch _ => return none

meta def distLaterStep (goal : MVarId) : MetaM (Option (List MVarId)) :=
  goal.withContext do
    let ctx ← getLCtx
    for decl? in ctx.decls do
      if let some decl := decl? then
        if decl.type.isAppOf ``OFE.DistLater then try
            let newGoals ← goal.apply decl.toExpr
            newGoals.head!.assumption
            return some newGoals.tail!
          catch _ => continue
    return none

meta def distStep (goal : MVarId) : MetaM (Option (List MVarId)) := do
  goal.withContext do
    let ctx ← getLCtx
    for decl? in ctx.decls do
      if let some decl := decl? then
        if decl.type.isAppOf ``OFE.Dist then try
            let newGoals ← goal.apply decl.toExpr
            newGoals.head!.assumption
            return some newGoals.tail!
          catch _ => continue
    return none

meta def tryUnfoldFn : TacticM Unit := do
  let _ ← observing? ((← getMainTarget).withApp <| λ _ args => do
    let fn := args[3]!.getAppFn.constName!
    -- don't unfold primitives
    if not <| (`Iris.BI.BIBase).isPrefixOf fn then
      evalTactic <| ← `(tactic|unfold $(mkIdent fn); try split))

meta def makeMainGoal (goal : MVarId) : TacticM Unit := do
  let goals ← getGoals
  let goals := goal :: goals.erase goal
  setGoals goals

meta partial def contractiveMain (goal : MVarId) (guarded : Bool) : TacticM Unit := do
  if ← goal.isAssigned then return
  makeMainGoal goal

  -- simplification step (includes application of Dist.rfl)
  if let some _ ← observing? (evalTactic <| ← `(tactic|simp)) then
    let _ ← (← getUnsolvedGoals).mapM (contractiveMain · guarded)
    return

  -- uses an OFE.Contractive instance
  if not guarded then if let some newGoals ← (distInstanceStep goal) then
    replaceMainGoal newGoals
    discard <| newGoals.mapM (contractiveMain · true)
    return

  -- applies an OFE.DistLater hypothesis
  if let some newGoals ← (distLaterStep goal) then
    replaceMainGoal newGoals
    discard <| newGoals.mapM (contractiveMain · guarded)
    return

  -- applies a non-expansive lemma
  if let some newGoals ← (nonexpStep goal) then
    replaceMainGoal newGoals
    discard <| newGoals.mapM (contractiveMain · guarded)
    return

elab "contractive" : tactic => do
  -- intro hypotheses
  evalTactic <| ← `(tactic|intros)

  -- intro foralls within OFE.Dist
  while ← distIsForall <| ← getMainTarget do
    evalTactic <| ← `(tactic|intro)

  -- unfold function definition
  tryUnfoldFn

  -- main loop
  contractiveMain (← getMainGoal) false

meta partial def nonexpMain (goal : MVarId) : TacticM Unit := do
  if ← goal.isAssigned then return
  makeMainGoal goal

  -- simplification step (includes application of Dist.rfl)
  if let some _ ← observing? (evalTactic <| ← `(tactic|simp)) then
    let _ ← (← getUnsolvedGoals).mapM (nonexpMain ·)
    return

  -- applies an OFE.Dist hypothesis
  if let some newGoals ← (distStep goal) then
    replaceMainGoal newGoals
    discard <| newGoals.mapM (nonexpMain ·)
    return

  -- applies a non-expansive lemma
  if let some newGoals ← (nonexpStep goal) then
    replaceMainGoal newGoals
    discard <| newGoals.mapM (nonexpMain ·)
    return

elab "nonexp" : tactic => do
  -- intro hypotheses
  evalTactic <| ← `(tactic|intros)

  -- intro foralls within OFE.Dist
  while ← distIsForall <| ← getMainTarget do
   evalTactic <| ← `(tactic|intro)

  -- unfold function definition
  tryUnfoldFn

  -- main loop
  nonexpMain (← getMainGoal)
