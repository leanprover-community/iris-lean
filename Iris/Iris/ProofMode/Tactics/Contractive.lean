/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.Algebra.OFE

namespace Iris

open Lean Elab Tactic Meta Iris.Std

meta def observingSuccess [Monad m] [MonadBacktrack s m] [MonadExcept ε m]
    (x : m α) : m Bool := do
  return (← observing? x).isSome

meta def nonexpLemmas : MetaM (Array Name) := do
  let env ← getEnv
  return (nonexpExt.getState env).reverse

meta def distIsForall (expr : Expr) : MetaM Bool := do
  expr.withApp <| λ _ distArgs =>
    distArgs[1]!.withApp <| λ ofeFn _ => do
      return ofeFn.getLambdaBody.getAppFn.isConstOf ``OFE.instForallOfOFEFun

meta def nonexpStep : TacticM Bool := do
  for neLem in ← nonexpLemmas do
    let tac ← `(tactic|apply $(mkIdent neLem):ident; try intros)
    if ← observingSuccess <| evalTactic tac then
      return true
  return false

meta def distInstanceStep : TacticM Bool := do
  let tac ← `(tactic|apply $(mkIdent ``OFE.Contractive.distLater_dist); intro _ _)
  return ← observingSuccess <| evalTactic tac

meta def distHypStep : TacticM Bool := do
  let goal ← getMainGoal
  pure <| ← goal.withContext do
    let ctx ← getLCtx
    for decl? in ctx.decls do
      if let some decl := decl? then
        if decl.type.isAppOf ``OFE.DistLater then
          let declIdent := mkIdent decl.userName
          let tac ← `(tactic|apply $declIdent:ident; assumption)
          if ← observingSuccess <| evalTactic tac then
            return true
    return false

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

meta partial def contractiveMain (goal : MVarId) (guarded : Bool := false) : TacticM Unit := do
  if ← goal.isAssigned then return
  makeMainGoal goal

  if let some _ ← observing? (evalTactic <| ← `(tactic|simp)) then
    let _ ← (← getUnsolvedGoals).mapM (contractiveMain · guarded)
    return

  if not guarded then if ← distInstanceStep then
    let _ ← (← getUnsolvedGoals).mapM (contractiveMain · true)
    return

  if ← distHypStep then
    let _ ← (← getUnsolvedGoals).mapM (contractiveMain · guarded)
    return

  if ← nonexpStep then
    let _ ← (← getUnsolvedGoals).mapM (contractiveMain · guarded)
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
  contractiveMain <| ← getMainGoal
