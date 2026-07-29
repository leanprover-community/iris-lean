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

meta def distLaterStep : TacticM Bool := do
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

meta def distStep : TacticM Bool := do
  let goal ← getMainGoal
  pure <| ← goal.withContext do
    let ctx ← getLCtx
    for decl? in ctx.decls do
      if let some decl := decl? then
        if decl.type.isAppOf ``OFE.Dist then
          let declIdent := mkIdent decl.userName
          let tac ← `(tactic|apply $declIdent:ident)
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

mutual

meta partial def contractiveRecurse (guarded : Bool) : TacticM Unit := do
  let _ ← (← getUnsolvedGoals).mapM (contractiveMain · guarded)

meta partial def contractiveMain (goal : MVarId) (guarded : Bool) : TacticM Unit := do
  if ← goal.isAssigned then return
  makeMainGoal goal

  -- simplification step (includes application of Dist.rfl)
  if let some _ ← observing? (evalTactic <| ← `(tactic|simp)) then contractiveRecurse guarded; return

  -- uses an OFE.Contractive instance
  if not guarded then if ← distInstanceStep then contractiveRecurse true; return

  -- applies an OFE.DistLater hypothesis
  if ← distLaterStep then contractiveRecurse guarded; return

  -- applies a non-expansive lemma
  if ← nonexpStep then contractiveRecurse guarded; return

end

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

mutual

meta partial def nonexpRecurse : TacticM Unit := do
  let _ ← (← getUnsolvedGoals).mapM (nonexpMain ·)

meta partial def nonexpMain (goal : MVarId) : TacticM Unit := do
  if ← goal.isAssigned then return
  makeMainGoal goal

  -- simplification step (includes application of Dist.rfl)
  if let some _ ← observing? (evalTactic <| ← `(tactic|simp)) then nonexpRecurse; return

  -- applies an OFE.Dist hypothesis
  if ← distStep then nonexpRecurse; return

  -- applies a non-expansive lemma
  if ← nonexpStep then nonexpRecurse; return

end

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
