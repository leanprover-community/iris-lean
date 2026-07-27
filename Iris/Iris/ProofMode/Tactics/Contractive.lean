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

elab "contractive" : tactic => do
  -- intro hypotheses
  evalTactic <| ← `(tactic|intros)

  -- intro foralls within OFE.Dist
  while ← distIsForall <| ← getMainTarget do
    evalTactic <| ← `(tactic|intro)

  -- unfold function definition, if possible
  let _ ← observing? ((← getMainTarget).withApp <| λ _ gArgs => do
    evalTactic <| ← `(tactic|unfold $(mkIdent gArgs[3]!.getAppFn.constName!); try split))

  -- main loop
  while ¬(← getUnsolvedGoals).isEmpty do
    -- simplification step (includes application of Dist.rfl)
    if let some _ ← observing? (evalTactic <| ← `(tactic|simp)) then continue

    -- uses an OFE.Contractive instance
    if ← distInstanceStep then continue

    -- applies an OFE.DistLater hypothesis
    if ← distHypStep then continue

    -- applies a non-expansive lemma
    if ← nonexpStep then continue

    -- exit if all fail
    break
