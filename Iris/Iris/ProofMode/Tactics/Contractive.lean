/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.Algebra.OFE
meta import Lean.Meta.Tactic.Split

namespace Iris

open Lean Elab Tactic Meta Term Iris.Std

meta def nonexpLemmas : MetaM (Array Name) := do
  let env ← getEnv
  return (nonexpExt.getState env).reverse

/-- Does `e` use the pointwise (`∀`) OFE instance? -/
meta def distIsForall (e : Expr) : MetaM Bool := do
  let some inst := e.getAppArgs[1]? | return false
  return inst.getAppFn.getLambdaBody.getAppFn.isConstOf ``OFE.instForallOfOFEFun

/-- Applying a hypothesis of a given type. -/
meta def applyHypStep (type : Name) (goal : MVarId) : TermElabM (Option (List MVarId)) :=
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

meta def distLaterStep (goal : MVarId) : TermElabM (Option (List MVarId)) :=
  applyHypStep ``OFE.DistLater goal

meta def distCarrier (h : Expr) : MetaM (Option Expr) := do
  return (← instantiateMVars (← inferType h)).getAppArgs[0]?

meta partial def distProjections (h : Expr) : MetaM (Array Expr) := do
  let some A ← distCarrier h | return #[h]
  if A.isAppOfArity ``Prod 2 then
    let hf ← mkAppM ``OFE.dist_fst #[h]
    let hs ← mkAppM ``OFE.dist_snd #[h]
    return #[h] ++ (← distProjections hf) ++ (← distProjections hs)
  else
    return #[h]

meta def distStep (goal : MVarId) : TermElabM (Option (List MVarId)) :=
  goal.withContext do
    for decl? in (← getLCtx).decls do
      if let some decl := decl? then
        if decl.type.isAppOf ``OFE.Dist then
          for cand in ← distProjections decl.toExpr do try
              match ← goal.apply cand with
              | [] => return some []
              | head :: tail =>
                head.assumption
                return some tail
            catch _ => continue
    return none

meta partial def discreteEqs (h : Expr) : MetaM (Array Expr) := do
  try
    return #[← mkAppM ``OFE.Discrete.discrete #[h]]
  catch _ =>
    let some A ← distCarrier h | return #[]
    if A.isAppOfArity ``Prod 2 then
      let hf ← mkAppM ``OFE.dist_fst #[h]
      let hs ← mkAppM ``OFE.dist_snd #[h]
      return (← discreteEqs hf) ++ (← discreteEqs hs)
    else
      return #[]

meta def discreteAlignStep (goal : MVarId) : TermElabM (Option (List MVarId)) :=
  goal.withContext do
    let mut eqs : Array Expr := #[]
    for decl? in (← getLCtx).decls do
      if let some decl := decl? then
        if decl.type.isAppOf ``OFE.Dist then
          eqs := eqs ++ (← discreteEqs decl.toExpr)
    if eqs.isEmpty then return none
    try
      let eqStxs ← eqs.mapM exprToSyntax
      let goals ← Elab.Tactic.run goal <| evalTactic <| ← `(tactic|simp only [$[$eqStxs:term],*])
      return some goals
    catch _ => return none

meta def splitMatchStep (goal : MVarId) : TermElabM (Option (List MVarId)) := do
  try
    let goals ← Elab.Tactic.run goal <| evalTactic <| ← `(tactic|split <;> try simp_all)
    return some goals
  catch _ => return none

meta def isPrimitive (fn : Name) : MetaM Bool := do
  return (`Iris.BI.BIBase).isPrefixOf fn || (← getProjectionFnInfo? fn).any (·.fromClass)

meta def unfoldHeadStep (goal : MVarId) : TermElabM (Option (List MVarId)) :=
  goal.withContext do
    let some fnArg := (← instantiateMVars (← goal.getType)).getAppArgs[3]? | return none
    let .const fn _ := fnArg.getAppFn | return none
    if ← isPrimitive fn then return none
    try
      let goals ← Elab.Tactic.run goal <| evalTactic <| ← `(tactic|unfold $(mkIdent fn))
      return some goals
    catch _ => return none

meta def distInstanceStep (goal : MVarId) : TermElabM (Option (List MVarId)) := do try
    match ← goal.applyConst ``OFE.Contractive.distLater_dist with
    | [] => return some []
    | head :: tail =>
      let (_, head) ← head.introN 2
      return some (head :: tail)
  catch _ => return none

meta def nonexpStep (goal : MVarId) : TermElabM (Option (List MVarId)) := do
  for neLem in ← nonexpLemmas do try
      let goals ← Elab.Tactic.run goal <| evalTactic <| ← `(tactic|apply $(mkIdent neLem))
      match goals with
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
    (step : MVarId → TermElabM (Option (List MVarId))) (goal : MVarId) : TacticM Bool := do
  match ← step goal with
  | some newGoals =>
    replaceMainGoal newGoals
    discard <| newGoals.mapM recurse
    return true
  | none => return false

meta def simpThenRecurse (k : MVarId → TacticM Unit) : TacticM Bool := do
  if let some _ ← observing? (evalTactic <| ← `(tactic|simp [Function.uncurry, Function.curry])) then
    if let some newGoal ← observing? getMainGoal then
      k newGoal
    return true
  return false

meta partial def contractiveMain (goal : MVarId) (guarded : Bool) : TacticM Unit := do
  if ← goal.isAssigned then return
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
  makeMainGoal goal

  -- simplification step (includes application of Dist.rfl)
  if ← simpThenRecurse nonexpMain then return

  -- deal with uncurried functions
  if ← tryStep nonexpMain discreteAlignStep goal then return

  -- split goal by cases
  if ← tryStep nonexpMain splitMatchStep goal then return

  -- applies an OFE.Dist hypothesis
  if ← tryStep nonexpMain distStep goal then return

  -- applies a non-expansive lemma
  if ← tryStep nonexpMain nonexpStep goal then return

  -- unfolds further if needed
  if ← tryStep nonexpMain unfoldHeadStep goal then return

  throwError "tactic 'nonexp' failed"

meta def contractiveSetup : TacticM Unit := do
  evalTactic <| ← `(tactic|intros)

  while ← distIsForall <| ← getMainTarget do
    evalTactic <| ← `(tactic|intro)

  tryUnfoldFn

meta def isNonExpansiveGoal : TacticM Bool := do
  let target ← getMainTarget
  return target.isAppOf ``OFE.NonExpansive || target.isAppOf ``OFE.NonExpansive₂

meta def nonexpSetup : TacticM Unit := do
  evalTactic <| ← `(tactic|intros)

  while ← isNonExpansiveGoal do
    evalTactic <| ← `(tactic|constructor)
    evalTactic <| ← `(tactic|intros)

  while ← distIsForall <| ← getMainTarget do
    evalTactic <| ← `(tactic|intro)

  tryUnfoldFn

elab "contractive" : tactic => do
  contractiveSetup
  contractiveMain (← getMainGoal) false

elab "nonexp" : tactic => do
  nonexpSetup
  nonexpMain (← getMainGoal)

end Iris
