/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.Algebra.OFE
public meta import Iris.Algebra.NeCongrAttr

public meta section

namespace Iris.SolveNE
open Lean Meta Elab Tactic
open Iris.NeCongr

register_option iris.solveNE.maxSteps : Nat := {
  defValue := 100
  descr := "maximum number of recursion steps for the solve_ne/solve_contractive tactics"
}

initialize registerTraceClass `Iris.solveNE

/--
Context threaded through the `solve_ne` recursion.
-/
structure Ctx where
  /-- Prefer `Contractive` over `NonExpansive` congruence steps. Set by `solve_contractive`,
  for `Contractive` goals, and when a `DistLater` hypothesis is in scope. The tactic commits
  to the first congruence step that applies, so this determines which step is used for
  functions that are both contractive and non-expansive (such as `▷`). -/
  contractive : Bool
  /-- Distance facts derived during the search (e.g. hypotheses lowered to a smaller
  step-index below a contractive step) that are not part of the local context. -/
  extra : Array Expr := #[]

private def isDist (e : Expr) : Bool := e.isAppOfArity ``OFE.Dist 5
private def isDistLater (e : Expr) : Bool := e.isAppOfArity ``OFE.DistLater 5

/-- Candidate distance facts: `Dist`/`DistLater` local hypotheses plus the derived facts
from `ctx.extra`. Must be called with the goal's local context in scope. -/
private def candidates (ctx : Ctx) : MetaM (Array Expr) := do
  let mut cands := ctx.extra
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let ty ← whnfR decl.type
      if isDist ty || isDistLater ty then
        cands := cands.push decl.toExpr
  return cands

/-- Run `x`; on failure, roll the state back and return `none`. This is only used for
speculative *local* checks (unification, instance synthesis); once a congruence step has
been selected, the tactic commits to it and failures in its subgoals propagate. -/
private def attempt? (x : MetaM α) : MetaM (Option α) := do
  let s ← saveState
  try
    return some (← x)
  catch _ =>
    s.restore
    return none

/-- Try to close `g` (of type `tgt`) with the candidate proof `e`. -/
private def tryAssign (g : MVarId) (tgt : Expr) (e : Expr) : MetaM Bool := do
  if ← isDefEq (← inferType e) tgt then
    g.assign e
    return true
  return false

/--
Apply the congruence projection `lem` (`NonExpansive.ne`, `NonExpansive₂.ne`, or
`Contractive.distLater_dist`) to `g` with the function argument (at position `fIdx` of the
projection's telescope) instantiated to `pre`. The required `NonExpansive`/`Contractive`
instance and the `OFE` instances of the argument types are synthesized; the result-type `OFE`
instance is taken from the goal by unification. Returns the remaining distance hypotheses as
subgoals.

(This cannot use `mkAppOptM`/`MVarId.apply` directly: the `OFE` binders of class projections
are plain implicit, so neither would synthesize them, and `apply` alone cannot solve the
higher-order problem of finding the function argument.)
-/
private def applyCongrProj (g : MVarId) (lem : Name) (fIdx : Nat) (pre : Expr) :
    MetaM (List MVarId) := do
  let lemE ← mkConstWithFreshMVarLevels lem
  let (xs, _, concl) ← forallMetaTelescopeReducing (← inferType lemE)
  unless ← isDefEq xs[fIdx]! pre do
    throwError "cannot instantiate the function argument of {lem}"
  unless ← isDefEq concl (← g.getType) do
    throwError "conclusion of {lem} does not unify with the goal"
  let mut goals := []
  for x in xs do
    let m := x.mvarId!
    unless ← m.isAssigned do
      let xty ← instantiateMVars (← m.getType)
      if (← isClass? xty).isSome then
        let val ← synthInstance xty
        unless ← isDefEq x val do
          throwError "failed to assign instance argument of {lem}"
      else
        goals := goals.concat m
  g.assign (← instantiateMVars (mkAppN lemE xs))
  return goals

mutual

/-- Dispatch a subgoal produced by a congruence step: distance goals recurse, anything else
must be closed by assumption (e.g. side conditions of `@[ne_congr]` lemmas). -/
private partial def solveSub (ctx : Ctx) (fuel : Nat) (g : MVarId) : MetaM Unit := do
  if ← g.isAssigned then return
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  if isDist t then
    solveDist ctx fuel g
  else if isDistLater t then
    solveDistLater ctx fuel g
  else
    g.assumption

/-- Solve a distance goal `a ≡{n}≡ b`. -/
private partial def solveDist (ctx : Ctx) (fuel : Nat) (g : MVarId) : MetaM Unit := do
  let fuel + 1 := fuel
    | throwError "solve_ne: maximum number of steps reached, \
      consider increasing the option `iris.solveNE.maxSteps`"
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless isDist t do
    throwError "solve_ne: not a distance goal{indentExpr t}"
  trace[Iris.solveNE] "distance goal:{indentExpr t}"
  -- beta-reduce both sides (e.g. after destructuring `NonExpansive (fun x => _)`)
  let args := t.getAppArgs
  let a := args[3]!.headBeta
  let b := args[4]!.headBeta
  let mut g := g
  if a != args[3]! || b != args[4]! then
    g ← g.change (mkAppN t.getAppFn #[args[0]!, args[1]!, args[2]!, a, b])

  -- 1. reflexivity (also covers definitionally equal sides)
  if (← attempt? do
      let gs ← g.applyConst ``OFE.Dist.rfl
      unless gs.isEmpty do throwError "leftover goals").isSome then
    return

  -- 2. close the goal with a hypothesis (possibly symmetrized)
  let tgt ← g.getType
  for c in ← candidates ctx do
    if (← attempt? do
        if ← tryAssign g tgt c then return
        if ← tryAssign g tgt (← mkAppM ``OFE.Dist.symm #[c]) then return
        throwError "candidate does not apply").isSome then
      return

  -- 3. congruence lemmas registered via `@[ne_congr]`
  for lem in ← getNeCongrLemmas tgt do
    if let some gs ← attempt? (g.apply (← mkConstWithFreshMVarLevels lem)) then
      for g' in gs do
        let (_, g'') ← g'.intros
        solveSub ctx fuel g''
      return

  -- 4. spine congruence via `NonExpansive`/`NonExpansive₂`/`Contractive` instances
  let fa := a.getAppFn
  let as := a.getAppArgs
  let bs := b.getAppArgs
  if fa == b.getAppFn && as.size == bs.size then
    -- `(lemma, m)`: apply `lemma` to the application prefix that drops the last `m` arguments
    let splits : Array (Name × Nat) :=
      if ctx.contractive then
        #[(``OFE.Contractive.distLater_dist, 1), (``OFE.NonExpansive.ne, 1),
          (``OFE.NonExpansive₂.ne, 2)]
      else
        #[(``OFE.NonExpansive.ne, 1), (``OFE.NonExpansive₂.ne, 2),
          (``OFE.Contractive.distLater_dist, 1)]
    for (lem, m) in splits do
      if as.size < m then continue
      let gs? ← attempt? do
        let k := as.size - m
        for i in [0:k] do
          unless ← isDefEq as[i]! bs[i]! do
            throwError "application prefixes differ"
        let fIdx := if lem == ``OFE.NonExpansive₂.ne then 6 else 4
        applyCongrProj g lem fIdx (mkAppN fa (as.extract 0 k))
      if let some gs := gs? then
        for g' in gs do
          solveSub ctx fuel g'
        return

  -- 5. unfold the head of either side and retry (`unfoldProjInst?` reduces class
  -- projections applied to concrete instances, e.g. `FUpd.fupd` to `uPred_fupd`)
  let unfoldHead? (e : Expr) : MetaM (Option Expr) := do
    if let some e' ← unfoldProjInst? e then return some e'
    if e.getAppFn.isProj then
      if let some r ← withReducibleAndInstances <| reduceProj? e.getAppFn then
        return some (mkAppN r e.getAppArgs).headBeta
    unfoldDefinition? e
  let a? ← unfoldHead? a
  let b? ← unfoldHead? b
  if a?.isSome || b?.isSome then
    let t' := mkAppN t.getAppFn
      #[args[0]!, args[1]!, args[2]!, (a?.getD a).headBeta, (b?.getD b).headBeta]
    solveDist ctx fuel (← g.change t')
    return

  throwError "solve_ne: cannot solve{indentExpr tgt}\n\
    (for functions of arity ≥ 3 or binders, register a congruence lemma with `@[ne_congr]`)"

/-- Solve a goal `DistLater n a b`. -/
private partial def solveDistLater (ctx : Ctx) (fuel : Nat) (g : MVarId) : MetaM Unit := do
  let fuel + 1 := fuel
    | throwError "solve_ne: maximum number of steps reached, \
      consider increasing the option `iris.solveNE.maxSteps`"
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless isDistLater t do
    throwError "solve_ne: not a `DistLater` goal{indentExpr t}"

  -- 1. reflexivity
  if (← attempt? do
      let gs ← g.applyConst ``OFE.DistLater.rfl
      unless gs.isEmpty do throwError "leftover goals").isSome then
    return

  -- 2. close with a hypothesis: `DistLater` directly or `Dist` weakened by `Dist.distLater`
  let tgt ← g.getType
  let cands ← candidates ctx
  for c in cands do
    if (← attempt? do
        let ty ← whnfR (← inferType c)
        if isDistLater ty then
          if ← tryAssign g tgt c then return
          if ← tryAssign g tgt (← mkAppM ``OFE.DistLater.symm #[c]) then return
        else if isDist ty then
          if ← tryAssign g tgt (← mkAppM ``OFE.Dist.distLater #[c]) then return
          if ← tryAssign g tgt
              (← mkAppM ``OFE.Dist.distLater #[← mkAppM ``OFE.Dist.symm #[c]]) then return
        throwError "candidate does not apply").isSome then
      return

  -- 3. introduce the smaller step-index `m < n` and lower all candidates to `m`
  let [g₁] ← g.applyConst ``OFE.DistLater.intro
    | throwError "solve_ne: unexpected goals from DistLater.intro"
  let (fvars, g₂) ← g₁.introN 2
  g₂.withContext do
  let hm := Expr.fvar fvars[1]!
  let mut extra := #[]
  for c in cands do
    let ty ← whnfR (← inferType c)
    let lower? ←
      if isDist ty then
        attempt? (mkAppM ``OFE.Dist.lt #[c, hm])
      else if isDistLater ty then
        attempt? (mkAppM ``OFE.DistLater.dist_lt #[c, hm])
      else
        pure none
    if let some e := lower? then
      extra := extra.push e
  solveDist { ctx with extra } fuel g₂

end

/-- Entry point shared by `solve_ne` and `solve_contractive`. -/
def solveNEGoal (g : MVarId) (forceContractive : Bool) : MetaM Unit := do
  let fuel := iris.solveNE.maxSteps.get (← getOptions)
  let (_, g) ← g.intros
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let mk? : Option Name :=
    if t.isAppOf ``OFE.NonExpansive then some ``OFE.NonExpansive.mk
    else if t.isAppOf ``OFE.NonExpansive₂ then some ``OFE.NonExpansive₂.mk
    else if t.isAppOf ``OFE.Contractive then some ``OFE.Contractive.mk
    else none
  let contractive := forceContractive || t.isAppOf ``OFE.Contractive
  let g ← do
    if let some mk := mk? then
      let [g'] ← g.applyConst mk
        | throwError "solve_ne: failed to apply {mk}"
      let (_, g'') ← g'.intros
      pure g''
    else
      pure g
  g.withContext do
  let contractive ← do
    if contractive then
      pure true
    else
      (← candidates { contractive := false }).anyM fun c => do
        return isDistLater (← whnfR (← inferType c))
  solveSub { contractive } fuel g

/--
`solve_ne` proves goals of the form `NonExpansive f`, `NonExpansive₂ f`, `Contractive f`,
`a ≡{n}≡ b`, and `DistLater n a b` by congruence: it destructures the goal, then recursively
decomposes the resulting distance goal using `NonExpansive`/`NonExpansive₂`/`Contractive`
instances and congruence lemmas registered with `@[ne_congr]` (e.g. for binders), closing the
leaves by reflexivity or with distance hypotheses from the local context.

This is the iris-lean analogue of Rocq Iris's `solve_proper`. See also `solve_contractive`.
-/
elab "solve_ne" : tactic =>
  liftMetaTactic fun g => do solveNEGoal g false; return []

/--
Variant of `solve_ne` that prefers `Contractive` over `NonExpansive` congruence steps, for
goals such as `Contractive (fun P => ▷ P ∗ Q)`. The analogue of Rocq Iris's
`solve_contractive`. (`solve_ne` itself also prefers `Contractive` steps when the goal is
`Contractive f` or a `DistLater` hypothesis is in scope.)
-/
elab "solve_contractive" : tactic =>
  liftMetaTactic fun g => do solveNEGoal g true; return []

end Iris.SolveNE
