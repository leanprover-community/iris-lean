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
open Iris.NeCongr OFE

initialize registerTraceClass `Iris.solveNE

attribute [ne_congr] NonExpansive.ne NonExpansive₂.ne DistLater.rfl Dist.rfl NonExpansive.mk NonExpansive₂.mk Contractive.mk
attribute [ne_congr high] Contractive.distLater_dist

@[ne_congr]
theorem Dist.distLater_ne {α β} [OFE α] [OFE β] {f : α → β}
  [NonExpansive f] ⦃n : Nat⦄ ⦃x₁ x₂ : α⦄ : DistLater n x₁ x₂ → DistLater n (f x₁) (f x₂) := by sorry

@[ne_congr]
theorem Dist.distLater_ne2 {α β γ} [OFE α] [OFE β] [OFE γ] {f : α → β → γ}
  [NonExpansive₂ f] ⦃n : Nat⦄ ⦃x₁ x₂ : α⦄ ⦃y₁ y₂ : β⦄ :
  DistLater n x₁ x₂ → DistLater n y₁ y₂ → DistLater n (f x₁ y₁) (f x₂ y₂) := by sorry


private def isDist (e : Expr) : Bool := e.isAppOfArity ``OFE.Dist 5
private def isDistLater (e : Expr) : Bool := e.isAppOfArity ``OFE.DistLater 5

/-- Candidate distance facts: `Dist`/`DistLater` local hypotheses plus the derived facts
from `ctx.extra`. Must be called with the goal's local context in scope. -/
private def candidates : MetaM (Array Expr) := do
  let mut cands := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let ty ← whnfR decl.type
      if isDist ty || isDistLater ty then
        cands := cands.push decl.toExpr
  return cands

/-- Try to close `g` (of type `tgt`) with the candidate proof `e`. -/
private def tryAssign (g : MVarId) (tgt : Expr) (e : Expr) : MetaM Bool := do
  if ← isDefEq (← inferType e) tgt then
    g.assign e
    return true
  return false

mutual

/-- Solve a distance goal `a ≡{n}≡ b`. -/
private partial def step (g : MVarId) : MetaM (List MVarId) := do
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  trace[Iris.solveNE] "goal:{indentExpr t}"

  -- intro universal quantifiers
  if Meta.getIntrosSize t != 0 then
    let ⟨_, g'⟩ ← withTransparency .reducible <| g.intros
    return [g']

  -- close the goal with a hypothesis (possibly symmetrized)
  let tgt ← g.getType
  for c in ← candidates do
    if (← observing? do
        if ← tryAssign g tgt c then return
        if ← tryAssign g tgt (← mkAppM ``OFE.Dist.symm #[c]) then return
        throwError "candidate does not apply").isSome then
      return []

  -- congruence lemmas registered via `@[ne_congr]`
  for lem in ← getNeCongrLemmas tgt do
    trace[Iris.solveNE] "lem: {lem}"
    if let some gs ← observing? (withTransparency .reducible <| g.apply (← mkConstWithFreshMVarLevels lem)) then
      return gs

  throwError "solve_ne: cannot solve{indentExpr tgt}\n\
    (for functions of arity ≥ 3 or binders, register a congruence lemma with `@[ne_congr]`)"

end

/--
`solve_ne` proves goals of the form `NonExpansive f`, `NonExpansive₂ f`, `Contractive f`,
`a ≡{n}≡ b`, and `DistLater n a b` by congruence: it destructures the goal, then recursively
decomposes the resulting distance goal using `NonExpansive`/`NonExpansive₂`/`Contractive`
instances and congruence lemmas registered with `@[ne_congr]` (e.g. for binders), closing the
leaves by reflexivity or with distance hypotheses from the local context.

This is the iris-lean analogue of Rocq Iris's `solve_proper`. See also `solve_contractive`.
-/
elab "solve_ne_step" : tactic =>
  liftMetaTactic step

macro "solve_ne" : tactic => `(tactic| repeat1' solve_ne_step)

end Iris.SolveNE
