/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Iris.BI.Lib.Monotone
public meta import Iris.ProofMode
public meta import Lean.Meta.Sym
public meta import Lean.LabelAttribute

namespace Iris

open Lean Elab Tactic Meta BI

open Sym in
/-- Decompose `goal` by `rules`, introducing quantifiers; returns the goals no rule applies to. -/
meta partial def decompose (rules : List BackwardRule) (goal : MVarId) : SymM (List MVarId) := do
  for rule in rules do
    if let .goals goals ← rule.apply goal then
      let goals' ← goals.mapM fun goal => do
        let .goal _ goal ← intros goal | decompose rules goal
        decompose rules goal
      return goals'.flatten
  return [goal]

/-- Solve an `IMonoPred R P P'` goal: decompose by the `@[imono]` rules, split `match` and `if`,
unfold other definitions (a recursive one only once per branch), and close the rest with `R`. -/
meta partial def imonoGoal (rules : List Sym.BackwardRule) (goal : MVarId)
    (unfolded : NameSet := {}) : TacticM Unit := do
  -- The rules match syntactically and Sym needs `let`-free terms: unfold reducible definitions
  -- (`name.pre`), beta-reduce, and inline `let`s first.
  let target ← Sym.unfoldReducible (← instantiateMVars (← goal.getType))
  let target ← Core.transform target (pre := fun
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | e => return .continue e)
  let goal ← goal.replaceTargetDefEq (← Core.betaReduce target)
  let goals ← Sym.SymM.run do decompose rules (← Sym.preprocessMVar goal)
  for goal in goals do
    setGoals [goal]
    let_expr IMonoPred _ _ _ P _ := ← instantiateMVars (← goal.getType)
      | throwError "imono: unexpected goal{indentD goal}"
    let .const fn _ := P.cleanupAnnotations.getAppFn
      | evalTactic (← `(tactic| first
          | ((repeat (apply IMonoPred.spec)); exact IMonoPred.call)
          | fail "imono: not monotone, or not covered by an @[imono] rule"))
    if (← getProjectionFnInfo? fn).isSome then throwError "imono: no rule for {fn}"
    if unfolded.contains fn then throwError "imono: no rule for {fn}, after unfolding it once"
    if (← isMatcher fn) || fn == ``ite || fn == ``dite then
      evalTactic (← `(tactic| split))
      for goal in ← getGoals do imonoGoal rules goal unfolded
    else
      try evalTactic (← `(tactic| unfold $(mkIdent fn):ident))
      catch _ => throwError "imono: no rule for {fn}"
      for goal in ← getGoals do
        let recursive := ((← instantiateMVars (← goal.getType)).find? (·.isConstOf fn)).isSome
        imonoGoal rules goal (if recursive then unfolded.insert fn else unfolded)
  setGoals []

/-- Prove `BIMono F`, or its unfolding `∀ Φ Ψ, ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x`
with any number of arguments `x`. -/
elab "imono" : tactic => do
  try
    evalTactic (← `(tactic| (
      try unfold BIMono
      intro Φ Ψ
      repeat (apply IMonoPred.arg; intro)
      change IMonoPred _ _ _)))
  catch _ => throwError "imono: expected a monotonicity goal, `BIMono F` or \
    `∀ Φ Ψ, ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x`"
  let rules ← (``IMonoPred.refl :: (← labelled `imono).toList).mapM (Sym.mkBackwardRuleFromDecl ·)
  imonoGoal rules (← getMainGoal)

end Iris
