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
/-- Recursively decompose `P` according to a list of BackwardRules, introducing quantifiers at each
step. Returns the list of goals that decompose no further. -/
meta partial def decompose (rules : List BackwardRule) (goal : MVarId) : SymM (List MVarId) := do
  for rule in rules do
    if let .goals goals ← rule.apply goal then
      let goals' ← goals.mapM fun goal => do
        -- Recursively introduce quantifiers and decompose
        let .goal _ goal ← intros goal | decompose rules goal
        decompose rules goal
      return goals'.flatten
  return [goal]

/-- Tactic for solving the `IMonoPred` obligations introduced by fixpoints.
Decomposes the goal according to the `@[imono]` rules, splits match statements, and tries to apply
the assumpton `R`. -/
meta partial def imonoGoal (rules : List Sym.BackwardRule) (goal : MVarId) : TacticM Unit := do
  -- The rules match syntactically, and Sym needs `let`-free terms: unfold reducible definitions
  -- such as `name.pre`, and reduce `(fun Φ x => …) Φ x` and `let next := Φ; next x`, first.
  let target ← Core.betaReduce (← Sym.unfoldReducible (← instantiateMVars (← goal.getType)))
  let target ← Core.transform target (pre := fun
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | e => return .continue e)
  let goal ← goal.replaceTargetDefEq (← Core.betaReduce target)
  let goals ← Sym.SymM.run do decompose rules (← Sym.preprocessMVar goal)
  -- The main loop
  for goal in goals do
    setGoals [goal]
    let_expr IMonoPred _ _ _ P _ := ← instantiateMVars (← goal.getType)
      | throwError "imono: unexpected goal{goal}"
    let .const fn _ := P.cleanupAnnotations.getAppFn
      | evalTactic (← `(tactic| first
          | ((repeat (apply IMonoPred.spec)); exact IMonoPred.call)
          | fail "imono: not monotone, or not covered by an @[imono] rule"))
    if (← getProjectionFnInfo? fn).isSome then throwError "imono: no rule for {fn}"
    let step ← if ← isMatcher fn then `(tactic| split) else `(tactic| unfold $(mkIdent fn):ident)
    evalTactic step
    for goal in ← getGoals do imonoGoal rules goal
  setGoals []

/-- Prove that a fixpoint body `F` is monotone, stated as `BIMono F` or with its arguments spelled
out: `∀ Φ Ψ, ⊢ □ (∀ x y, Φ x y -∗ Ψ x y) -∗ ∀ x y, F Φ x y -∗ F Ψ x y`. -/
elab "imono" : tactic => do
  evalTactic (← `(tactic| (
    try unfold BIMono
    intro Φ Ψ
    repeat (apply IMonoPred.arg; intro)
    change IMonoPred _ _ _)))
  let rules ← (``IMonoPred.refl :: (← labelled `imono).toList).mapM (Sym.mkBackwardRuleFromDecl ·)
  imonoGoal rules (← getMainGoal)

end Iris
