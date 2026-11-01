/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.BI.Lib.Monotone
public meta import Iris.ProofMode

namespace Iris

open Lean Elab Tactic Meta

/-- Whether `fn` is a BI connective, which typeclass search handles directly. -/
meta def isPrimitiveConnective (fn : Name) : MetaM Bool := do
  return (`Iris.BI.BIBase).isPrefixOf fn || (← getProjectionFnInfo? fn).any (·.fromClass)

/-- Unfold the definition at the head of the body of `G` in a goal `MonoFn G` or `AntiFn G`. -/
elab "monotone_unfold" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some G := target.getAppArgs.back? | throwError "monotone: unexpected goal{indentExpr target}"
  let some fn ← lambdaTelescope G fun _ body => pure body.getAppFn.constName?
    | throwError "monotone: nothing to unfold"
  if ← isPrimitiveConnective fn then throwError "monotone: {fn} is a BI connective"
  evalTactic (← `(tactic| unfold $(mkIdent fn):ident))

/-- Prove `MonoFn G`, the monotonicity a fixpoint body needs, by typeclass search. Arguments are
introduced one at a time, `match`es on them are split, and definitions that the search cannot see
through are unfolded. -/
syntax "monotone" : tactic

macro_rules
  | `(tactic| monotone) => `(tactic| first
      | infer_instance
      | (refine MonoFn.of_forall fun _ => ?_; monotone)
      | (split <;> monotone)
      | (monotone_unfold; monotone))

end Iris
