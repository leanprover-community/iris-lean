/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.Std.Classes
import Iris.Std.Tactic

import Lean.Elab.Tactic

namespace Iris.Std
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta Lean.Parser.Tactic

/- This file implements a rewriting tactic for preorders with monotone rules on how to
destruct operators. -/

/-- Rewrite rules for `rw'` have the same structure as for `rw`, except they allow an additional
`!` prefix to indicate that a rewrite rule should be used as often as possible. -/
syntax rwRule' := "!"? rwRule

/-- Modifier for a rewrite rule to indicate how often is should be used. -/
inductive RewriteModifier
  | single
  | all

/-- Parse a `rwRule'` syntax object and return its `RewriteModifier` together with the contained
`rwRule` syntax object. -/
private def parseRewriteRule' (rule : TSyntax ``rwRule') : TacticM <| RewriteModifier × TSyntax ``rwRule := do
  match rule with
  | `(rwRule'| !$rule)       => pure (.all, rule)
  | `(rwRule'| $rule:rwRule) => pure (.single, rule)
  | _ => throwUnsupportedSyntax

/-- Rewrite direction of a `rwRule`. -/
inductive RewriteDirection
  | forward
  | reverse

/-- Parse a `rwRule` and return its `RewriteDirection` together with the contained `term`
syntax object. -/
private def parseRewriteRule (rule : TSyntax ``rwRule) : TacticM <| RewriteDirection × TSyntax `term := do
  match rule with
  | `(rwRule| ← $rule)    => pure (.reverse, rule)
  | `(rwRule| $rule:term) => pure (.forward, rule)
  | _ => throwUnsupportedSyntax


/-- Register an environment extension to hold all operator destruction rules. -/
initialize monoRulesExt : SimplePersistentEnvExtension Name NameSet ← registerSimplePersistentEnvExtension {
  name := `rwMonoRules,
  addEntryFn := NameSet.insert,
  addImportedFn := fun es => mkStateFromImportedEntries NameSet.insert {} es
}

/-- Return all operator destruction rules from the environment extension `rwMonoRules`. -/
private def getMonotonicityRules : TacticM <| Array Name := do
  return monoRulesExt.getState (← getEnv) |>.toArray

/-- Register the attribute `rw_mono_rule` for adding theorems to the environment
extension `rwMonoRules`. -/
initialize registerBuiltinAttribute {
  name := `rw_mono_rule,
  descr := "monotonicity rule used to destruct terms during rewriting",
  add := fun name _ kind => do
    if !kind matches .global then
      throwError "only global definitions are allowed as monotonicity rules"
    setEnv <| monoRulesExt.addEntry (← getEnv) name
}


/-- Normalize a goal by, e.g., introducing all universally-bound variables. -/
private def normalizeGoal (goal : MVarId) : TacticM MVarId := do
  if (← goal.getType).isForall then
    let (_, goal) ← goal.intro `_
    return goal
  else
    return goal


/-- Rewrite the rule `rule` with the tactic `rewrite` and return whether the operation
was successful. -/
private def rewriteConventional (rule : TSyntax ``rwRule) : TacticM Bool := do
  try
    evalTactic (← `(tactic| rewrite [$rule]))
    return true
  catch _ =>
    return false

/-- Rewrite the rule `rule` in the rewrite direction `direction` using the trans and
refl of the preorder in the goal and `rule`, as well as the monotonicity of the registered
operator destruction rules. -/
private partial def rewriteTMR (direction : RewriteDirection) (rule : TSyntax `term) : TacticM Bool := do
  let goal ← getMainGoal
  let tag ← goal.getTag

  -- apply trans
  let some (goalL, goalR) ← applyTransitivity goal
    | return false

  -- select the correct goal based on the rewrite direction
  let goal ← match direction with
    | .forward => do
      goalR.setTag tag
      pure goalL
    | .reverse => do
      goalL.setTag tag
      pure goalR

  -- try to rewrite with the given rule
  go goal rule
where
  applyTransitivity (goal : MVarId) : TacticM <| Option <| MVarId × MVarId := do
    try
      let some <| goalL :: goalR :: [] ← apply' goal ``trans
        | return none
      return some (goalL, goalR)
    catch _ =>
      return none

  applyMonotonicity (goal : MVarId) : TacticM <| Option <| List MVarId := do
    for rule in (← getMonotonicityRules) do
      try
        if let some goals ← apply' goal rule then
          return ← goals.mapM normalizeGoal
      catch _ =>
        continue
    return none

  applyReflexivity (goal : MVarId) : TacticM Unit := do
    try
      discard <| apply' goal ``refl
    catch _ => pure ()

  go (goal : MVarId) (rule : TSyntax `term) : TacticM Bool := do
    -- try to rewrite with the given rule
    try
      withFocus goal <| withoutRecover <| evalTactic (← `(tactic|
        exact $rule
      ))
      return true
    catch _ => pure ()

    -- try to apply any monotonicity rule
    let state ← saveState
    if let some goals ← applyMonotonicity goal then
      let mut rule? := some rule

      -- try to rewrite in exactly one subterm
      for goal in goals do
        match rule? with
        | some rule =>
          if ← go goal rule then
            rule? := none
        | none =>
          applyReflexivity goal

      -- if the term is unchanged, restore the state to reduce the proof term size
      if rule?.isSome then
        state.restore
        applyReflexivity goal

      return rule?.isNone
    else
      -- do not rewrite in the term
      applyReflexivity goal
      return false


elab "rw' " "[" rules:rwRule',*,? "]" : tactic => do
  -- rewrite the rules in order
  for rule' in rules.getElems do
    let (modifier , rule) ← parseRewriteRule' rule'
    let (direction, term) ← parseRewriteRule  rule

    match modifier with
    -- universal rules should be applied as often as possible
    | .all =>
      while ← rewriteConventional rule  do pure ()
      while ← rewriteTMR direction term do pure ()
    -- singular rules are applied exactly once
    | .single =>
      if      ← rewriteConventional rule  then continue
      else if ← rewriteTMR direction term then continue
      else throwError s!"could not rewrite `{rule'.raw.prettyPrint}`"

  -- try to close the goal using refl
  withoutRecover <| evalTactic (← `(tactic|
    try first
    | rfl
    | exact refl
  ))

end Iris.Std
