import Iris.Std.Classes
import Iris.Std.Prod
import Iris.Std.Tactic

import Lean.Elab.Tactic

namespace Iris.Std
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta Lean.Parser.Tactic

syntax rwRule' := "!"? rwRule

inductive RewriteModifier
  | single
  | all

private def parseRewriteRule' (rule : TSyntax ``rwRule') : TacticM <| RewriteModifier × TSyntax ``rwRule := do
  match rule with
  | `(rwRule'| !$rule)       => pure (.all, rule)
  | `(rwRule'| $rule:rwRule) => pure (.single, rule)
  | _ => throwUnsupportedSyntax

inductive RewriteDirection
  | forward
  | reverse

private def parseRewriteRule (rule : TSyntax ``rwRule) : TacticM <| RewriteDirection × TSyntax `term := do
  match rule with
  | `(rwRule| ← $rule)    => pure (.reverse, rule)
  | `(rwRule| $rule:term) => pure (.forward, rule)
  | _ => throwUnsupportedSyntax


private def normalizeGoal (goal : MVarId) : TacticM MVarId := do
  if (← getMVarType goal).isForall then
    let (_, goal) ← intro goal `_
    return goal
  else
    return goal

-- TODO use attribute instead
private def getMonotonicityRules : TacticM <| Array Name := do
  return #[
    `Iris.BI.and_mono,
    `Iris.BI.or_mono,
    `Iris.BI.impl_mono,
    `Iris.BI.forall_mono,
    `Iris.BI.exist_mono,
    `Iris.BI.BI.sep_mono,
    `Iris.BI.wand_mono,
    `Iris.BI.affinely_mono,
    `Iris.BI.affinely_if_mono,
    `Iris.BI.absorbingly_mono,
    `Iris.BI.absorbingly_if_mono,
    `Iris.BI.BI.persistently_mono,
    `Iris.BI.persistently_if_mono,
    `Iris.BI.intuitionistically_mono,
    `Iris.BI.intuitionistically_if_mono
  ]


private def rewriteConventional (rule : TSyntax ``rwRule) : TacticM Bool := do
  try
    evalTactic (← `(tactic| rewrite [$rule]))
    return true
  catch _ =>
    return false

private partial def rewriteTMR (direction : RewriteDirection) (rule : TSyntax `term) : TacticM Bool := do
  let goal ← getMainGoal

  -- apply transitivity
  let some (goalL, goalR) ← applyTransitivity goal
    | return false

  -- select the correct goal based on the rewrite direction
  let goal ← match direction with
    | .forward => do
      setMVarTag goalR .anonymous
      pure goalL
    | .reverse => do
      setMVarTag goalL .anonymous
      pure goalR

  -- try to rewrite with the given rule
  go goal rule
where
  applyTransitivity (goal : MVarId) : TacticM <| Option <| MVarId × MVarId := do
    try
      let some <| goalL :: goalR :: [] ← apply' goal ``transitivity
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
      discard <| apply' goal ``reflexivity
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

  -- try to close the goal using reflexivity
  withoutRecover <| evalTactic (← `(tactic|
    try first
    | rfl
    | exact reflexivity
  ))

end Iris.Std
