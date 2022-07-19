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


private def rewriteConventional (rule : TSyntax ``rwRule) : TacticM Bool := do
  try
    evalTactic (← `(tactic| rewrite [$rule]))
    return true
  catch _ =>
    return false

private partial def rewriteTMR (direction : RewriteDirection) (rule : TSyntax `term) : TacticM Bool := do
  -- apply transitivity
  let some (goalL, goalR) ← applyTransitivity
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
  withFocus goal <| go rule
where
  applyTransitivity : TacticM <| Option <| MVarId × MVarId := do
    let tagL ← mkFreshUserName `l
    let tagR ← mkFreshUserName `r

    try
      withoutRecover <| evalTactic (← `(tactic|
        refine' transitivity ?$(mkIdent tagL) ?$(mkIdent tagR)
      ))
    catch _ =>
      return none

    return (← (tagL, tagR).mapAllM findGoalFromTag?).allSome?

  applyMonotonicity : TacticM <| Option <| Array MVarId := do
    -- try to apply binary monotonicity rules
    try
      let tagL ← mkFreshUserName `l
      let tagR ← mkFreshUserName `r

      withoutRecover <| evalTactic (← `(tactic|
        first
        | refine' monotonicity_binary                    ?$(mkIdent tagL) ?$(mkIdent tagR)
        | refine' monotonicity_left_contravariant_binary ?$(mkIdent tagL) ?$(mkIdent tagR)
      ))
      return (← #[tagL, tagR].mapM findGoalFromTag?).sequenceMap id
    catch _ =>
      pure ()

    -- try to apply unary monotonicity rules
    try
      let tag ← mkFreshUserName `g

      withoutRecover <| evalTactic (← `(tactic|
        first
        | refine' monotonicity_unary                     ?$(mkIdent tag)
        | refine' monotonicity_pointwise_unary (fun _ => ?$(mkIdent tag))
      ))
      return (← #[tag].mapM findGoalFromTag?).sequenceMap id
    catch _ =>
      pure ()

    -- no applicable monotonicity rule found
    return none

  applyReflexivity : TacticM Unit := do
    try
      withoutRecover <| evalTactic (← `(tactic|
        refine' reflexivity
      ))
    catch _ => pure ()

  go (rule : TSyntax `term) : TacticM Bool := do
    -- try to rewrite with the given rule
    try
      withoutRecover <| evalTactic (← `(tactic|
        exact $rule
      ))
      return true
    catch _ => pure ()

    -- try to apply any monotonicity rule
    let state ← saveState
    if let some goals ← applyMonotonicity then
      let mut rule? := some rule

      -- try to rewrite in one subterm
      for goal in goals do
        match rule? with
        | some rule =>
          if ← withFocus goal <| go rule then
            rule? := none
        | none =>
          withFocus goal <| applyReflexivity

      -- if the term is unchanged, restore the state to avoid unfolding definitions
      if rule?.isSome then
        state.restore
        applyReflexivity

      return rule?.isNone
    else
      -- do not rewrite in the term
      applyReflexivity
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
