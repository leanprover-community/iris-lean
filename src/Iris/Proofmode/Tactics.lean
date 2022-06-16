import Iris.BI
import Iris.Proofmode.Environments
import Iris.Proofmode.Expr
import Iris.Proofmode.Theorems
import Iris.Std

import Lean.Elab

namespace Iris.Proofmode
open Iris.BI
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

namespace Internal
end Internal
open Internal

elab "istart_proof" : tactic => do
  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← (← getMVarType goal) |> instantiateMVars

  -- check if already in proof mode
  if isEnvsEntails expr then
    return ()

  -- create environment
  try evalTactic (← `(tactic|
    refine (as_emp_valid_2 _ ?_) ;
    refine (tac_start _ ?_)
  ))
  catch _ => throwError "unable to start proof mode"

elab "istop_proof" : tactic => do
  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← (← getMVarType goal) |> instantiateMVars

  -- check if already in proof mode
  if !isEnvsEntails expr then
    throwError "not in proof mode"

  -- reduce proof mode definitions
  try evalTactic (← `(tactic|
    simp only [envs_entails, of_envs] ;
    simp only [bigOp, List.foldr1]
  ))
  catch _ => throwError "unable to stop proof mode"


private def extractEnvsEntailsFromGoal (startProofMode : Bool := false) : TacticM <| Expr × Expr × Expr := do
  if startProofMode then
    evalTactic (← `(tactic|
      istart_proof
    ))

  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← (← getMVarType goal) |> instantiateMVars

  let some envsEntails := extractEnvsEntails? expr
    | throwError "not in proof mode"

  return envsEntails

private def findHypothesis (name : Name) : TacticM HypothesisIndex := do
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal
  if let some i ← Γₚ.asListExpr_findIndex? (·.getMDataName?.isEqSome name) then
    let some l ← Γₚ.asListExpr_length?
      | throwError "ill-formed proof environment"
    return ⟨.intuitionistic, i, l⟩
  else if let some i ← Γₛ.asListExpr_findIndex? (·.getMDataName?.isEqSome name) then
    let some l ← Γₛ.asListExpr_length?
      | throwError "ill-formed proof environment"
    return ⟨.spatial, i, l⟩
  else
    throwError "unknown hypothesis"


def Internal.irenameCore (hypIndex : HypothesisIndex) (name : Name) : TacticM Unit := do
  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← (← getMVarType goal) |> instantiateMVars

  let some (Γₚ, Γₛ, _) := extractEnvsEntails? expr
    | throwError "not in proof mode"

  let modifyHypothesis (Γ : Expr) (idx : Nat) : TacticM Expr := do
    -- find hypothesis
    let some h ← Γ.asListExpr_get? idx
      | throwError "invalid index or ill-formed proof environment"

    -- check for unique (or equal) hypothesis name
    let nameFrom? := h.getMDataName?
    if nameFrom? |>.map (· != name) |>.getD true then
      if ← [Γₚ, Γₛ].anyM (fun Γ => do return (← Γ.asListExpr_any? (·.getMDataName?.isEqSome name)) matches some true) then
        throwError "name is already used for another hypothesis"

    -- rename hypothesis
    let h := h.setMDataName? name

    -- re-insert hypothesis
    let some Γ ← Γ.asListExpr_set? h idx
      | throwError "invalid index or ill-formed proof environment"

    return Γ

  -- modify environment
  let (Γₚ, Γₛ) ← match hypIndex with
    | ⟨.intuitionistic, index, _⟩ => do
      pure (← modifyHypothesis Γₚ index, Γₛ)
    | ⟨.spatial, index, _⟩ => do
      pure (Γₚ, ← modifyHypothesis Γₛ index)

  -- update goal
  let some expr := modifyEnvsEntails? expr Γₚ Γₛ none
    | throwError "ill-formed proof environment"

  setMVarType goal expr

elab "irename " colGt nameFrom:ident " into " colGt nameTo:ident : tactic => do
  -- parse syntax
  if nameFrom.getId.isAnonymous then
    throwUnsupportedSyntax
  let nameTo := nameTo.getId
  if nameTo.isAnonymous then
    throwUnsupportedSyntax

  -- find and rename hypothesis
  irenameCore (← findHypothesis nameFrom.getId) nameTo


elab "iclear" colGt name:ident : tactic => do
  -- parse syntax
  let name := name.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let hypIndex ← findHypothesis name

  -- clear hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_clear $(← hypIndex.quoteAsEnvsIndex) _ ?_
    | fail
  ))
  catch _ => throwError "failed to clear the hypothesis"


elab "iintro " colGt name:ident : tactic => do
  -- parse syntax
  let name := name.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- extract environment
  let (_, Γₛ, _) ← extractEnvsEntailsFromGoal true

  -- determine hypothesis list length
  let some lₛ ← Γₛ.asListExpr_length?
    | throwError "ill-formed proof environment"

  -- introduce hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_impl_intro _ ?_
    | refine tac_wand_intro _ ?_
    | fail
  ))
  catch _ => throwError "failed to introduce hypothesis"

  -- name hypothesis
  irenameCore ⟨.spatial, lₛ, lₛ + 1⟩ name

elab "iintro " colGt "#" colGt name:ident : tactic => do
  -- parse syntax
  let name := name.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- extract environment
  let (Γₚ, _, _) ← extractEnvsEntailsFromGoal true

  -- determine hypothesis list length
  let some lₚ ← Γₚ.asListExpr_length?
    | throwError "ill-formed proof environment"

  -- introduce hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_impl_intro_intuitionistic _ ?_
    | refine tac_wand_intro_intuitionistic _ ?_
    | fail
  ))
  catch _ => throwError "failed to introduce hypothesis"

  -- name hypothesis
  irenameCore ⟨.intuitionistic, lₚ, lₚ + 1⟩ name


elab "iexact " colGt name:ident : tactic => do
  -- parse syntax
  let name := name.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let hypIndex ← findHypothesis name

  -- try to solve the goal with the found hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_assumption $(← hypIndex.quoteAsEnvsIndex) _
    | fail
  ))
  catch _ => throwError "failed to use the hypothesis to close the goal"

elab "iassumption_lean" : tactic => do
  -- try all hypotheses from the local context
  let hs ← getLCtx
  for h in ← getLCtx do
    -- match on `⊢ Q`
    let some (P, _) := extractEntails? h.type
      | continue
    if !isEmp P then
      continue

    -- try to solve the goal
    try
      evalTactic (← `(tactic|
        refine tac_assumption_lean _ $(mkIdent h.userName)
      ))
      return
    catch _ => continue

  throwError "no matching hypothesis found or remaining environment cannot be cleared"

elab "iassumption" : tactic => do
  -- extract environment
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal

  let (some lₚ, some lₛ) ← (Γₚ, Γₛ).mapAllM (M := MetaM) Lean.Expr.asListExpr_length?
    | throwError "ill-formed proof environment"

  -- try to close the goal
  let tryCloseGoal (envsIndex : Syntax) : TacticM Bool := do
    try
      evalTactic (← `(tactic|
        first
        | refine tac_assumption $envsIndex _
        | refine tac_false_destruct $envsIndex _ (by rfl)
        | fail
      ))
      pure true
    catch _ => pure false

  -- try all available hypotheses
  for i in List.range lₚ do
    let hypIndex : HypothesisIndex := ⟨.intuitionistic, i, lₚ⟩
    if ← tryCloseGoal (← hypIndex.quoteAsEnvsIndex) then
      return ()

  for i in List.range lₛ do
    let hypIndex : HypothesisIndex := ⟨.spatial, i, lₛ⟩
    if ← tryCloseGoal (← hypIndex.quoteAsEnvsIndex) then
      return ()

  -- try all hypotheses from the Lean context
  try evalTactic (← `(tactic|
    first
    | iassumption_lean
    | fail
  ))
  catch _ => throwError "no matching hypothesis found or remaining environment cannot be cleared"


elab "isplit" : tactic => do
  -- start proof mode if not already
  evalTactic (← `(tactic|
    istart_proof
  ))

  -- split conjunction
  try evalTactic (← `(tactic|
    first
    | refine tac_and_split _ ?And.left ?And.right
    | fail
  ))
  catch _ => throwError "unable to split conjunction"

elab "isplit" side:(&"l" <|> &"r") "[" names:ident,* "]" : tactic => do
  -- parse syntax
  let splitRight ← match side.getKind with
    | `l => pure false
    | `r => pure true
    | _  => throwUnsupportedSyntax
  let names ← names.getElems.mapM (fun name => do
    let name := name.getId
    if name.isAnonymous then
      throwUnsupportedSyntax
    pure name
  )

  -- extract environment
  let (_, Γₛ, _) ← extractEnvsEntailsFromGoal true

  -- find indices
  let indices ← names.mapM (fun name => do
    let some index ← Γₛ.asListExpr_findIndex? (·.getMDataName?.isEqSome name)
      | throwError "unknown spatial hypothesis"
    pure index
  )

  -- split conjunction
  try evalTactic (← `(tactic|
    first
    | refine tac_sep_split $(quote indices.toList) $(quote splitRight) _ ?Sep.left ?Sep.right
      <;> simp only [List.partitionIndices, List.partitionIndices.go, Prod.map, ite_true, ite_false]
    | fail
  ))
  catch _ => throwError "unable to split separating conjunction"

macro "isplit" &"l" : tactic => `(tactic| isplit r [])
macro "isplit" &"r" : tactic => `(tactic| isplit l [])

end Iris.Proofmode
