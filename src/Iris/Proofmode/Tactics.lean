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

elab "iStartProof" : tactic => do
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

elab "iStopProof" : tactic => do
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


private def extractEnvsEntailsFromGoal? (startProofMode : Bool := false) : TacticM <| Expr × Expr × Expr := do
  if startProofMode then
    evalTactic (← `(tactic|
      iStartProof
    ))

  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← (← getMVarType goal) |> instantiateMVars

  let some envsEntails := extractEnvsEntails? expr
    | throwError "not in proof mode"

  return envsEntails

private def findHypothesis? (name : Name) (Γₚ Γₛ : Expr) : TacticM <| HypothesisType × Nat := do
  if let some i ← Γₚ.asListExpr_findIndex? (·.getMDataName?.isEqSome name) then
    return (.intuitionistic, i)
  else if let some i ← Γₛ.asListExpr_findIndex? (·.getMDataName?.isEqSome name) then
    return (.spatial, i)
  else
    throwError "unknown hypothesis"


namespace Internal

scoped elab "iRename " categ:(&"p" <|> &"s") idx:num colGt name:ident : tactic => do
  -- parse syntax
  let categ ← match categ.getKind with
    | `p => pure HypothesisType.intuitionistic
    | `s => pure HypothesisType.spatial
    | _  => throwUnsupportedSyntax
  let some idx := idx.isNatLit?
    | throwUnsupportedSyntax
  let name := name.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← (← getMVarType goal) |> instantiateMVars

  let some (Γₚ, Γₛ, _) := extractEnvsEntails? expr
    | throwError "not in proof mode"

  -- check for unique hypothesis name
  if ← [Γₚ, Γₛ].anyM (fun Γ => do return (← Γ.asListExpr_any? (·.getMDataName?.isEqSome name)) matches some true) then
    throwError "name is already used for another hypothesis"

  -- find hypothesis
  let Γ := match categ with
    | .intuitionistic => Γₚ
    | .spatial        => Γₛ
  let some h ← Γ.asListExpr_get? idx
    | throwError "invalid index or ill-formed proof environment"

  -- rename
  let h := h.setMDataName? name

  -- insert modified hypothesis
  let some Γ ← Γ.asListExpr_set? h idx
    | throwError "invalid index or ill-formed proof environment"
  let Γₚ := if categ matches .intuitionistic then Γ else Γₚ
  let Γₛ := if categ matches .spatial        then Γ else Γₛ

  -- update goal
  let some expr := modifyEnvsEntails? expr Γₚ Γₛ none
    | throwError "ill-formed proof environment"

  setMVarType goal expr

end Internal

elab "iRename " colGt nameFrom:ident " into " colGt nameTo:ident : tactic => do
  -- parse syntax
  if nameFrom.getId.isAnonymous then
    throwUnsupportedSyntax
  if nameTo.getId.isAnonymous then
    throwUnsupportedSyntax

  -- extract environment
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal? true

  -- find hypothesis index and rename hypothesis
  match ← findHypothesis? nameFrom.getId Γₚ Γₛ with
    | (.intuitionistic, i) => evalTactic (← `(tactic| iRename p $(quote i) $nameTo))
    | (.spatial, i)        => evalTactic (← `(tactic| iRename s $(quote i) $nameTo))


elab "iClear" colGt name:ident : tactic => do
  -- parse syntax
  let name := name.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- extract environment
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal? true

  let (some lₚ, some lₛ) ← (Γₚ, Γₛ).mapAllM (M := MetaM) Lean.Expr.asListExpr_length?
    | throwError "ill-formed proof environment"

  -- find hypothesis index
  let envsIndex ← match ← findHypothesis? name Γₚ Γₛ with
    | (.intuitionistic, i) => `(EnvsIndex.p ⟨$(quote i), by show $(quote i) < $(quote lₚ) ; decide⟩)
    | (.spatial,        i) => `(EnvsIndex.s ⟨$(quote i), by show $(quote i) < $(quote lₛ) ; decide⟩)

  -- clear hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_clear $envsIndex _ ?_
    | fail
  ))
  catch _ => throwError "failed to clear the hypothesis"


elab "iIntro " colGt name:ident : tactic => do
  -- parse syntax
  if name.getId.isAnonymous then
    throwUnsupportedSyntax

  -- extract environment
  let (_, Γₛ, _) ← extractEnvsEntailsFromGoal? true

  -- determine hypothesis list length
  let some s_length ← Γₛ.asListExpr_length?
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
  evalTactic (← `(tactic|
    iRename s $(quote s_length) $name
  ))

elab "iIntro " colGt "#" colGt name:ident : tactic => do
  -- parse syntax
  if name.getId.isAnonymous then
    throwUnsupportedSyntax

  -- extract environment
  let (Γₚ, _, _) ← extractEnvsEntailsFromGoal? true

  -- determine hypothesis list length
  let some p_length ← Γₚ.asListExpr_length?
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
  evalTactic (← `(tactic|
    iRename p $(quote p_length) $name
  ))


elab "iExact " colGt name:ident : tactic => do
  -- parse syntax
  let name := name.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- extract environment
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal?

  let (some lₚ, some lₛ) ← (Γₚ, Γₛ).mapAllM (M := MetaM) Lean.Expr.asListExpr_length?
    | throwError "ill-formed proof environment"

  -- find hypothesis index
  let envsIndex ← match ← findHypothesis? name Γₚ Γₛ with
    | (.intuitionistic, i) => `(EnvsIndex.p ⟨$(quote i), by show $(quote i) < $(quote lₚ) ; decide⟩)
    | (.spatial,        i) => `(EnvsIndex.s ⟨$(quote i), by show $(quote i) < $(quote lₛ) ; decide⟩)

  -- try to solve the goal with the found hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_assumption $envsIndex _
    | fail
  ))
  catch _ => throwError "failed to use the hypothesis to close the goal"

elab "iAssumptionLean" : tactic => do
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

elab "iAssumption" : tactic => do
  -- extract environment
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal?

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
    let envsIndex ← `(EnvsIndex.p ⟨$(quote i), by show $(quote i) < $(quote lₚ) ; decide⟩)
    if ← tryCloseGoal envsIndex then
      return ()

  for i in List.range lₛ do
    let envsIndex ← `(EnvsIndex.s ⟨$(quote i), by show $(quote i) < $(quote lₛ) ; decide⟩)
    if ← tryCloseGoal envsIndex then
      return ()

  -- try all hypotheses from the Lean context
  try evalTactic (← `(tactic|
    first
    | iAssumptionLean
    | fail
  ))
  catch _ => throwError "no matching hypothesis found or remaining environment cannot be cleared"


elab "iSplit" : tactic => do
  -- start proof mode if not already
  evalTactic (← `(tactic|
    iStartProof
  ))

  -- split conjunction
  try evalTactic (← `(tactic|
    first
    | refine tac_and_split _ ?And.left ?And.right
    | fail
  ))
  catch _ => throwError "unable to split conjunction"

namespace Internal

scoped elab "iSplit" side:(&"L" <|> &"R") "[" names:sepBy(ident, ",") "]" : tactic => do
  -- parse syntax
  let splitRight ← match side.getKind with
    | `L => pure false
    | `R => pure true
    | _  => throwUnsupportedSyntax
  let names ← names.getElems.mapM (fun name => do
    let name := name.getId
    if name.isAnonymous then
      throwUnsupportedSyntax
    pure name
  )

  -- extract environment
  let (_, Γₛ, _) ← extractEnvsEntailsFromGoal? true

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

end Internal

macro "iSplitL" "[" names:sepBy(ident, ",") "]" : tactic => `(tactic| iSplit L [$[$names:ident],*])
macro "iSplitR" "[" names:sepBy(ident, ",") "]" : tactic => `(tactic| iSplit R [$[$names:ident],*])

macro "iSplitL" : tactic => `(tactic| iSplit R [])
macro "iSplitR" : tactic => `(tactic| iSplit L [])

end Iris.Proofmode
