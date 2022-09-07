import Iris.BI
import Iris.Proofmode.Environments
import Iris.Proofmode.Expr
import Iris.Proofmode.InputPatterns
import Iris.Proofmode.Theorems
import Iris.Proofmode.Tactics.Cases
import Iris.Proofmode.Tactics.Rename
import Iris.Std

import Lean.Elab

namespace Iris.Proofmode
open Iris.BI Iris.Std Internal
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

elab "istart" : tactic => do
  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← instantiateMVars <| ← getMVarType goal

  -- check if already in proof mode
  if ← isEnvsEntails expr then
    return ()

  -- create environment
  try evalTactic (← `(tactic|
    refine as_emp_valid_2 _ ?_ ;
    refine tac_start _ ?_
  ))
  catch _ => throwError "unable to start proof mode"

elab "istop" : tactic => do
  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← instantiateMVars <| ← getMVarType goal

  -- check if already in proof mode
  if !(← isEnvsEntails expr) then
    throwError "not in proof mode"

  -- reduce proof mode definitions
  try evalTactic (← `(tactic|
    refine tac_stop _ ?_ ;
    simp only [big_op]
  ))
  catch _ => throwError "unable to stop proof mode"


private def extractEnvsEntailsFromGoal (startProofMode : Bool := false) : TacticM <| Expr × Expr × Expr := do
  if startProofMode then
    evalTactic (← `(tactic|
      istart
    ))

  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← instantiateMVars <| ← getMVarType goal

  let some envsEntails ← extractEnvsEntails? expr
    | throwError "not in proof mode"

  return envsEntails

private def findHypothesis (name : Name) : TacticM HypothesisIndex := do
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal
  if let some i ← EnvExpr.findIndex? Γₚ (·.getMDataName?.isEqSome name) then
    let some l ← EnvExpr.length? Γₚ
      | throwError "ill-formed proof environment"
    return ⟨.intuitionistic, i, l⟩
  else if let some i ← EnvExpr.findIndex? Γₛ (·.getMDataName?.isEqSome name) then
    let some l ← EnvExpr.length? Γₛ
      | throwError "ill-formed proof environment"
    return ⟨.spatial, i, l⟩
  else
    throwError "unknown hypothesis"


elab "irename" colGt nameFrom:ident "to" colGt nameTo:ident : tactic => do
  -- parse syntax
  if nameFrom.getId.isAnonymous then
    throwUnsupportedSyntax
  let nameTo := nameTo.getId
  if nameTo.isAnonymous then
    throwUnsupportedSyntax

  -- find and rename hypothesis
  irenameCore (← findHypothesis nameFrom.getId) nameTo


elab "iclear" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId
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


def Internal.iintroCore (type : HypothesisType) (name : Name) : TacticM Unit := do
  -- extract environment
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal true

  let (some lₚ, some lₛ) ← (Γₚ, Γₛ).mapAllM (EnvExpr.length? ·)
    | throwError "ill-formed proof environment"

  match type with
  | .intuitionistic =>
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
  | .spatial =>
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

def Internal.iintroCoreClear : TacticM Unit := do
  -- drop implication premise
  try evalTactic (← `(tactic|
    first
    | istart
      refine tac_impl_intro_drop _ ?_
    | fail
  )) catch _ => throwError "failed to drop implication hypothesis"

def Internal.iintroCoreForall (name : Name) : TacticM Unit := do
  -- introduce universally bound variable
  try evalTactic (← `(tactic|
    first
    | istart
      refine tac_forall_intro _ ?_
      intro $(mkIdent name):ident
    | fail
  ))
  catch _ => throwError "failed to introduce universally bound variable"


elab "iexists" x:term : tactic => do
  -- resolve existential quantifier with the given argument
  try evalTactic (← `(tactic|
    istart ;
    first
    | refine tac_exist _ ?_
      apply Exists.intro $x
    | fail
  )) catch _ => throwError "could not resolve existential quantifier"


elab "iexact" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let hypIndex ← findHypothesis name

  -- try to solve the goal with the found hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_assumption $(← hypIndex.quoteAsEnvsIndex) _
      done
    | fail
  ))
  catch _ => throwError "failed to use the hypothesis to close the goal"

elab "iassumption_lean" : tactic => do
  -- retrieve goal mvar declaration
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved

  let some decl := (← getMCtx).findDecl? goal
    | throwError "ill-formed proof environment"

  -- try all hypotheses from the local context
  for h in decl.lctx do
    let (name, type) := (h.userName, ← instantiateMVars h.type)

    -- match on `⊢ Q`
    let some (P, _) ← extractEntails? type
      | continue
    if !(← isEmp P) then
      continue

    -- try to solve the goal
    try
      evalTactic (← `(tactic|
        first
        | refine tac_assumption_lean _ $(mkIdent name)
          done
        | fail
      ))
      return
    catch _ => continue

  throwError "no matching hypothesis found or remaining environment cannot be cleared"

elab "iassumption" : tactic => do
  -- extract environment
  let (Γₚ, Γₛ, _) ← extractEnvsEntailsFromGoal

  let (some lₚ, some lₛ) ← (Γₚ, Γₛ).mapAllM (M := MetaM) (EnvExpr.length? ·)
    | throwError "ill-formed proof environment"

  -- try to close the goal
  let tryCloseGoal (envsIndex : TSyntax `term) : TacticM Bool := do
    try
      evalTactic (← `(tactic|
        first
        | refine tac_assumption $envsIndex _
          done
        | refine tac_false_destruct $envsIndex _ (by rfl)
          done
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
    iassumption_lean
  ))
  catch _ => throwError "no matching hypothesis found or remaining environment cannot be cleared"


elab "iex_falso" : tactic => do
  -- change goal to `False`
  try evalTactic (← `(tactic|
    first
    | refine tac_ex_falso _ ?_
    | fail
  )) catch _ => throwError "could not turn goal into False"


elab "ipure" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let hypIndex ← findHypothesis name

  -- move hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_pure $(← hypIndex.quoteAsEnvsIndex) _ ?_
      intro $(mkIdent name):ident
    | fail
  )) catch _ => throwError "could not move hypothesis to the Lean context"

elab "iintuitionistic" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let hypIndex ← findHypothesis name

  -- move hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_intuitionistic $(← hypIndex.quoteAsEnvsIndex) _ ?_
    | fail
  )) catch _ => throwError "could not move hypothesis to the intuitionistic context"

  -- extract environment
  let (Γₚ, _, _) ← extractEnvsEntailsFromGoal

  let some lₚ ← EnvExpr.length? Γₚ
    | throwError "ill-formed proof environment"

  -- re-name hypothesis
  irenameCore ⟨.intuitionistic, lₚ - 1, lₚ⟩ name

elab "ispatial" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let hypIndex ← findHypothesis name

  -- move hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_spatial $(← hypIndex.quoteAsEnvsIndex) _ ?_
    | fail
  )) catch _ => throwError "could not move hypothesis to the spatial context"

  -- extract environment
  let (_, Γₛ, _) ← extractEnvsEntailsFromGoal

  let some lₛ ← EnvExpr.length? Γₛ
    | throwError "ill-formed proof environment"

  -- re-name hypothesis
  irenameCore ⟨.spatial, lₛ - 1, lₛ⟩ name


elab "iemp_intro" : tactic => do
  -- solve `emp`
  try evalTactic (← `(tactic|
    istart ;
    first
    | refine tac_emp_intro
      done
    | fail
  )) catch _ => throwError "goal is not `emp` or spatial context is not affine"

elab "ipure_intro" : tactic => do
  -- change into Lean goal
  try evalTactic (← `(tactic|
    istart ;
    first
    | refine tac_pure_intro _ ?_
    | fail
  )) catch _ => throwError "goal is not pure"


elab "isplit" : tactic => do
  -- start proof mode if not already
  evalTactic (← `(tactic|
    istart
  ))

  -- split conjunction
  try evalTactic (← `(tactic|
    first
    | refine tac_and_split _ ?And.left ?And.right
    | fail
  ))
  catch _ => throwError "unable to split conjunction"

declare_syntax_cat splitSide
syntax "l" : splitSide
syntax "r" : splitSide

elab "isplit" side:splitSide "[" hyps:ident,* "]" : tactic => do
  -- parse syntax
  let splitRight ← match side with
    | `(splitSide| l) => pure false
    | `(splitSide| r) => pure true
    | _  => throwUnsupportedSyntax
  let names ← hyps.getElems.mapM (fun name => do
    let name := name.getId
    if name.isAnonymous then
      throwUnsupportedSyntax
    pure name
  )

  -- extract environment
  let (_, Γₛ, _) ← extractEnvsEntailsFromGoal true

  let some lₛ ← EnvExpr.length? Γₛ
    | throwError "ill-formed proof environment"

  -- construct hypothesis mask
  let mut mask := List.replicate lₛ false
  for name in names do
    let some index ← EnvExpr.findIndex? Γₛ (·.getMDataName?.isEqSome name)
      | throwError "unknown spatial hypothesis"

    mask := mask.set index true

  if splitRight then
    mask := mask.map (!·)

  -- split conjunction
  -- TODO we can't inline this for now -> see lean4/#1415
  let h_length_eq ← ``(by show $(quote mask.length) = $(quote lₛ) ; decide)
  try evalTactic (← `(tactic|
    first
    | refine tac_sep_split $(quote mask) $h_length_eq _ ?Sep.left ?Sep.right
    | fail
  ))
  catch _ => throwError "unable to split separating conjunction"

macro "isplit" &"l" : tactic => `(tactic| isplit r [])
macro "isplit" &"r" : tactic => `(tactic| isplit l [])


elab "ileft" : tactic => do
  -- choose left side of disjunction
  try evalTactic (← `(tactic|
    istart ;
    first
    | refine tac_disjunction_l _ ?_
    | fail
  )) catch _ => throwError "goal is not a disjunction"

elab "iright" : tactic => do
  -- choose right side of disjunction
  try evalTactic (← `(tactic|
    istart ;
    first
    | refine tac_disjunction_r _ ?_
    | fail
  )) catch _ => throwError "goal is not a disjunction"


partial def Internal.icasesCore (nameFrom : Name) (pat : iCasesPat) : TacticM Unit := do
  -- focus on main goal and save state
  let mainGoal :: remainingGoals ← getUnsolvedGoals
    | pure ()
  setGoals [mainGoal]

  -- find hypothesis index
  let hypIndex ← findHypothesis nameFrom

  -- process pattern
  processPattern hypIndex pat

  -- restore goal state
  setGoals <| (← getUnsolvedGoals) ++ remainingGoals
where
  processPattern (hypIndex : HypothesisIndex) : iCasesPat → (TacticM Unit)
  | .one nameTo => do
    irenameCore hypIndex nameTo

  | .clear => do
    evalTactic (← `(tactic|
      iclear $(mkIdent nameFrom)
    ))

  | .conjunction args => do
    if let #[] := args then
      throwError "empty constructor is not a valid icases pattern"
    else if let #[arg] := args then
      return ← icasesCore nameFrom arg
    else if let #[.one var, f] := args then
      if let some (name, arg) ← icasesCoreExist hypIndex var f then
        return ← icasesCore name arg

    let remainingArguments ← icasesCoreConjunction hypIndex args

    -- process arguments recursively
    for (name, arg) in remainingArguments do
      let mut goals := []

      for goal in (← getUnsolvedGoals) do
        setGoals [goal]
        icasesCore name arg
        goals := goals ++ (← getUnsolvedGoals)

      setGoals goals

  | .disjunction args => do
    if let #[] := args then
      throwError "empty list of alternatives is not a valid icases pattern"
    else if let #[arg] := args then
      return ← icasesCore nameFrom arg

    let remainingArguments ← icasesCoreDisjunction hypIndex args (← getMainGoal)

    -- process arguments recursively
    let mut goals := []
    for (goal, name, arg) in remainingArguments do
      setGoals [goal]
      icasesCore name arg
      goals := goals ++ (← getUnsolvedGoals)

    setGoals goals

  | .pure (.one nameTo) => do
    irenameCore hypIndex nameTo

    evalTactic (← `(tactic|
      ipure $(mkIdent nameTo)
    ))

  | .pure _ =>
    throwError "cannot further destruct a hypothesis after moving it to the Lean context"

  | .intuitionistic pat => do
    evalTactic (← `(tactic|
      iintuitionistic $(mkIdent nameFrom)
    ))

    icasesCore nameFrom pat

  | .spatial pat => do
    evalTactic (← `(tactic|
      ispatial $(mkIdent nameFrom)
    ))

    icasesCore nameFrom pat

elab "icases" colGt hyp:ident "with" colGt pat:icasesPat : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax
  let some pat := iCasesPat.parse pat
    | throwUnsupportedSyntax

  -- process pattern
  icasesCore name pat


elab "iintro" pats:(colGt icasesPat)* : tactic => do
  -- parse syntax
  let some pats := pats
    |>.map iCasesPat.parse
    |>.sequenceMap id
    | throwUnsupportedSyntax

  for pat in pats do
    let tmpName ← mkFreshUserName `i

    -- introduce hypothesis and determine remaining pattern
    let mut pat? := some pat
    if pat matches .clear then
      iintroCoreClear
      pat? := none
    else if let .pure (.one name) := pat then
      try
        iintroCoreForall name
        pat? := none
      catch _ =>
        iintroCore .spatial tmpName
    else if let .intuitionistic pat := pat then
      iintroCore .intuitionistic tmpName
      pat? := some pat
    else
      iintroCore .spatial tmpName

    -- process pattern
    if let some pat := pat? then
      icasesCore tmpName pat

end Iris.Proofmode
