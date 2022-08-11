import Iris.BI
import Iris.Proofmode.Environments
import Iris.Proofmode.Expr
import Iris.Proofmode.InputPatterns
import Iris.Proofmode.Theorems
import Iris.Std

import Lean.Elab

namespace Iris.Proofmode
open Iris.BI Iris.Std
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

namespace Internal
end Internal
open Internal

elab "istart_proof" : tactic => do
  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← instantiateMVars <| ← getMVarType goal

  -- check if already in proof mode
  if ← isEnvsEntails expr then
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
      istart_proof
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


def Internal.irenameCore (hypIndex : HypothesisIndex) (name : Name) : TacticM Unit := do
  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← instantiateMVars <| ← getMVarType goal

  let some (Γₚ, Γₛ, _) ← extractEnvsEntails? expr
    | throwError "not in proof mode"

  let modifyHypothesis (Γ : Expr) (idx : Nat) : TacticM Expr := do
    -- find hypothesis
    let some h ← EnvExpr.get? Γ idx
      | throwError "invalid index or ill-formed proof environment"

    -- check for unique (or equal) hypothesis name
    let nameFrom? := h.getMDataName?
    if nameFrom? |>.map (· != name) |>.getD true then
      if ← [Γₚ, Γₛ].anyM (fun Γ => do return (← EnvExpr.any? Γ (·.getMDataName?.isEqSome name)) matches some true) then
        throwError "name is already used for another hypothesis"

    -- rename hypothesis
    let h := h.setMDataName? name

    -- re-insert hypothesis
    let some Γ ← EnvExpr.set? Γ h idx
      | throwError "invalid index or ill-formed proof environment"

    return Γ

  -- modify environment
  let (Γₚ, Γₛ) ← match hypIndex with
    | ⟨.intuitionistic, index, _⟩ => do
      pure (← modifyHypothesis Γₚ index, Γₛ)
    | ⟨.spatial, index, _⟩ => do
      pure (Γₚ, ← modifyHypothesis Γₛ index)

  -- update goal
  let some expr ← modifyEnvsEntails? expr Γₚ Γₛ none
    | throwError "ill-formed proof environment"

  setMVarType goal expr

elab "irename" colGt nameFrom:ident "into" colGt nameTo:ident : tactic => do
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
    | istart_proof
      refine tac_impl_intro_drop _ ?_
    | fail
  )) catch _ => throwError "failed to drop implication hypothesis"

def Internal.iintroCoreForall (name : Name) : TacticM Unit := do
  -- introduce universally bound variable
  try evalTactic (← `(tactic|
    first
    | istart_proof
      refine tac_forall_intro _ ?_
      intro $(mkIdent name):ident
    | fail
  ))
  catch _ => throwError "failed to introduce universally bound variable"


elab "iexists" x:term : tactic => do
  -- resolve existential quantifier with the given argument
  try evalTactic (← `(tactic|
    first
    | istart_proof
      refine tac_exist _ ?_
      apply Exists.intro $x
    | fail
  )) catch _ => throwError "could not resolve existential quantifier"


elab "iexact" colGt name:ident : tactic => do
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
  -- retrieve goal mvar declaration
  let some decl := (← getMCtx).findDecl? (← getMainGoal)
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
        refine tac_assumption_lean _ $(mkIdent name)
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


elab "iex_falso" : tactic => do
  -- change goal to `False`
  try evalTactic (← `(tactic|
    first
    | refine tac_ex_falso _ ?_
    | fail
  )) catch _ => throwError "could not turn goal into False"


elab "ipure" colGt name:ident : tactic => do
  -- parse syntax
  if name.getId.isAnonymous then
    throwUnsupportedSyntax

  -- find hypothesis index
  let hypIndex ← findHypothesis name.getId

  -- move hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_pure $(← hypIndex.quoteAsEnvsIndex) _ ?_
      intro $(mkIdent name.getId):ident
    | fail
  )) catch _ => throwError "could not move hypothesis to the Lean context"

elab "iintuitionistic" colGt name:ident : tactic => do
  -- parse syntax
  let name := name.getId
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

elab "ispatial" colGt name:ident : tactic => do
  -- parse syntax
  let name := name.getId
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


elab "ipure_intro" : tactic => do
  -- change into Lean goal
  try evalTactic (← `(tactic|
    first
    | istart_proof
      refine tac_pure_intro _ ?_
    | fail
  )) catch _ => throwError "goal is not pure"


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

declare_syntax_cat splitSide
syntax "l" : splitSide
syntax "r" : splitSide

elab "isplit" side:splitSide "[" names:ident,* "]" : tactic => do
  -- parse syntax
  let splitRight ← match side with
    | `(splitSide| l) => pure false
    | `(splitSide| r) => pure true
    | _  => throwUnsupportedSyntax
  let names ← names.getElems.mapM (fun name => do
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
  let h_length_eq ← `(by show $(quote mask.length) = $(quote lₛ) ; decide)
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
    first
    | refine tac_disjunction_l _ ?_
    | fail
  )) catch _ => throwError "goal is not a disjunction"

elab "iright" : tactic => do
  -- choose right side of disjunction
  try evalTactic (← `(tactic|
    first
    | refine tac_disjunction_r _ ?_
    | fail
  )) catch _ => throwError "goal is not a disjunction"


private def Internal.icasesCoreExist (hypIndex : HypothesisIndex) (var : Name) (f : iCasesPat) : TacticM <| Option <| Name × iCasesPat := do
  -- destruct existential quantifier
  try evalTactic (← `(tactic|
    first
    | refine tac_exist_destruct $(← hypIndex.quoteAsEnvsIndex) _ ?_
      intro $(mkIdent var):ident
    | fail
  )) catch _ => return none

  -- temporarily name hypothesis
  let name ← mkFreshUserName `f
  irenameCore { hypIndex with index := hypIndex.length - 1 } name

  -- return remainig argument
  return (name, f)

private def Internal.icasesCoreConjunction (hypIndex : HypothesisIndex) (args : Array iCasesPat) : TacticM <| Array <| Name × iCasesPat := do
  if h : args.size < 2 then
    throwError "conjunction must contain at least two elements"
  else
  -- proof that `args` is non-empty
  have : 0 < args.size := by
    rw [Nat.not_lt_eq] at h
    let h := Nat.lt_of_succ_le h
    exact Nat.zero_lt_of_lt h

  -- destruct hypothesis with multiple conjunctions
  let mut remainingArguments := #[(.anonymous, args[0])]
  let mut hypIndex := hypIndex
  for h : i in [:args.size - 1] do
    let (h, ra) ← destructChoice hypIndex args ⟨i, h.upper⟩

    -- update hypothesis index and collect remaining arguments
    hypIndex := h
    remainingArguments := remainingArguments |>.pop |>.append ra

  -- return remaining arguments
  return remainingArguments
where
  destructChoice (hypIndex : HypothesisIndex) (args : Array iCasesPat) (i : Fin (args.size - 1)) : TacticM <| HypothesisIndex × (Array <| Name × iCasesPat) := do
    have : i + 1 < args.size := Nat.add_lt_of_lt_sub i.isLt
    have : i     < args.size := Nat.lt_of_succ_lt this

    -- destruct hypothesis and clear one side if requested
    if args[i] matches .clear then
      if let some result ← destructRight hypIndex args[i.val + 1] then
        return result
    else if i + 1 == args.size - 1 && args[i.val + 1] matches .clear then
      if let some result ← destructLeft hypIndex args[i] then
        return result

    let some result ← destruct hypIndex args[i] args[i.val + 1]
      | throwError "failed to destruct conjunction"
    return result

  destructRight (hypIndex : HypothesisIndex) (argR : iCasesPat) : TacticM <| Option <| HypothesisIndex × (Array <| Name × iCasesPat) := do
    -- destruct hypothesis
    try evalTactic (← `(tactic|
      first
      | refine tac_conjunction_destruct_choice $(← hypIndex.quoteAsEnvsIndex) false _ ?_
        simp only [ite_true, ite_false]
      | fail
    )) catch _ => return none

    -- update hypothesis index
    let hypIndex := { hypIndex with index := hypIndex.length - 1 }

    -- temporarily name hypothesis
    let name ← mkFreshUserName `i
    irenameCore hypIndex name

    -- return new hypothesis index and remaining arguments
    return (hypIndex, #[(name, argR)])

  destructLeft (hypIndex : HypothesisIndex) (argL : iCasesPat) : TacticM <| Option <| HypothesisIndex × (Array <| Name × iCasesPat) := do
    -- destruct hypothesis
    try evalTactic (← `(tactic|
      first
      | refine tac_conjunction_destruct_choice $(← hypIndex.quoteAsEnvsIndex) true _ ?_
        simp only [ite_true, ite_false]
      | fail
    )) catch _ => return none

    -- update hypothesis index
    let hypIndex := { hypIndex with index := hypIndex.length - 1 }

    -- temporarily name hypothesis
    let name ← mkFreshUserName `i
    irenameCore hypIndex name

    -- return new hypothesis index and remaining arguments
    return (hypIndex, #[(name, argL)])

  destruct (hypIndex : HypothesisIndex) (argL argR : iCasesPat) : TacticM <| Option <| HypothesisIndex × (Array <| Name × iCasesPat) := do
    -- destruct hypothesis
    try evalTactic (← `(tactic|
      first
      | refine tac_conjunction_destruct $(← hypIndex.quoteAsEnvsIndex) _ ?_
      | fail
    ))
    catch _ => return none

    -- update hypothesis index
    let hypIndex := { hypIndex with index := hypIndex.length, length := hypIndex.length + 1 }

    -- temporarily name hypotheses
    let nameL ← mkFreshUserName `i
    let nameR ← mkFreshUserName `i

    irenameCore { hypIndex with index := hypIndex.length - 2 } nameL
    irenameCore { hypIndex with index := hypIndex.length - 1 } nameR

    -- return new hypothesis index and remaining arguments
    return (hypIndex, #[(nameL, argL), (nameR, argR)])

private def Internal.icasesCoreDisjunction (hypIndex : HypothesisIndex) (args : Array iCasesPat) (mainGoal : MVarId) : TacticM <| Array <| MVarId × Name × iCasesPat := do
  -- find main goal tag
  let tag ← getMVarTag mainGoal

  let mut goalsInd := #[mainGoal]
  let mut hypIndex := hypIndex
  for i in [1:args.size] do
    -- assemble new goal tags
    let tagL := tag ++ s!"Ind_{i}".toName
    let tagR := if i < args.size - 1 then
      tag ++ s!"Ind_{i + 1}_tmp".toName
    else
      tag ++ s!"Ind_{i + 1}".toName

    -- destruct hypothesis
    try evalTactic (← `(tactic|
      first
      | refine tac_disjunction_destruct $(← hypIndex.quoteAsEnvsIndex) _
          ?$(mkIdent <| tagL):ident
          ?$(mkIdent <| tagR):ident
      | fail
    ))
    catch _ => throwError "failed to destruct disjunction"

    -- update hypothesis index for new goals
    hypIndex := { hypIndex with index := hypIndex.length - 1 }

    -- save new goals
    let (some goalL, some goalR) ← (tagL, tagR).mapAllM findGoalFromTag?
      | throwError "goal tag assignment failed"
    goalsInd := goalsInd |>.pop |>.push goalL |>.push goalR

    -- switch to right new goal
    setGoals [goalR]

  -- temporarily name hypotheses and construct remaining arguments
  let remainingArguments ← args |>.zip goalsInd |>.mapM fun (arg, goal) => do
    let name ← mkFreshUserName `i

    setGoals [goal]
    irenameCore { hypIndex with index := hypIndex.length - 1 } name
    return (goal, name, arg)

  -- restore all new goals
  setGoals goalsInd.toList

  -- return remaining arguments
  return remainingArguments

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

elab "icases" colGt name:ident "with" colGt pat:icasesPat : tactic => do
  -- parse syntax
  let name := name.getId
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
