import Iris.Proofmode.Patterns.CasesPattern
import Iris.Proofmode.Theorems
import Iris.Proofmode.Tactics.Rename
import Iris.Std

namespace Iris.Proofmode.Internal
open Iris.Std
open Lean Lean.Elab.Tactic Lean.Meta

def icasesCoreExist (hypIndex : HypothesisIndex) (var : Name) (f : iCasesPat) : TacticM <| Option <| Name × iCasesPat := do
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

def icasesCoreConjunction (hypIndex : HypothesisIndex) (args : Array iCasesPat) : TacticM <| Array <| Name × iCasesPat := do
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

def icasesCoreDisjunction (hypIndex : HypothesisIndex) (args : Array iCasesPat) (mainGoal : MVarId) : TacticM <| Array <| MVarId × Name × iCasesPat := do
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

end Iris.Proofmode.Internal
