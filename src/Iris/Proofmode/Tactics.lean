import Iris.Proofmode.Environments
import Iris.Proofmode.Reduction
import Iris.Proofmode.Theorems
import Iris.Std.Syntax

import Lean.Elab

namespace Iris.Proofmode
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
  evalTactic (← `(tactic|
    refine (as_emp_valid_2 _ ?_) ;
    refine (tac_start _ ?_)
  ))


elab "iStopProof" : tactic => do
  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← (← getMVarType goal) |> instantiateMVars

  -- check if already in proof mode
  if !(isEnvsEntails expr) then
    throwError "not in proof mode"

  evalTactic (← `(tactic|
    simp only [envs_entails, of_envs] ;
    pmReduce
  ))


namespace Internal

scoped elab "iRename " categ:(&"p" <|> &"s") idx:num name:ident : tactic => do
  -- parse syntax
  let categ : Option HypothesisType := match categ.getKind with
    | `p => some .intuitionistic
    | `s => some .spatial
    | _  => none
  let some categ := categ
    | throwUnsupportedSyntax
  let some idx := idx.getAtomValFromNode? `num String.toNat?
    | throwUnsupportedSyntax
  let name := name.getId

  -- parse goal
  let goal :: _ ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let expr ← (← getMVarType goal) |> instantiateMVars

  let some (Γₚ, Γₛ, _) := extractEnvsEntails? expr
    | throwError "not in proof mode"

  -- check for unique hypothesis name
  if [Γₚ, Γₛ].any (·.asListExpr_any? (·.getMDataName?.isEqSome name) matches some true) then
    throwError "name is already used for another hypothesis"

  -- find hypothesis
  let Γ := match categ with
    | .intuitionistic => Γₚ
    | .spatial        => Γₛ
  let some h := Γ.asListExpr_get? idx
    | throwError "invalid index or ill-formed proof environment"

  -- rename
  let h := h.setMDataName? name

  -- insert modified hypothesis
  let some Γ := Γ.asListExpr_set? h idx
    | throwError "invalid index or ill-formed proof environment"
  let Γₚ := if categ matches .intuitionistic then Γ else Γₚ
  let Γₛ := if categ matches .spatial        then Γ else Γₛ

  -- update goal
  let some expr := modifyEnvsEntails? expr Γₚ Γₛ none
    | throwError "ill-formed proof environment"

  setMVarType goal expr

end Internal

end Iris.Proofmode
