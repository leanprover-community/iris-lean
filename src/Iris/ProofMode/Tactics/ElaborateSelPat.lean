import Lean.Data.Name
import Iris.ProofMode.Patterns.SelectPattern

namespace Iris.ProofMode
open Lean

open Lean Elab Tactic Meta Std

inductive iElaboratedSelectPat
| pure
| ident (intuitionistic: Bool) (name : TSyntax ``binderIdent)


elab "ielaborateselpat" colGt pat:iselectPat : tactic => do

  -- parse syntax
  let pat ← liftMacroM <| iSelectPat.parse pat

  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { u, prop, bi, e, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let uniq ← hyps.findWithInfo hyp
  let ⟨e', hyps', out, _, _, _, pf⟩ := hyps.remove true uniq

  let m : Q($e' ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { u, prop, bi, hyps := hyps', goal, .. }

  mvar.assign ((← clearCore bi e e' out goal pf).app m)
  replaceMainGoal [m.mvarId!]
