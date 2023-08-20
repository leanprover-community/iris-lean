/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem pure_assumption [BI PROP] {P A Q : PROP} (h_P : ⊢ A)
    [inst : FromAssumption true A Q] [TCOr (Affine P) (Absorbing Q)] :
    P ⊢ Q :=
  have := intuitionistically_emp.2.trans <| (intuitionistically_mono h_P).trans inst.1
  emp_sep.2.trans <| (sep_mono_l this).trans sep_elim_l

def assumptionLean {prop : Q(Type)} (_bi : Q(BI $prop)) (ehyps goal : Q($prop))
    (mvar : MVarId) : MetaM Unit := do
  mvar.withContext do
    let _ ← synthInstanceQ q(TCOr (Affine $ehyps) (Absorbing $goal))
    for h in ← getLCtx do
      let some #[_, _, hh, (P : Q($prop))] := (← whnfR h.type).appM? ``Entails | continue
      unless (← whnfR hh).isAppOfArity ``BI.emp 2 do continue
      have h : Q(⊢ $P) := .fvar h.fvarId
      -- let (name, type) := (h.userName, ← instantiateMVars h.type)

      -- try to solve the goal
      try
        let _ ← synthInstanceQ q(FromAssumption true $P $goal)
        mvar.assign q(pure_assumption (P := $ehyps) (Q := $goal) $h)
        return
      catch e => trace[Meta.debug] e.toMessageData; pure ()
    throwError "no matching hypothesis found"

elab "iassumption_lean" : tactic => do
  -- retrieve goal mvar declaration
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { bi, e, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
  assumptionLean bi e goal mvar
  replaceMainGoal []

inductive AssumptionFastPath (prop : Q(Type)) (bi : Q(BI $prop)) (Q : Q($prop)) where
  | absorbing (_ : Q(Absorbing $Q))
  | biAffine (_ : Q(BIAffine $prop))

variable {prop : Q(Type)} (bi : Q(BI $prop)) (Q : Q($prop))
  (fastPath : AssumptionFastPath prop bi Q) in
def assumptionFast {e} (hyps : Hyps bi e) : MetaM Q($e ⊢ $Q) := do
  let some ⟨inst, _, _, out, ty, b, _, pf⟩ ←
    hyps.removeG true fun _ _ b ty => try? do
      synthInstance q(FromAssumption $b $ty $Q)
    | failure
  let (_ : Q(FromAssumption $b $ty $Q)) := inst
  have : $out =Q iprop(□?$b $ty) := ⟨⟩
  match fastPath with
  | .absorbing _ => return q(assumption (Q := $Q) $pf)
  | .biAffine _ => return q(assumption (Q := $Q) $pf)

inductive AssumptionSlow {prop : Q(Type)} (bi : Q(BI $prop)) (Q e : Q($prop)) where
  | none
  | affine (pf : Q(Affine $e))
  | main (pf : Q($e ⊢ $Q)) (pf : Option Q(Affine $e))

theorem assumption_l [BI PROP] {P Q R : PROP} [Affine Q] (h : P ⊢ R) : P ∗ Q ⊢ R :=
  sep_elim_l.trans h
theorem assumption_r [BI PROP] {P Q R : PROP} [Affine P] (h : Q ⊢ R) : P ∗ Q ⊢ R :=
  sep_elim_r.trans h

variable {prop : Q(Type)} (bi : Q(BI $prop)) (Q : Q($prop)) in
def assumptionSlow (assume : Bool) :
    ∀ {e}, Hyps bi e → MetaM (AssumptionSlow bi Q e)
  | _, .emp _ =>
    Pure.pure (.affine q(emp_affine))
  | out, .hyp _ _ _ b ty _ => do
    let fromAssum (_:Unit) := do
      let _ ← synthInstanceQ q(FromAssumption $b $ty $Q)
      let inst ← try? (synthInstanceQ q(Affine $out))
      return .main q(FromAssumption.from_assumption) inst
    let affine (_:Unit) := return .affine (← synthInstanceQ q(Affine $out))
    if assume then
      try fromAssum () catch _ => try affine () catch _ => return .none
    else
      try affine () catch _ => try fromAssum () catch _ => return .none
  | _, .sep _ elhs erhs _ lhs rhs => do
    match ← assumptionSlow assume rhs with
    | .none => return .none
    | .affine _ =>
      match ← assumptionSlow assume lhs with
      | .none => return .none
      | .affine _ => return .affine q(sep_affine ..)
      | .main lpf linst =>
        return .main q(assumption_l $lpf) <| linst.map fun _ => q(sep_affine $elhs $erhs)
    | .main rpf rinst =>
      match ← assumptionSlow false lhs, rinst with
      | .none, _ | .main _ none, none => return .none
      | .affine _, rinst | .main _ (some _), rinst =>
        return .main q(assumption_r $rpf) <| rinst.map fun _ => q(sep_affine $elhs $erhs)
      | .main lpf none, some _ => return .main q(assumption_l $lpf) none

elab "iassumption" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, e, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let inst : Option (AssumptionFastPath prop bi goal) ← try
    pure (some (.biAffine (← synthInstanceQ q(BIAffine $prop))))
  catch _ => try? (AssumptionFastPath.absorbing <$> synthInstanceQ q(Absorbing $goal))

  try
    let pf ← match inst with
    | some fastPath => assumptionFast bi goal fastPath hyps
    | none =>
      let .main pf _ ← assumptionSlow bi goal true hyps | failure
      pure pf
    mvar.assign pf
  catch _ =>
    assumptionLean bi e goal mvar
  replaceMainGoal []
