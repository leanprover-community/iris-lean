/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.Proofmode.Tactics.Basic
import Iris.Proofmode.Tactics.Remove

namespace Iris.Proofmode
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
  let some { bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
  assumptionLean bi hyps.strip goal mvar
  replaceMainGoal []

inductive AssumptionFastPath (prop : Q(Type)) (bi : Q(BI $prop)) (Q : Q($prop)) where
  | absorbing (_ : Q(Absorbing $Q))
  | biAffine (_ : Q(BIAffine $prop))

variable {prop : Q(Type)} (bi : Q(BI $prop)) (Q : Q($prop))
  (fastPath : AssumptionFastPath prop bi Q) in
def assumptionFast (hyps : Hyps prop) : MetaM Q($hyps.strip ⊢ $Q) := do
  let some ⟨inst, _, out, ty, b, _, pf⟩ ←
    hyps.removeG bi true fun kind _ ty => try? do
      let b := match kind with
      | .intuitionistic => q(true)
      | .spatial => q(false)
      synthInstance q(FromAssumption $b $ty $Q)
    | failure
  let (_ : Q(FromAssumption $b $ty $Q)) := inst
  have : $out =Q iprop(□?$b $ty) := ⟨⟩
  match fastPath with
  | .absorbing _ =>
    return q(assumption (Q := $Q) $pf)
  | .biAffine s =>
    have : @BIAffine.toBI _ $s =Q $bi := ⟨⟩
    return q(assumption (Q := $Q) $pf)

inductive AssumptionSlow (prop : Q(Type)) (bi : Q(BI $prop)) (Q e : Q($prop)) where
  | none
  | affine (pf : Q(Affine $e))
  | main (pf : Q($e ⊢ $Q)) (pf : Option Q(Affine $e))

theorem assumption_l [BI PROP] {P Q R : PROP} [Affine Q] (h : P ⊢ R) : P ∗ Q ⊢ R :=
  sep_elim_l.trans h
theorem assumption_r [BI PROP] {P Q R : PROP} [Affine P] (h : Q ⊢ R) : P ∗ Q ⊢ R :=
  sep_elim_r.trans h

variable {prop : Q(Type)} (bi : Q(BI $prop)) (Q : Q($prop)) in
def assumptionSlow (assume : Bool) :
    (hyps : Hyps prop) → MetaM (AssumptionSlow prop bi Q hyps.strip)
  | .emp s =>
    have : $s =Q emp := ⟨⟩
    Pure.pure (.affine q(emp_affine))
  | .hyp _ out kind _ ty => do
    let b := match kind with
    | .intuitionistic => q(true)
    | .spatial => q(false)
    have : $out =Q iprop(□?$b $ty) := ⟨⟩
    let fromAssum (_:Unit) := do
      let _ ← synthInstanceQ q(FromAssumption $b $ty $Q)
      let inst ← try? (synthInstanceQ q(Affine $out))
      return .main q(FromAssumption.from_assumption) inst
    let affine (_:Unit) := return .affine (← synthInstanceQ q(Affine $out))
    if assume then
      try fromAssum () catch _ => try affine () catch _ => return .none
    else
      try affine () catch _ => try fromAssum () catch _ => return .none
  | .sep _ s lhs rhs => do
    let elhs := lhs.strip
    let erhs := rhs.strip
    match ← assumptionSlow assume rhs with
    | .none => return .none
    | .affine hr =>
      match ← assumptionSlow assume lhs with
      | .none => return .none
      | .affine _ =>
        have : $s =Q iprop($elhs ∗ $erhs) := ⟨⟩
        return .affine q(sep_affine ..)
      | .main lpf (linst : Option Q(Affine $elhs)) =>
        let linst := linst.map fun hl =>
          -- FIXME: these haves should not be necessary
          have elhs := elhs; have erhs := erhs
          have : Q(Affine $elhs) := hl; have : Q(Affine $erhs) := hr
          have : $s =Q iprop($elhs ∗ $erhs) := ⟨⟩
          q(sep_affine $elhs $erhs)
        have : $s =Q iprop($elhs ∗ $erhs) := ⟨⟩
        return .main q(assumption_l $lpf) linst
    | .main rpf rinst =>
      match ← assumptionSlow false lhs, rinst with
      | .none, _ | .main _ none, none => return .none
      | .affine hl, rinst | .main _ (some hl), rinst =>
        let rinst := rinst.map fun hr =>
          -- FIXME: these haves should not be necessary
          have elhs := elhs; have erhs := erhs
          have : Q(Affine $elhs) := hl; have : Q(Affine $erhs) := hr
          have : $s =Q iprop($elhs ∗ $erhs) := ⟨⟩
          q(sep_affine $elhs $erhs)
        have : $s =Q iprop($elhs ∗ $erhs) := ⟨⟩
        return .main q(assumption_r $rpf) rinst
      | .main lpf none, some _ =>
        have : $s =Q iprop($elhs ∗ $erhs) := ⟨⟩
        return .main q(assumption_l $lpf) none

elab "iassumption" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

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
    assumptionLean bi hyps.strip goal mvar
  replaceMainGoal []
