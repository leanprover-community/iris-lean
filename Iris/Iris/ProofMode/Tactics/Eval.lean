/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Patterns.SelPattern
public meta import Iris.ProofMode.ProofModeM

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Lean.Parser.Tactic

/-- For iteratively applying the tactic sequences to selection targets in the context -/
private structure EvalState {u} {prop : Q(Type u)} {bi : Q(BI $prop)} (e : Q($prop)) where
  {newE : Q($prop)}
  (newHyps : Hyps bi newE)
  (pf : Q($e ⊢ $newE))

/--
  Apply the tactic sequence `tac` to transform `ty`, which is strengthened when
  it is the goal or weakened when it is a hypothesis in the context.

  When `isGoal` is `true`, the tactic sequence results in the proof goal being *strengthened*.
  When `isGoal` is `false`, the tactic sequence results in the hypothesis being *weakened*.

  The function returns the new expression and a proof that the expression
  is strengthened/weakened.
-/
private def iEvalOne {u} {prop : Q(Type u)} (bi : Q(BI $prop))
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (isGoal : Bool) (ty : Q($prop)) :
    ProofModeM <| Q($prop) × Expr := do
  let m : Q($prop) ← mkFreshExprMVar q($prop)
  let pf ← mkFreshExprSyntheticOpaqueMVar <| if isGoal then q($m ⊢ $ty) else q($ty ⊢ $m)
  let [g] ← evalTacticAt tac pf.mvarId!
    | throwError "ieval: the supplied tactic does not produce exactly one subgoal"
  let some #[_, _, lhs, rhs] ← g.getType <&> (·.appM? ``Entails)
    | throwError "ieval: the goal is not Iris entailment upon applying the supplied tactic"
  let newTy : Q($prop) := if isGoal then rhs else lhs
  m.mvarId!.assign newTy
  g.assign (q(.rfl) : Q($newTy ⊢ $newTy))
  return ⟨m, pf⟩

/--
  Apply the tactic sequence `tac` to either the proof goal (when `selTargets`
  is `none`) or the hypotheses in the context specified by the selection targets.
-/
private def iEvalCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
    (selTargets : Option <| List SelTarget) : ProofModeM Q($e ⊢ $goal) := do
  match selTargets with
  -- No selection pattern given, apply the tactics to the proof goal
  | none =>
    let ⟨newGoal, (pf : Q($newGoal ⊢ $goal))⟩ ← iEvalOne (isGoal := true) bi tac goal
    let pf' ← addBIGoal hyps newGoal
    return q($(pf').trans $pf)
  -- Selection patterns given, apply the tactics to the chosen hypotheses
  | some selTargets =>
    let mut evalState : EvalState e := { newHyps := hyps, pf := q(.rfl) }
    -- Iteratively apply the supplied tactic sequence to the selection targets
    for selTarget in selTargets do
      evalState ← match selTarget.kind with
      | .pure _ =>
        throwError "ieval: pure hypotheses in the selection pattern is not supported"
      | .ipm ivar =>
        let some ⟨newE, newHyps, pf⟩ ← evalState.newHyps.evalReplace ivar fun ty => do
          let ⟨newTy, pf⟩ ← iEvalOne (isGoal := false) bi tac ty
          return ⟨newTy, (pf : Q($ty ⊢ $newTy))⟩
        | throwError m!"ieval: unable to find the hypothesis {ivar.name} in the context"
        pure { newE, newHyps, pf := q($(evalState.pf).trans $pf) }
    let pf' ← addBIGoal evalState.newHyps goal
    return q($(evalState.pf).trans $pf')

/--
  `ieval (tac)` applies the tactic sequence `tac` to the proof goal.
-/
elab "ieval " "(" tac:tacticSeq ")" : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let pf ← iEvalCore hyps goal tac none
    mvar.assign pf

/--
  `ieval (tac) in spats` applies the tactic sequence `tac` to the Iris
  hypotheses chosen by the selection pattern `spats`. Pure hypotheses are not
  supported by this tactic.
-/
elab "ieval " "(" tacs:tacticSeq ")" " in " spats:(colGt ppSpace selPat)+ : tactic => do
  let selPats ← liftMacroM <| SelPat.parse spats

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let selTargets ← SelPat.resolve hyps selPats
    let pf ← iEvalCore hyps goal tacs selTargets
    mvar.assign pf

/--
  `isimp` applies `simp` to the proof goal. This is shorthand for `ieval (simp)`.

  `isimp in spats` applies `simp` to the Iris hypotheses chosen by the
  selection pattern `spats`. Pure hypotheses are not supported by this tactic.
  This is shorthand for `ieval (simp) in spats`.

  One can also use `isimp [h₁, h₂, …, hₙ]`, `isimp [*]` and
  `isimp only [h₁, h₂, …, hₙ]` for the tactic behaviour corresponding to
  `simp [h₁, h₂, …, hₙ]`, `simp [*]` and `simp only [h₁, h₂, …, hₙ]`,
  respectively.
-/
syntax "isimp" optConfig (discharger)? (&" only")? (simpArgs)?
  (" in " (colGt ppSpace selPat)+)? : tactic

private def elabSimp (simp : TSyntax `tactic)
    (spats : Option (TSyntaxArray `selPat)) : TacticM Unit :=
  match spats with
  | none       => do evalTactic (← `(tactic| ieval ($simp:tactic)))
  | some spats => do evalTactic (← `(tactic| ieval ($simp:tactic) in $spats*))

elab_rules : tactic
  | `(tactic| isimp $cfg* $[$disch]? $[[$args,*]]? $[in $spats*]?) => do
      elabSimp (← `(tactic| simp $cfg* $[$disch]? $[[$args,*]]?)) spats
  | `(tactic| isimp $cfg* $[$disch]? only $[[$args,*]]? $[in $spats*]?) => do
      elabSimp (← `(tactic| simp $cfg* $[$disch]? only $[[$args,*]]?)) spats

/-- `iunfold hs` applies `unfold hs` to the proof goal. This is shorthand for `ieval (unfold)`. -/
macro "iunfold " hs:ident,+ : tactic => `(tactic| ieval (unfold $hs*))

/--
  `iunfold hs in spats` applies `unfold hs` to the Iris hypotheses chosen by
  the selection pattern `spats`. Pure hypotheses are not supported by this tactic.
  This is shorthand for `ieval (unfold hs) in spats`.
-/
macro "iunfold " hs:ident,+ " in " spats:(colGt ppSpace selPat)* : tactic =>
  `(tactic| ieval (unfold $hs*) in $spats*)
