/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Yunsong Yang
-/
module

public import Iris.ProofMode.ClassesMake
public meta import Iris.ProofMode.Patterns.SelPattern
public meta import Iris.ProofMode.Tactics.Basic

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Lean.Meta.Tactic.TryThis

namespace Iris.ProofMode

public section
open BI Std

theorem wand_revert [BI PROP] {Δ Δ' P Q : PROP}
    (h1 : Δ ⊣⊢ Δ' ∗ P) (h2 : Δ' ⊢ P -∗ Q) : Δ ⊢ Q :=
  h1.mp.trans (wand_elim h2)

theorem forall_revert {α} [BI PROP] {Δ : PROP} {Ψ : α → PROP}
    (h : Δ ⊢ BI.forall Ψ) : ∀ x, Δ ⊢ Ψ x :=
  λ x => h.trans (forall_elim x)

theorem pure_revert [BI PROP] {Δ P Q : PROP} {φ : Prop}
    [hA : MakeAffinely iprop(⌜φ⌝) P]
    (h : Δ ⊢ P -∗ Q) : φ → Δ ⊢ Q := by
  intro hp
  have hA : (emp : PROP) ⊢ P :=
    (affinely_emp.mpr.trans <| affinely_mono <| pure_intro hp).trans (hA.make_affinely.mp)
  exact (sep_emp.mpr.trans (sep_mono .rfl hA)).trans (wand_elim h)

public meta section
open Lean Elab Tactic Meta Qq

/--
  `reverted` collects lean variables already reverted. This is necessary for dependency checks
  since they are only cleared from the Lean context for the final goal.
-/
private structure RevertState {prop : Q(Type u)} {bi : Q(BI $prop)} (origE origGoal : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e) (goal : Q($prop))
  (reverted : Array FVarId := #[])
  pf : Q(($e ⊢ $goal) → ($origE ⊢ $origGoal))

/-- Revert a proofmode hypothesis by turning it into a wand premise. -/
private def RevertState.revertProofModeHyp
    : @RevertState u prop bi origE origGoal → IVarId →
      ProofModeM (@RevertState u prop bi origE origGoal)
  | { hyps, goal, reverted, pf, .. }, ivar => do
    let ⟨e', hyps', out, _, _, _, hΔ⟩ := hyps.remove true ivar
    return { e := e', hyps := hyps', goal := q(wand $out $goal), reverted,
             pf := q(fun h => $pf (wand_revert $hΔ h)) }

/-- Revert a Lean proposition by turning it into the `MakeAffinely` pure premise. -/
private def RevertState.revertLeanPropHyp
    (st : @RevertState u prop bi origE origGoal) (f : FVarId) (φ : Q(Prop)) :
    ProofModeM (@RevertState u prop bi origE origGoal) := do
  let { e, hyps, goal, reverted, pf } := st
  let P ← mkFreshExprMVarQ prop
  let _hA : Q(MakeAffinely iprop(⌜$φ⌝) $P) ← synthInstanceQ q(MakeAffinely iprop(⌜$φ⌝) $P)
  let hp : Q($φ) := mkFVar f
  let goal' : Q($prop) := q(iprop($P -∗ $goal))
  let pf' : Q(($e ⊢ $goal') → ($origE ⊢ $origGoal)) := q(fun h => $pf (pure_revert h $hp))
  return { e, hyps, goal := goal', reverted := reverted.push f, pf := pf' }

/-- Revert a Lean non-`Prop` local by turning the current goal into a forall. -/
private def RevertState.revertLeanForallHyp
    (st : @RevertState u prop bi origE origGoal) (f : FVarId) (α : Q(Sort v)) :
    ProofModeM (@RevertState u prop bi origE origGoal) := do
  let { e, hyps, goal, reverted, pf } := st
  let x : Q($α) := mkFVar f
  -- abstract over x in the goal
  let Φ ← mkLambdaFVars #[x] goal
  -- make sure that the binder info is set to default, otherwise the
  -- printing of BI.forall breaks
  have Φ : Q($α → $prop) :=
    match Φ with | .lam n t b _ => .lam n t b .default | e => e
  let goal' : Q($prop) := q(BI.forall $Φ)
  have pf' : Q(($e ⊢ $goal') → ($origE ⊢ $origGoal)) :=
    ← withLocalDeclDQ `h q($e ⊢ BI.forall $Φ) fun h => do
      mkLambdaFVars #[h] (mkApp pf (← mkAppM ``forall_revert #[h, x]))
  return { e, hyps, goal := goal', reverted := reverted.push f, pf := pf' }

/-- Revert a Lean local after checking proofmode and local-context dependencies. -/
private def RevertState.revertLeanHyp
    (st : @RevertState u prop bi origE origGoal) (f : FVarId) :
    ProofModeM (@RevertState u prop bi origE origGoal) := do
  let ldecl ← st.hyps.checkRemovableFVar "irevert" f none st.reverted.contains
  let v : Level ← Meta.getLevel ldecl.type
  have α : Q(Sort v) := ldecl.type
  if (← Meta.isProp α) && !st.goal.containsFVar f then
    have φ : Q(Prop) := α
    st.revertLeanPropHyp f φ
  else
    st.revertLeanForallHyp f α

/--
  When the tactic `irevert z₁ ... zₙ` is applied, `z₁ ... zₙ`, which can be
  regular Lean variables or Iris hypotheses, are reverted from the context.
  This function checks that hypotheses depending on any of `z₁ ... zₙ` is also
  included for reverting.

  This function is also used for `iinduction e generalizing z₁ ... zₙ` and
  `iloeb as IH generalizing z₁ ... zₙ`. When such a tactic applied,
  the variables `z₁ ... zₙ`, it is possible that `x` is amongst the Lean
  variables explcitly reverted by the user using the `generalizing` syntax while
  there exists another Lean variable `y` such that `y` depends on `x`. In this
  case, this function suggests that the user includes `%y` in the `generalizing`
  syntax.

  It is also possible that `x` is amongst the Lean variables being generalised
  such that there exists an Iris hypothesis `HP` in the intuitionistic context
  where:
  1. `P` does not depend on the induction target and thus not reverted automatically,
  2. `P` depends on `x` in the `generalizing` syntax, and
  3. `P` itself is not included in the `generalizing` syntax.
  In this case, this function suggests the user to include `HP` in the
  `generalizing` syntax.

  Note that Iris hypotheses in the spatial context are always reverted, so there
  is no need for further checks by this function.
-/
def checkDependentHyps {u} {prop : Q(Type $u)} {bi} {e : Q($prop)}
    (tacticName : String) (hyps : Hyps bi e) (explicitTargets : List SelTarget)
    (mkSuggestion :
      Array (TSyntax `selPat) →
      Array (TSyntax `selPat) →
      ProofModeM (TSyntax `tactic)):
    ProofModeM Unit := do

  let explicitIrisIVarIds := explicitTargets.filterMap
    (match ·.kind with | .ipm ivar => some ivar | _ => none)
  let explicitPureFVars := explicitTargets.filterMap
    (match ·.kind with | .pure f => some f | _ => none)

  -- Pairs of `FVarId` values `(f1, f2)` indicating `f1` depends on `f2`.
  let mut missingPure : List (FVarId × FVarId) := []

  -- Check forward dependency of pure hypotheses in the `generalizing` syntax
  for fvar in explicitPureFVars.eraseDups do
    let fwdDeps ← collectForwardDeps #[mkFVar fvar] false
    for dep in fwdDeps do
      let depId := dep.fvarId!
      -- Skip `x` itself and variables already included in `explicitPureFVars`
      if depId != fvar && !explicitPureFVars.contains depId then
        -- Record the missing hypothesis to be generalised, if not already included
        if !missingPure.any (·.fst == depId) then
          missingPure := missingPure ++ [(depId, fvar)]

  let allPureFVars := explicitPureFVars ++ missingPure.map (·.fst)

  -- Check Iris hypothesis that depend on hypotheses in the `generalizing` syntax
  let missingIris : List (Name × FVarId) :=
  hyps.intuitionisticIVarIds.filterMap fun ivar =>
    if explicitIrisIVarIds.contains ivar then none
    else match hyps.getDecl? ivar with
      | some ⟨name, _, _, ty⟩ =>
        match allPureFVars.find? (ty.containsFVar ·) with
        | some x => some (name, x)
        | none   => none
      | none => none

  -- Throw an error if there exists some pure/Lean hypotheses that should also be generalised
  if !missingPure.isEmpty || !missingIris.isEmpty then
    let leanLines ← missingPure.mapM fun (depId, srcId) => do
      let depDecl ← depId.getDecl
      let srcDecl ← srcId.getDecl
      return s!"• Lean hypothesis `{depDecl.userName}` depends on `{srcDecl.userName}`"
    let irisLines ← missingIris.mapM fun (name, srcId) => do
      let srcDecl ← srcId.getDecl
      return s!"• Iris hypothesis in the intuitionstic context `{name}` depends on `{srcDecl.userName}`"

    -- Sort the pure Lean hypothesis according to the dependency
    let allPureFVarsSorted := (← getLCtx).sortFVarsByContextOrder allPureFVars.eraseDups.toArray
    let sortedPurePats : Array (TSyntax `selPat) ← allPureFVarsSorted.mapM fun fvarId => do
      let decl ← fvarId.getDecl
      let id := mkIdent (.mkSimple decl.userName.toString)
      `(selPat| %$id:ident)

    -- Build `selPat` syntax nodes for each missing item
    let newIrisPats : Array (TSyntax `selPat) ←
      missingIris.toArray.mapM fun (name, _) => `(selPat| $(mkIdent name):ident)

    -- Find the old tactic syntax and generate the new one with missing hypotheses added
    let oldTactic ← getRef
    let newTactic ← mkSuggestion sortedPurePats newIrisPats

    -- Suggestion the fixed tactic
    Lean.Meta.Tactic.TryThis.addSuggestion oldTactic newTactic

    -- Log the error and attach the clickable suggestion
    throwError m!"{tacticName}: The following hypotheses depend on variables in \
      the `generalizing` clause but are not themselves included:\
      \n{"\n".intercalate (leanLines ++ irisLines)}"

syntax (name := irevert) "irevert" (colGt ppSpace selPat)+ : tactic

/--
  A helper function for `checkDependentHyps` to generate the fixed tactic.
-/
private def checkDependentHypsMkSuggestion
    (purePats : Array (TSyntax `selPat)) (newIrisPats : Array (TSyntax `selPat)) :
    ProofModeM (TSyntax `tactic) := do
    let oldTactic ← getRef
    let `(tactic| irevert $pats:selPat*) := oldTactic
      | throwError "irevert: invalid syntax"
    let existingIrisPats := pats.filter fun p =>
      match p.raw with
      | `(selPat| %$_:ident) => false
      | _ => true
    let extendedPats : TSyntaxArray `selPat := purePats ++ existingIrisPats ++ newIrisPats
    `(tactic| irevert $extendedPats*)

def iRevertCore (targets : List SelTarget) {u : Level}{prop: Q(Type $u)}{bi : Q(BI $prop)}{e : Q($prop)}(hyps : Hyps bi e)(goal: Q($prop))
  (k : ∀ {e : Q($prop)}, Hyps bi e → (goal: Q($prop)) → ProofModeM Q($e ⊢ $goal) := addBIGoal) :
    ProofModeM Q($e ⊢ $goal) := do
  checkDependentHyps "irevert" hyps targets checkDependentHypsMkSuggestion

  let init : RevertState e goal := { e, hyps, goal, pf := q(id) }
  let st ← targets.reverse.foldlM (init := init) fun st target => do
      match target.kind with
      | .ipm ivar => st.revertProofModeHyp ivar
      | .pure fvar => st.revertLeanHyp fvar

  let pf' : Q($(st.e) ⊢ $(st.goal)) ← withoutFVars (u:=0) st.reverted (k st.hyps st.goal)
  return q($(st.pf) $pf')

elab_rules : tactic
  | `(tactic| irevert $pats:selPat*) => do
  let pats ← liftMacroM <| SelPat.parse pats

  ProofModeM.runTactic fun mvar {hyps, goal, ..} => do
    let targets ← SelPat.resolve hyps pats
    let expr ← iRevertCore targets hyps goal
    mvar.assign expr
