/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

public import Iris.ProofMode.Instances
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open BI Std

theorem pure_elim_spatial [BI PROP] {P P' A Q : PROP} {φ : Prop}
    [hA : IntoPure A φ] [or : TCOr (Affine A) (Absorbing Q)]
    (h : P ⊣⊢ P' ∗ A) (h_entails : φ → P' ⊢ Q) : P ⊢ Q :=
  h.1.trans <| match or with
  | TCOr.l =>
    (sep_mono_right <| (affine_affinely A).2.trans (affinely_mono hA.1)).trans <|
    persistent_and_affinely_sep_right.2.trans (pure_elim_right h_entails)
  | TCOr.r =>
    (sep_mono_right <| hA.1.trans absorbingly_affinely_intro_of_persistent).trans <|
    absorbingly_sep_left_right.2.trans <| persistent_and_affinely_sep_right.2.trans <|
    pure_elim_right fun hφ => (absorbingly_mono <| h_entails hφ).trans absorbing

theorem pure_elim_intuitionistic [BI PROP] {P P' A Q : PROP} {φ : Prop}
    [IntoPure A φ] (h : P ⊣⊢ P' ∗ □ A) (h' : φ → P' ⊢ Q) : P ⊢ Q :=
  pure_elim_spatial h h'

theorem pure_intro_affine [BI PROP] {Q : PROP} {φ : Prop}
    (h : FromPure true Q .out φ) [Affine P] (hφ : φ) : P ⊢ Q :=
  (affine.trans (eq_true hφ ▸ affinely_true.2)).trans h.1

theorem pure_intro_spatial [BI PROP] {Q : PROP} {φ : Prop}
    (h : FromPure false Q .out φ) (hφ : φ) : P ⊢ Q :=
  (pure_intro hφ).trans h.1

public meta section
open Lean Elab Tactic Meta Qq

def iPureDestruct (ty : Q(Prop)) (pat : TSyntax `rcasesPat)
    (k : MVarId → ProofModeM Expr) : ProofModeM Q($ty) := do
  let m : Q($ty) ← mkFreshExprSyntheticOpaqueMVar ty
  let gs ← withRef pat <| Lean.Elab.Tactic.RCases.rintro #[pat] none m.mvarId!
  for g in gs do
    g.withContext do g.assign (← k g)
  instantiateMVars m

def iPureCore {prop : Q(Type u)} (_bi : Q(BI $prop))
    (P P' : Q($prop)) (p : Q(Bool)) (A Q : Q($prop))
    (purePat : TSyntax `rcasesPat) (pf : Q($P ⊣⊢ $P' ∗ □?$p $A))
    (k : ProofModeM Q($P' ⊢ $Q)) : ProofModeM Q($P ⊢ $Q) := do
  let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPure $A $φ)
    | throwError "ipure: {A} is not pure"
  let f ← iPureDestruct q($φ → ($P' ⊢ $Q)) purePat <| fun _ => k
  match matchBool p with
  | .inl _ =>
    return (q(pure_elim_intuitionistic $pf $f))
  | .inr _ =>
    let .some _ ← trySynthInstanceQ q(TCOr (Affine $A) (Absorbing $Q))
      | throwError "ipure: {A} is not affine and the goal not absorbing"
    return q(pure_elim_spatial (A := $A) $pf $f)

def iPureIntroCore {u} {prop : Q(Type u)} (_bi : Q(BI $prop))
    (e goal : Q($prop)) (tacName : String) :
    ProofModeM <| Q($e ⊢ $goal) × MVarId := do
  let b : Q(Bool) ← mkFreshExprMVarQ q(Bool)
  let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let .some h ← ProofModeM.trySynthInstanceQ q(FromPure $b $goal .out $φ)
  | throwError "{tacName}: {goal} is not pure"
  let m : Q($φ) ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars φ)

  let pf : Q($e ⊢ $goal) ← do
    match ← whnf b with
    | .const ``true _ =>
      have : $b =Q true := ⟨⟩
      let .some _ ← trySynthInstanceQ q(Affine $e)
        | throwError "{tacName}: context is not affine"
      pure q(pure_intro_affine (P := $e) (Q := $goal) $h $m)
    | .const ``false _ =>
      have : $b =Q false := ⟨⟩
      pure q(pure_intro_spatial (P := $e) (Q := $goal) $h $m)
    -- the following indicates a bug in the typeclass instances that generate b
    | _ => throwError "{tacName}: bug in typeclass instances, cannot reduce {b} to true or false"

  return ⟨pf, m.mvarId!⟩

/--
  `ipure H` moves a pure hypothesis `H` from the Iris context into the regular
  Lean context.
-/
elab "ipure " colGt hyp:ident : tactic => do
  ProofModeM.runTactic λ mvar { bi, e, hyps, goal, .. } => do

  let ivar ← hyps.findWithInfo hyp
  let ⟨e', hyps', _, out', p, _, pf⟩ := hyps.remove true ivar

  let pf ← iPureCore bi e e' p out' goal (← `(rcasesPat| $hyp:ident)) pf <| addBIGoal hyps' goal

  mvar.assign pf

/--
  `iempintro` solves an `emp` goal, provided that the spatial context is affine.
-/
elab "iempintro" : tactic => do
  ProofModeM.runTactic λ mvar { prop, e, goal, .. } => do

  let .true ← isDefEq goal q(emp : $prop) | throwError "goal is not `emp`"
  let .some _ ← trySynthInstanceQ q(Affine $e)
    | throwError "iempintro: context is not affine"
  mvar.assign q(affine (P := $e))

/--
  `ipureintro` turns a goal of the form `⌜φ⌝` into the Lean goal `φ`.
-/
elab "ipureintro" : tactic => do
  ProofModeM.runTactic λ mvar { bi, e, goal, .. } => do
    let ⟨pf, m⟩ ← iPureIntroCore bi e goal "ipureintro"
    addMVarGoal m
    mvar.assign pf

-- TODO: what is the best lean automation tactic to call here?
-- `assumption` is necessary if the goal contains mvars
macro_rules | `(tactic| itrivial) => `(tactic| (first | ipureintro | exfalso) <;> (first | simp [*] | assumption) <;> done)
