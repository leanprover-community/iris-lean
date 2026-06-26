/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open BI Std

theorem pure_elim_spatial [BI PROP] {P P' A Q : PROP} {φ : Prop}
    (hA : IntoPure A φ) (or : TCOr (Affine A) (Absorbing Q))
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
    (instIntoPure : IntoPure A φ) (h : P ⊣⊢ P' ∗ □ A) (h' : φ → P' ⊢ Q) : P ⊢ Q :=
  have instAffine := @TCOr.l (Affine iprop(□ A)) (Absorbing Q) ⟨(intuitionistically_affine A).affine⟩
  pure_elim_spatial ⟨intuitionistically_elim.trans instIntoPure.into_pure⟩ instAffine h h'

public meta section
open Lean Elab Tactic Meta Qq

def iPureCore {prop : Q(Type u)} (_bi : Q(BI $prop))
    (P P' : Q($prop)) (p : Q(Bool)) (A Q : Q($prop)) (name : TSyntax ``binderIdent) (pf : Q($P ⊣⊢ $P' ∗ □?$p $A))
    (k : (φ : Q(Prop)) → Q($φ) → ProofModeM (Q($P' ⊢ $Q))) : ProofModeM (Q($P ⊢ $Q)) := do
  let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let .some instIntoPure ← ProofModeM.trySynthInstanceQ q(IntoPure $A $φ)
    | throwError "ipure: {A} is not pure"

  let (name, ref) ← getFreshName name
  withLocalDeclDQ name φ fun h => do
    addLocalVarInfo ref (← getLCtx) h φ
    let m ← k φ h
    let f : Q($φ → $P' ⊢ $Q) ← mkLambdaFVars #[h] m

    match matchBool p with
    | .inl _ =>
      return (q(pure_elim_intuitionistic $instIntoPure $pf $f))
    | .inr _ =>
      let .some instAffineAbsorbing ← trySynthInstanceQ q(TCOr (Affine $A) (Absorbing $Q))
        | throwError "ipure: {A} is not affine and the goal not absorbing"
      return q(pure_elim_spatial $instIntoPure $instAffineAbsorbing $pf $f)

/--
  `ipure H` moves a pure hypothesis `H` from the Iris context into the regular
  Lean context.
-/
elab "ipure " colGt hyp:ident : tactic => do
  ProofModeM.runTactic λ mvar { bi, e, hyps, goal, .. } => do

  let ivar ← hyps.findWithInfo hyp
  let ⟨e', hyps', _, out', p, _, pf⟩ := hyps.remove true ivar

  let pf ← iPureCore bi e e' p out' goal (← `(binderIdent| $hyp:ident)) pf fun _ _ => addBIGoal hyps' goal

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

theorem pure_intro_affine [BI PROP] {Q : PROP} {φ : Prop}
    (h : FromPure true Q .out φ) [Affine P] (hφ : φ) : P ⊢ Q :=
  (affine.trans (eq_true hφ ▸ affinely_true.2)).trans h.1

theorem pure_intro_spatial [BI PROP] {Q : PROP} {φ : Prop}
    (h : FromPure false Q .out φ) (hφ : φ) : P ⊢ Q :=
  (pure_intro hφ).trans h.1

/--
  `ipureintro` turns a goal of the form `⌜φ⌝` into the Lean goal `φ`.
-/
elab "ipureintro" : tactic => do
  ProofModeM.runTactic λ mvar { e, goal, .. } => do

  let b : Q(Bool) ← mkFreshExprMVarQ q(Bool)
  let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let .some h ← ProofModeM.trySynthInstanceQ q(FromPure $b $goal .out $φ)
    | throwError "ipureintro: {goal} is not pure"
  let m : Q($φ) ← mkFreshExprMVar (← instantiateMVars φ)
  addMVarGoal m.mvarId!

  match ← whnf b with
  | .const ``true _ =>
    have : $b =Q true := ⟨⟩
    let .some _ ← trySynthInstanceQ q(Affine $e)
      | throwError "ipureintro: context is not affine"
    mvar.assign q(pure_intro_affine (P := $e) (Q := $goal) $h $m)
  | .const ``false _ =>
    have : $b =Q false := ⟨⟩
    mvar.assign q(pure_intro_spatial (P := $e) (Q := $goal) $h $m)
  -- the following indicates a bug in the typeclass instances that generate b
  | _ => throwError "ipureintro: bug in typeclass instances, cannot reduce {b} to true or false"

-- TODO: what is the best lean automation tactic to call here?
-- `assumption` is necessary if the goal contains mvars
macro_rules | `(tactic| itrivial) => `(tactic| (first | ipureintro | exfalso) <;> (first | simp [*] | assumption) <;> done)
