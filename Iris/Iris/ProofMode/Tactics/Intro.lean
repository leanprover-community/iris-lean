/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Patterns.IntroPattern
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.ModIntro
public meta import Iris.ProofMode.Tactics.Trivial

namespace Iris.ProofMode

public section
open BI Std

theorem imp_intro_drop [BI PROP] {P Q A1 A2 : PROP} [inst : FromImp Q A1 A2] (h : P ⊢ A2) : P ⊢ Q :=
  BI.imp_intro (and_elim_left_trans h) |>.trans inst.1

theorem from_forall_intro [BI PROP] {P Q : PROP} {Φ : α → PROP} [inst : FromForall Q Φ]
    (h : ∀ a, P ⊢ Φ a) : P ⊢ Q :=
  (forall_intro h).trans inst.1

theorem imp_intro_intuitionistic [BI PROP] {P Q A1 A2 B : PROP}
    [FromImp Q A1 A2] [inst : IntoPersistently false A1 B] (h : P ∗ □ B ⊢ A2) : P ⊢ Q := by
  refine BI.imp_intro ?_ |>.trans from_imp
  exact (and_mono_right inst.1).trans <| persistently_and_intuitionistically_sep_right.1.trans h

theorem wand_intro_intuitionistic [BI PROP] {P Q A1 A2 B : PROP}
    [FromWand Q .out A1 A2] [inst : IntoPersistently false A1 B] [or : TCOr (Affine A1) (Absorbing A2)]
    (h : P ∗ □ B ⊢ A2) : P ⊢ Q := by
  refine (wand_intro ?_).trans (from_wand .out (Q1:=A1))
  exact match or with
  | TCOr.l => (sep_mono_right <| (affine_affinely A1).2.trans (affinely_mono inst.1)).trans h
  | TCOr.r => (sep_mono_right <| inst.1.trans absorbingly_intuitionistically.2).trans <|
      absorbingly_sep_right.1.trans <| (absorbingly_mono h).trans absorbing

theorem imp_intro_spatial [BI PROP] {P Q A1 A2 B : PROP}
    [FromImp Q A1 A2] [inst : FromAffinely B A1] [or : TCOr (Persistent A1) (Intuitionistic P)]
    (h : P ∗ B ⊢ A2) : P ⊢ Q := by
  refine (BI.imp_intro ?_).trans from_imp
  refine Entails.trans ?_ <| (sep_mono_right inst.1).trans h
  exact match or with
  | TCOr.l => persistent_and_affinely_sep_right_mp
  | TCOr.r (u := u) =>
    (and_mono_left u.1).trans <| affinely_and_left_right.1.trans <|
    persistently_and_intuitionistically_sep_left.1.trans <| sep_mono_left intuitionistically_elim

theorem wand_intro_spatial [BI PROP] {P Q A1 A2 : PROP}
    [FromWand Q .out A1 A2] (h : P ∗ A1 ⊢ A2) : P ⊢ Q := (wand_intro h).trans (from_wand .out (Q1:=A1))

public meta section
open Lean Elab Tactic Meta Qq BI Std

/--
Introduce the hypothesis specified by `pats` into the context given by `P` (structured  as `hyps`).
The type of the current goal is given by `Q`.

This function returns the proof of `P ⊢ Q` to be assigned. The new context is included in the
`goals` directly by the tactic.
-/
partial def iIntroCore {prop : Q(Type u)} {bi : Q(BI $prop)}
  {P} (hyps : Hyps bi P) (Q : Q($prop)) (pats : List (Syntax × IntroPat))
  (k : ∀ {prop : Q(Type $u)} {bi : Q(BI $prop)} {e : Q($prop)}, Hyps bi e → (goal: Q($prop)) → ProofModeM Q($e ⊢ $goal) := addBIGoal) :
    ProofModeM (Q($P ⊢ $Q)) := do
  match pats with
  | [] => k hyps Q
  | (ref, .modintro) :: pats =>
    withRef ref do
    iModIntroCore hyps Q (← `(_)) (iIntroCore · · pats k)
  | (ref, .trivial) :: pats =>
    withRef ref do
    if let some r ← iTrivial hyps Q then
      return r
    else
      iIntroCore hyps Q pats k
  | (ref, .simp) :: pats =>
    withRef ref do
    let simpCtx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
    let ⟨Q', _⟩ ← Lean.Meta.dsimp Q simpCtx #[← Simp.getSimprocs]
    iIntroCore hyps Q' pats k
  | (ref, .simptrivial) :: pats =>
    iIntroCore hyps Q ((ref, .simp) :: (ref, .trivial) :: pats) k
  | (ref, .all) :: pats =>
    withRef ref do
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVarQ q(Sort v)
    let Φ ← mkFreshExprMVarQ q($α → $prop)
    match ← ProofModeM.trySynthInstanceQ q(FromForall $Q $Φ) with
    | none =>
      iIntroCore hyps Q pats k
    | some _ =>
      let (n, ref') ← getFreshName (← `(binderIdent| _))
      withLocalDeclDQ n α fun x => do
        addLocalVarInfo ref' (← getLCtx) x α
        have B : Q($prop) := Expr.headBeta q($Φ $x)
        have : $B =Q $Φ $x := ⟨⟩
        let pf : Q(∀ x, $P ⊢ $Φ x) ← mkLambdaFVars #[x] <| ← iIntroCore hyps q($Φ $x) ((ref, .all) :: pats) k
        return q(from_forall_intro (Q := $Q) $pf)
  | (ref, .intro (.pure n)) :: pats =>
    withRef ref do
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVarQ q(Sort v)
    let Φ ← mkFreshExprMVarQ q($α → $prop)
    let .some _ ← ProofModeM.trySynthInstanceQ q(FromForall $Q $Φ)
      | throwError "iintro: {Q} cannot be turned into a universal quantifier or pure hypothesis"
    let (n, ref) ← getFreshName n
    withLocalDeclDQ n α fun x => do
      addLocalVarInfo ref (← getLCtx) x α
      have B : Q($prop) := Expr.headBeta q($Φ $x)
      have : $B =Q $Φ $x := ⟨⟩
      let pf : Q(∀ x, $P ⊢ $Φ x) ← mkLambdaFVars #[x] <|← iIntroCore hyps B pats k
      return q(from_forall_intro (Q := $Q) $pf)
  | (ref, .intro pat) :: pats =>
    withRef ref do
    let A1 ← mkFreshExprMVarQ q($prop)
    let A2 ← mkFreshExprMVarQ q($prop)
    let fromImp ← ProofModeM.trySynthInstanceQ q(FromImp $Q $A1 $A2)
    if let (.clear, some _) := (pat, fromImp) then
      let pf ← iIntroCore hyps A2 pats k
      return q(imp_intro_drop (Q := $Q) $pf)
    else
    let B ← mkFreshExprMVarQ q($prop)
    match pat, fromImp with
    | .intuitionistic pat, some _ =>
      let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently false $A1 $B)
        | throwError "iintro: {A1} not persistent"
      let pf ← iCasesCore hyps A2 pat q(true) B (iIntroCore · · pats k)
      return q(imp_intro_intuitionistic (Q := $Q) $pf)
    | .intuitionistic pat, none =>
      let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
        | throwError "iintro: {Q} not a wand"
      let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently false $A1 $B)
        | throwError "iintro: {A1} not persistent"
      let .some _ ← trySynthInstanceQ q(TCOr (Affine $A1) (Absorbing $A2))
        | throwError "iintro: {A1} not affine and the goal not absorbing"
      let pf ← iCasesCore hyps A2 pat q(true) B (iIntroCore · · pats k)
      return q(wand_intro_intuitionistic (A1 := $A1) (Q := $Q) $pf)
    | _, some _ =>
      -- should always succeed
      let _ ← ProofModeM.synthInstanceQ q(FromAffinely $B $A1)
      let .some _ ← trySynthInstanceQ q(TCOr (Persistent $A1) (Intuitionistic $P))
        | throwError "iintro: {A1} is not persistent and spatial context is non-empty"
      let pf ← iCasesCore hyps A2 pat q(false) B (iIntroCore · · pats k)
      return q(imp_intro_spatial (Q := $Q) $pf)
    | _, none =>
      let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
        | throwError "iintro: {Q} not a wand"
      let pf ← iCasesCore hyps A2 pat q(false) A1 (iIntroCore · · pats k)
      return q(wand_intro_spatial (A1 := $A1) (Q := $Q) $pf)

/--
  `iintro pats` introduces hypotheses using the introduction pattern `pats`.
-/
elab "iintro " pats:(colGt ppSpace introPat)* : tactic => do
  -- parse syntax
  let pats ← liftMacroM <| pats.mapM <| IntroPat.parse

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let pf ← iIntroCore hyps goal pats.toList

  mvar.assign pf
