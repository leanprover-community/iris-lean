/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Patterns.IntroPattern
import Iris.ProofMode.Tactics.Cases
import Iris.ProofMode.Tactics.ModIntro

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

private theorem imp_intro_drop [BI PROP] {P Q A1 A2 : PROP} [inst : FromImp Q A1 A2] (h : P ⊢ A2) : P ⊢ Q :=
  BI.imp_intro (and_elim_l' h) |>.trans inst.1

private theorem from_forall_intro [BI PROP] {P Q : PROP} {Φ : α → PROP} [inst : FromForall Q Φ]
    (h : ∀ a, P ⊢ Φ a) : P ⊢ Q :=
  (forall_intro h).trans inst.1

private theorem imp_intro_intuitionistic [BI PROP] {P Q A1 A2 B : PROP}
    [FromImp Q A1 A2] [inst : IntoPersistently false A1 B] (h : P ∗ □ B ⊢ A2) : P ⊢ Q := by
  refine BI.imp_intro ?_ |>.trans from_imp
  exact (and_mono_r inst.1).trans <| persistently_and_intuitionistically_sep_r.1.trans h

private theorem wand_intro_intuitionistic [BI PROP] {P Q A1 A2 B : PROP}
    [FromWand Q A1 A2] [inst : IntoPersistently false A1 B] [or : TCOr (Affine A1) (Absorbing A2)]
    (h : P ∗ □ B ⊢ A2) : P ⊢ Q := by
  refine (wand_intro ?_).trans from_wand
  exact match or with
  | TCOr.l => (sep_mono_r <| (affine_affinely A1).2.trans (affinely_mono inst.1)).trans h
  | TCOr.r => (sep_mono_r <| inst.1.trans absorbingly_intuitionistically.2).trans <|
      absorbingly_sep_r.1.trans <| (absorbingly_mono h).trans absorbing

private theorem imp_intro_spatial [BI PROP] {P Q A1 A2 B : PROP}
    [FromImp Q A1 A2] [inst : FromAffinely B A1] [or : TCOr (Persistent A1) (Intuitionistic P)]
    (h : P ∗ B ⊢ A2) : P ⊢ Q := by
  refine (BI.imp_intro ?_).trans from_imp
  refine Entails.trans ?_ <| (sep_mono_r inst.1).trans h
  exact match or with
  | TCOr.l => persistent_and_affinely_sep_r_1
  | TCOr.r (u := u) =>
    (and_mono_l u.1).trans <| affinely_and_lr.1.trans <|
    persistently_and_intuitionistically_sep_l.1.trans <| sep_mono_l intuitionistically_elim

private theorem wand_intro_spatial [BI PROP] {P Q A1 A2 : PROP}
    [FromWand Q A1 A2] (h : P ∗ A1 ⊢ A2) : P ⊢ Q := (wand_intro h).trans from_wand

partial def iIntroCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {P} (hyps : Hyps bi P) (Q : Q($prop)) (pats : List (Syntax × IntroPat)) :
    ProofModeM (Q($P ⊢ $Q)) := do
  match pats with
  | [] => addBIGoal hyps Q
  | (ref, .modintro) :: pats =>
    withRef ref do
    iModIntroCore hyps Q (← `(_)) (iIntroCore · · pats)
  | (ref, .intro (.pure n)) :: pats =>
    withRef ref do
    let v ← mkFreshLevelMVar
    let α : Quoted q(Sort v) ← mkFreshExprMVarQ q(Sort v)
    let Φ : Quoted q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    let .some _ ← ProofModeM.trySynthInstanceQ q(FromForall $Q $Φ)
      | throwError "iintro: {Q} cannot be turned into a universal quantifier or pure hypothesis"
    let (n, ref) ← getFreshName n
    withLocalDeclDQ n α fun x => do
      addLocalVarInfo ref (← getLCtx) x α
      have B : Q($prop) := Expr.headBeta q($Φ $x)
      have : $B =Q $Φ $x := ⟨⟩
      let pf : Q(∀ x, $P ⊢ $Φ x) ← mkLambdaFVars #[x] <|← iIntroCore hyps B pats
      return q(from_forall_intro (Q := $Q) $pf)
  | (ref, .intro pat) :: pats =>
    withRef ref do
    let A1 ← mkFreshExprMVarQ q($prop)
    let A2 ← mkFreshExprMVarQ q($prop)
    let fromImp ← ProofModeM.trySynthInstanceQ q(FromImp $Q $A1 $A2)
    if let (.clear, some _) := (pat, fromImp) then
      let pf ← iIntroCore hyps A2 pats
      return q(imp_intro_drop (Q := $Q) $pf)
    else
    let B ← mkFreshExprMVarQ q($prop)
    match pat, fromImp with
    | .intuitionistic pat, some _ =>
      let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently false $A1 $B)
        | throwError "iintro: {A1} not persistent"
      let pf ← iCasesCore bi hyps A2 q(true) q(iprop(□ $B)) B ⟨⟩ pat (iIntroCore · A2 pats)
      return q(imp_intro_intuitionistic (Q := $Q) $pf)
    | .intuitionistic pat, none =>
      let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $Q $A1 $A2)
        | throwError "iintro: {Q} not a wand"
      let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently false $A1 $B)
        | throwError "iintro: {A1} not persistent"
      let .some _ ← trySynthInstanceQ q(TCOr (Affine $A1) (Absorbing $A2))
        | throwError "iintro: {A1} not affine and the goal not absorbing"
      let pf ← iCasesCore bi hyps A2 q(true) q(iprop(□ $B)) B ⟨⟩ pat (iIntroCore · A2 pats)
      return q(wand_intro_intuitionistic (Q := $Q) $pf)
    | _, some _ =>
      -- should always succeed
      let _ ← ProofModeM.synthInstanceQ q(FromAffinely $B $A1)
      let .some _ ← trySynthInstanceQ q(TCOr (Persistent $A1) (Intuitionistic $P))
        | throwError "iintro: {A1} is not persistent and spatial context is non-empty"
      let pf ← iCasesCore bi hyps A2 q(false) B B ⟨⟩ pat (iIntroCore · A2 pats)
      return q(imp_intro_spatial (Q := $Q) $pf)
    | _, none =>
      let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $Q $A1 $A2)
        | throwError "iintro: {Q} not a wand"
      let pf ← iCasesCore bi hyps A2 q(false) A1 A1 ⟨⟩ pat (iIntroCore · A2 pats)
      return q(wand_intro_spatial (Q := $Q) $pf)


elab "iintro" pats:(colGt introPat)* : tactic => do
  -- parse syntax
  let pats ← liftMacroM <| pats.mapM <| IntroPat.parse

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let pf ← iIntroCore hyps goal pats.toList

  mvar.assign pf
