/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Patterns.IntroPattern
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.Pure
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

private def iIntroCoreForallIntro {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {P} (hyps : Hyps bi P) (ref : Syntax) (n : Name) (Q : Q($prop))
    (k : Expr → Q($prop) → ProofModeM Expr):
    ProofModeM Q($P ⊢ $Q) := do
  withRef ref do
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVarQ q(Sort v)
    let Φ ← mkFreshExprMVarQ q($α → $prop)
    let .some _ ← ProofModeM.trySynthInstanceQ q(FromForall $Q $Φ)
      | throwError "iintro: {Q} cannot be turned into a universal quantifier or pure hypothesis"
    withLocalDeclDQ n α fun x => do
      addLocalVarInfo ref (← getLCtx) x α
      have B : Q($prop) := Expr.headBeta q($Φ $x)
      have : $B =Q $Φ $x := ⟨⟩
      let pf : Q(∀ x, $P ⊢ $Φ x) ← k x B
      return q(from_forall_intro (Q := $Q) $pf)

set_option maxHeartbeats 250000 in
/--
Introduce the hypothesis specified by `pats` into the context given by `P` (structured  as `hyps`).
The type of the current goal is given by `Q`.

This function returns the proof of `P ⊢ Q` to be assigned. The new context is included in the
`goals` directly by the tactic.
-/
partial def iIntroCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
  {P} (hyps : Hyps bi P) (Q : Q($prop)) (pats : List (Syntax × IntroPat))
  (k : ∀ {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}, Hyps bi e → (goal: Q($prop)) → ProofModeM Q($e ⊢ $goal) := addBIGoal) :
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
        let pf : Q(∀ x, $P ⊢ $Φ x) ←
          mkLambdaFVars #[x] <|← iIntroCore hyps B ((ref, .all) :: pats) k
        return q(from_forall_intro (Q := $Q) $pf)
  | (ref, .allwand) :: pats =>
    withRef ref do
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVarQ q(Sort v)
    let Φ ← mkFreshExprMVarQ q($α → $prop)
    match ← ProofModeM.trySynthInstanceQ q(FromForall $Q $Φ) with
    -- Introduction of a universally quantified variable
    | some _ =>
      let (n, ref') ← getFreshName (← `(binderIdent| _))
      withLocalDeclDQ n α fun x => do
        addLocalVarInfo ref' (← getLCtx) x α
        have B : Q($prop) := Expr.headBeta q($Φ $x)
        have : $B =Q $Φ $x := ⟨⟩
        let pf : Q(∀ x, $P ⊢ $Φ x) ←
          mkLambdaFVars #[x] <|← iIntroCore hyps B ((ref, .allwand) :: pats) k
        return q(from_forall_intro (Q := $Q) $pf)
    -- Introduction of a wand premise or an implication premise, if possible
    | none =>
      let A1 ← mkFreshExprMVarQ q($prop)
      let A2 ← mkFreshExprMVarQ q($prop)
      let instFromImp ← ProofModeM.trySynthInstanceQ q(FromImp $Q $A1 $A2)
      let instFromWand ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
      let instPersistent ← ProofModeM.trySynthInstanceQ q(TCOr (Persistent $A1) (Intuitionistic $P))
      match instFromWand, instFromImp, instPersistent with
      | some _, _, _ | _, some _, some _ =>
        iIntroCore hyps Q ((ref, .intro (.one (← `(binderIdent| _)))) :: (ref, .allwand) :: pats) k
      | _, _, _ =>
        iIntroCore hyps Q pats k
  | (ref, .pureintro) :: pats =>
    withRef ref do
    let b ← mkFreshExprMVarQ q(Bool)
    let ϕ ← mkFreshExprMVarQ q(Prop)
    let some inst ← ProofModeM.trySynthInstanceQ q(FromPure $b $Q .out $ϕ)
    | throwError "iintro: {Q} is not a pure"
    let m : Q($ϕ) ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars ϕ)
    let pf ← do match ← whnf b with
    | .const ``true _ =>
      have : $b =Q true := ⟨⟩
      let .some _ ← trySynthInstanceQ q(Affine $P)
      | throwError "iintro: unable to introduce a pure goal as the context is not affine"
      pure q(pure_intro_affine (Q := $Q) $inst $m)
    | .const ``false _ =>
      have : $b =Q false := ⟨⟩
      pure q(pure_intro_spatial (Q := $Q) $inst $m)
    | _ => throwError "iintro: bug in typeclass instances, cannot reduce {b} to true or false"
    if pats.isEmpty then
      addMVarGoal m.mvarId!
    else
      let ⟨newM, g⟩ ← startProofMode m.mvarId!
      let pf' ← newM.withContext <| iIntroCore g.hyps g.goal pats k
      newM.assign pf'
    return pf
  | (ref, .clear selPats) :: pats =>
    withRef ref do
    match selPats with
    | [] => iIntroCore hyps Q pats k
    | ⟨false, s⟩ :: selPats =>
      iClearCore hyps Q [s]
        fun hyps' goal' fvars => withoutFVars (u := 0) fvars
          <| iIntroCore hyps' goal' ((ref, .clear selPats) :: pats) k
    | ⟨true, s⟩ :: selPats =>
      let res ← s.resolveOne hyps >>= iFrame hyps Q
      res.finish (iIntroCore · · ((ref, .clear selPats) :: pats) k)
  | (ref, .intro (.rewrite direction)) :: pats =>
    let (n, ref) ← getFreshName (← `(binderIdent| _))
    iIntroCoreForallIntro hyps ref n Q <|
      fun x B => do mkLambdaFVars #[x] <|← iCasesPureRewrite hyps B x direction (iIntroCore · · pats k)
  | (ref, .intro (.pure n)) :: pats =>
    let (n, ref) ← getFreshName n
    iIntroCoreForallIntro hyps ref n Q <|
      fun x B => do mkLambdaFVars #[x] <|← iIntroCore hyps B pats k
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
