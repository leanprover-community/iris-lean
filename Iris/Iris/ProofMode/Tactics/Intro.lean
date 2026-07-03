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

/--
  Used by `iIntroCore` for the cases `.intro (.pure …)`, `.intro (.rewrite …)`,
  `.all` and `.allwand`.

  The function `k'` is the fallback option when type class synthesis with `Q`
  using `FromForall` fails. The fallback option is applicable only for
  `.all` and `.allwand`.
-/
private def iIntroCoreForallIntro {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {P : Q($prop)} (ref : Syntax) (n : Option <| TSyntax ``binderIdent)
    (Q : Q($prop)) (tacName : String) (k' : Option <| ProofModeM Q($P ⊢ $Q))
    (k : Q($prop) → (B : Q($prop)) → ProofModeM Q($P ⊢ $B)) :
    ProofModeM Q($P ⊢ $Q) := do
  let ⟨n, _⟩ ← getFreshName <| n.getD (← `(binderIdent| _))
  let v ← mkFreshLevelMVar
  let α ← mkFreshExprMVarQ q(Sort v)
  let Φ ← mkFreshExprMVarQ q($α → $prop)
  match ← ProofModeM.trySynthInstanceQ q(FromForall $Q $Φ), k' with
  | none, none =>
    throwError "{tacName}: {Q} cannot be turned into a universal quantifier or pure hypothesis"
  | none, some k' => k'
  | some _, _ =>
    withLocalDeclDQ n α fun x => do
      addLocalVarInfo ref (← getLCtx) x α
      have B : Q($prop) := Expr.headBeta q($Φ $x)
      let pf : Q(∀ x, $P ⊢ $Φ x) ← mkLambdaFVars #[x] <|← k x B
      return q(from_forall_intro $pf)

/--
Introduce the hypothesis specified by `pats` into the context given by `P` (structured  as `hyps`).
The type of the current goal is given by `Q`.

This function returns the proof of `P ⊢ Q` to be assigned. The new context is included in the
`goals` directly by the tactic.
-/
partial def iIntroCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
  {P} (hyps : Hyps bi P) (Q : Q($prop)) (pats : List (Syntax × IntroPat)) (tacName : String)
  (k : ∀ {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}, Hyps bi e → (goal: Q($prop)) → ProofModeM Q($e ⊢ $goal) := addBIGoal) :
    ProofModeM (Q($P ⊢ $Q)) := do
  match pats with
  | [] => k hyps Q
  | (ref, pat) :: pats =>
    withRef ref do match pat with
    | .modintro =>
      iModIntroCore hyps Q (← `(_)) tacName (iIntroCore · · pats tacName k)
    | .trivial =>
      if let some r ← iTrivial hyps Q then
        return r
      else
        iIntroCore hyps Q pats tacName k
    | .simp =>
      let simpCtx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
      let ⟨Q', _⟩ ← Lean.Meta.dsimp Q simpCtx #[← Simp.getSimprocs]
      iIntroCore hyps Q' pats tacName k
    | .simptrivial =>
      iIntroCore hyps Q ((ref, .simp) :: (ref, .trivial) :: pats) tacName k
    | .all =>
      iIntroCoreForallIntro ref none Q tacName
        -- No more universally quantified variable to be introduced
        (iIntroCore hyps Q pats tacName k)
        -- Introduction of a universally quantified variable
        (fun _ B => iIntroCore hyps B ((ref, .all) :: pats) tacName k)
    | .allwand =>
      let k' : ProofModeM Q($P ⊢ $Q) := do
        let A1 ← mkFreshExprMVarQ q($prop)
        let A2 ← mkFreshExprMVarQ q($prop)
        let instFromImp ← ProofModeM.trySynthInstanceQ q(FromImp $Q $A1 $A2)
        let instFromWand ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
        let instPersistent ← ProofModeM.trySynthInstanceQ q(TCOr (Persistent $A1) (Intuitionistic $P))
        match instFromWand, instFromImp, instPersistent with
        -- Introduction of a wand premise or a pure premise, if possible
        | some _, _, _ | _, some _, some _ =>
          iIntroCore hyps Q ((ref, .intro (.one ref (← `(binderIdent| _)))) :: (ref, .allwand) :: pats) tacName k
        | _, _, _ =>
          -- No more universally quantified variable or premise to be introduced
          iIntroCore hyps Q pats tacName k
      -- Introduction of a universally quantified variable
      iIntroCoreForallIntro ref none Q tacName k'
        (fun _ B => iIntroCore hyps B ((ref, .allwand) :: pats) tacName k)
    | .pureintro =>
      let ⟨pf, m⟩ ← iPureIntroCore bi P Q tacName
      if pats.isEmpty then
        addMVarGoal m
      else
        let ⟨newM, g⟩ ← startProofMode m
        let pf' ← newM.withContext <| iIntroCore g.hyps g.goal pats tacName k
        newM.assign pf'
      return pf
    | .clear selPats =>
      match selPats with
      | [] => iIntroCore hyps Q pats tacName k
      | ⟨false, s⟩ :: selPats =>
        iClearCore hyps Q [s]
          fun hyps' goal' fvars => withoutFVars (u := 0) fvars
            <| iIntroCore hyps' goal' ((ref, .clear selPats) :: pats) tacName k
      | ⟨true, s⟩ :: selPats =>
        let res ← s.resolveOne hyps >>= iFrame hyps Q
        res.finish (iIntroCore · · ((ref, .clear selPats) :: pats) tacName k)
    | .intro (.rewrite _ direction) =>
      iIntroCoreForallIntro ref none Q tacName none <|
        fun x B => iPureRewriteCoreAux hyps B x direction tacName (iIntroCore · · pats tacName k)
    | .intro (.pure _ pat) =>
      let v ← mkFreshLevelMVar
      let α ← mkFreshExprMVarQ q(Sort v)
      let Φ ← mkFreshExprMVarQ q($α → $prop)
      let .some _ ← ProofModeM.trySynthInstanceQ q(FromForall $Q $Φ)
      | throwError "{tacName}: {Q} cannot be turned into a universal quantifier or pure hypothesis"
      let pf : Q(∀ x, $P ⊢ $Φ x) ← iPureDestruct q(∀ x, $P ⊢ $Φ x) pat fun g => do
        let B : Q($prop) ← mkFreshExprMVarQ q($prop)
        let eq ← isDefEq (← g.getType) q($P ⊢ $B)
        if !eq then throwError "{tacName}: internal error: unexpected goal after intro pattern"
        iIntroCore hyps (Expr.headBeta (← instantiateMVars B)) pats tacName k
      return q(from_forall_intro (Q := $Q) $pf)
    | .intro pat =>
      let A1 ← mkFreshExprMVarQ q($prop)
      let A2 ← mkFreshExprMVarQ q($prop)
      let fromImp ← ProofModeM.trySynthInstanceQ q(FromImp $Q $A1 $A2)
      if let (.clear _, some _) := (pat, fromImp) then
        let pf ← iIntroCore hyps A2 pats tacName k
        return q(imp_intro_drop (Q := $Q) $pf)
      else
      let B ← mkFreshExprMVarQ q($prop)
      match pat, fromImp with
      | .intuitionistic _ pat, some _ =>
        let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently false $A1 $B)
          | throwError "{tacName}: {A1} not persistent"
        let pf ← iCasesCore hyps A2 pat q(true) B tacName (iIntroCore · · pats tacName k)
        return q(imp_intro_intuitionistic (Q := $Q) $pf)
      | .intuitionistic _ pat, none =>
        let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
          | throwError "{tacName}: {Q} not a wand"
        let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently false $A1 $B)
          | throwError "{tacName}: {A1} not persistent"
        let .some _ ← trySynthInstanceQ q(TCOr (Affine $A1) (Absorbing $A2))
          | throwError "{tacName}: {A1} not affine and the goal not absorbing"
        let pf ← iCasesCore hyps A2 pat q(true) B tacName (iIntroCore · · pats tacName k)
        return q(wand_intro_intuitionistic (A1 := $A1) (Q := $Q) $pf)
      | _, some _ =>
        -- should always succeed
        let _ ← ProofModeM.synthInstanceQ q(FromAffinely $B $A1)
        let .some _ ← trySynthInstanceQ q(TCOr (Persistent $A1) (Intuitionistic $P))
          | throwError "{tacName}: {A1} is not persistent and spatial context is non-empty"
        let pf ← iCasesCore hyps A2 pat q(false) B tacName (iIntroCore · · pats tacName k)
        return q(imp_intro_spatial (Q := $Q) $pf)
      | _, none =>
        let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
          | throwError "{tacName}: {Q} not a wand"
        let pf ← iCasesCore hyps A2 pat q(false) A1 tacName (iIntroCore · · pats tacName k)
        return q(wand_intro_spatial (A1 := $A1) (Q := $Q) $pf)

/--
  `iintro pats` introduces hypotheses using the introduction pattern `pats`.
-/
elab "iintro " pats:(colGt ppSpace introPat)* : tactic => do
  -- parse syntax
  let pats ← liftMacroM <| pats.mapM <| IntroPat.parse

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let pf ← iIntroCore hyps goal pats.toList "iintro"

  mvar.assign pf
