/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Patterns.IntroPattern
public import Iris.ProofMode.Tactics.Cases
public import Iris.ProofMode.Tactics.Pure
public import Iris.ProofMode.Tactics.ModIntro
public import Iris.ProofMode.Tactics.Trivial

namespace Iris.ProofMode

public section
open BI Std

@[rocq_alias tac_impl_intro_drop]
theorem imp_intro_drop [BI PROP] {P Q A1 A2 : PROP}
    [inst : FromImp Q A1 A2] (h : P ⊢ A2) : P ⊢ Q :=
  BI.imp_intro (and_elim_left_trans h) |>.trans inst.1

@[rocq_alias tac_forall_intro]
theorem from_forall_intro [BI PROP] {P Q : PROP} {Φ : α → PROP} [inst : FromForall Q Φ]
    (h : ∀ a, P ⊢ Φ a) : P ⊢ Q :=
  (forall_intro h).trans inst.1

@[rocq_alias tac_impl_intro_intuitionistic]
theorem imp_intro_intuitionistic [BI PROP] {P Q A1 A2 B : PROP}
    [FromImp Q A1 A2] [inst : IntoPersistently false A1 B] (h : P ∗ □ B ⊢ A2) : P ⊢ Q := by
  refine BI.imp_intro ?_ |>.trans from_imp
  calc
    _ ⊢ P ∧ <pers> B := and_mono_right inst.1
    _ ⊢ P ∗ □ B      := persistently_and_intuitionistically_sep_right.1
    _ ⊢ A2           := h

@[rocq_alias tac_wand_intro_intuitionistic]
theorem wand_intro_intuitionistic [BI PROP] {P Q A1 A2 B : PROP}
    [instFromWand : FromWand Q .out A1 A2]
    [inst : IntoPersistently false A1 B] [or : TCOr (Affine A1) (Absorbing A2)]
    (h : P ∗ □ B ⊢ A2) : P ⊢ Q := by
  refine (wand_intro ?_).trans instFromWand.from_wand
  match or with
  | TCOr.l =>
    exact (sep_mono_right <| (affine_affinely A1).2.trans (affinely_mono inst.1)).trans h
  | TCOr.r =>
    calc
      _ ⊢ P ∗ <absorb> □ B   := sep_mono_right <| inst.1.trans absorbingly_intuitionistically.2
      _ ⊢ <absorb> (P ∗ □ B) := absorbingly_sep_right.1
      _ ⊢ <absorb> A2        := absorbingly_mono h
      _ ⊢ A2                 := absorbing

@[rocq_alias tac_impl_intro]
theorem imp_intro_spatial [BI PROP] {P Q A1 A2 B : PROP}
    [FromImp Q A1 A2] [inst : FromAffinely B A1] [or : TCOr (Persistent A1) (Intuitionistic P)]
    (h : P ∗ B ⊢ A2) : P ⊢ Q := by
  refine (BI.imp_intro ?_).trans from_imp
  refine Entails.trans ?_ <| (sep_mono_right inst.1).trans h
  exact match or with
  | TCOr.l => persistent_and_affinely_sep_right_mp
  | TCOr.r (u := u) =>
    calc
      _ ⊢ □ P ∧ A1               := and_mono_left u.1
      _ ⊢ <pers> P ∧ <affine> A1 := affinely_and_left_right.1
      _ ⊢ □ P ∗ <affine> A1      := persistently_and_intuitionistically_sep_left.1
      _ ⊢ P ∗ <affine> A1        := sep_mono_left intuitionistically_elim

@[rocq_alias tac_wand_intro]
theorem wand_intro_spatial [BI PROP] {P Q A1 A2 : PROP}
    [inst : FromWand Q .out A1 A2] (h : P ∗ A1 ⊢ A2) : P ⊢ Q :=
  (wand_intro h).trans inst.from_wand

#rocq_ignore tac_wand_intro_drop
  "Functionality shared with the case destruction pattern for clearing"

public meta section
open Lean Elab Tactic Meta Qq BI Std

/--
  Used by `iIntroCore` for the pure and quantifier cases.

  The function `k'` is the fallback option when type class synthesis with `Q`
  using `FromForall` fails. The fallback option is applicable only for
  `.all` and `.allwand`.
-/
private def iIntroCoreForallIntro {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {P : Q($prop)} (hyps : Hyps bi P) (pat : TSyntax `rcasesPat)
    (Q : Q($prop)) (k' : Option <| ProofModeM Q($P ⊢ $Q))
    (k : MVarId → ∀ {P' : Q($prop)}, Hyps bi P' → (B : Q($prop)) → ProofModeM Q($P' ⊢ $B)) :
    ProofModeM Q($P ⊢ $Q) := do
  let v ← mkFreshLevelMVar
  let α ← mkFreshExprMVarQ q(Sort v)
  let Φ ← mkFreshExprMVarQ q($α → $prop)
  match ← ProofModeM.trySynthInstanceQ q(FromForall $Q $Φ), k' with
  | none, none =>
    throwIPMError "{Q} cannot be turned into a universal quantifier or pure hypothesis"
  | none, some k' => k'
  | some _, _ =>
    let pf : Q(∀ x, $hyps.tm ⊢ $Φ x) ← iPureCases q(∀ x, $hyps.tm ⊢ $Φ x) pat fun g => do
      let some ⟨_, _, tm', B⟩ := parseEntails? (← instantiateMVars (← g.getType))
        | throwIPMError "unexpected goal {← g.getType} after intro pattern"
      let some ⟨_, hyps'⟩ := parseHyps? bi tm'
        | throwIPMError "unable to parse the Iris context {tm'}"
      return (← k g hyps' (Expr.headBeta B) : Expr)
    have : $hyps.tm =Q $P := ⟨⟩
    return q(from_forall_intro (Q := $Q) $pf)

/-- Return `true` if there is a premise to introduce using `.allwand` (`**`). -/
private def iIntroCoreAllWandCheck {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (P Q : Q($prop)) : ProofModeM Bool := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  -- Check whether a wand premise can be introduced
  let instFromWand ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
  if instFromWand.isSome then return true

  -- Check whether a pure premise can be introduced
  let instFromImp ← ProofModeM.trySynthInstanceQ q(FromImp $Q $A1 $A2)
  if instFromImp.isNone then return false
  let instPersistent ← ProofModeM.trySynthInstanceQ q(TCOr (Persistent $A1) (Intuitionistic $P))
  return instPersistent.isSome

/--
Introduce the hypothesis specified by `pats` into the context given by `P` (structured as `hyps`).
The type of the current goal is given by `Q`.

This function returns the proof of `P ⊢ Q` to be assigned. The new context is included in the
`goals` directly by the tactic.
-/
partial def iIntroCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {P} (hyps : Hyps bi P) (Q : Q($prop)) (pats : List (Syntax × IntroPat))
    (k : ∀ {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)},
      Hyps bi e → (goal: Q($prop)) → ProofModeM Q($e ⊢ $goal) := addBIGoal) :
    ProofModeM (Q($P ⊢ $Q)) := do
  match pats with
  | [] => k hyps Q
  | (ref, pat) :: pats =>
    withRef ref do match pat with
    | .modintro =>
      iModIntroCore hyps Q (← `(_)) (iIntroCore · · pats k)
    | .trivial =>
      if let some r ← iTrivial hyps Q then
        return r
      else
        iIntroCore hyps Q pats k
    | .simp =>
      let simpCtx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
      let ⟨res, _⟩ ← Lean.Meta.simp Q simpCtx #[← Simp.getSimprocs]
      have Q' : Q($prop) := res.expr
      let h : Q($Q = $Q') ← res.getProof
      let pf ← iIntroCore hyps Q' pats k
      return q($h ▸ $pf)
    | .simptrivial =>
      iIntroCore hyps Q ((ref, .simp) :: (ref, .trivial) :: pats) k
    | .all =>
      iIntroCoreForallIntro hyps (← `(rcasesPat| _)) Q
        -- No more universally quantified variable to be introduced
        (iIntroCore hyps Q pats k)
        -- Introduction of a universally quantified variable
        (fun _ _ hyps' B => iIntroCore hyps' B ((ref, .all) :: pats) k)
    | .allwand =>
      -- Introduction of a universally quantified variable
      iIntroCoreForallIntro hyps (← `(rcasesPat| _)) Q
        (some (do
          -- Introduction of a wand premise or a pure premise, if possible
          if ← iIntroCoreAllWandCheck (bi := bi) P Q then
            iIntroCore hyps Q ((ref, .intro ⟨ref, (.one (← `(binderIdent| _)))⟩) ::
              (ref, .allwand) :: pats) k
          -- No more universally quantified variable or premise to be introduced
          else iIntroCore hyps Q pats k))
        (fun _ _ hyps' B => iIntroCore hyps' B ((ref, .allwand) :: pats) k)
    | .pureintro =>
      let ⟨pf, m⟩ ← iPureIntroCore bi P Q
      if pats.isEmpty then
        addMVarGoal m
      else
        let ⟨newM, g⟩ ← startProofMode m
        let pf' ← newM.withContext <| iIntroCore g.hyps g.goal pats k
        newM.assign pf'
      return pf
    | .clear selPats =>
      match selPats with
      | [] => iIntroCore hyps Q pats k
      | ⟨false, s⟩ :: selPats =>
        iClearCore hyps Q [s]
          fun hyps' goal' fvars => withoutFVars (u := 0) fvars
            <| iIntroCore hyps' goal' ((ref, .clear selPats) :: pats) k
      | ⟨true, s⟩ :: selPats =>
        let res ← s.resolveOne hyps .bottomToTop >>= iFrame hyps Q
        res.finish (iIntroCore · · ((ref, .clear selPats) :: pats) k)
    | .intro ⟨_, .pure pat⟩ =>
      iIntroCoreForallIntro hyps pat Q none fun _ _ hyps' B =>
        iIntroCore hyps' B pats k
    | .intro pat =>
      let A1 ← mkFreshExprMVarQ q($prop)
      let A2 ← mkFreshExprMVarQ q($prop)
      let fromImp ← ProofModeM.trySynthInstanceQ q(FromImp $Q $A1 $A2)
      if let (.clear, some _) := (pat.case, fromImp) then
        let pf ← iIntroCore hyps A2 pats k
        return q(imp_intro_drop (Q := $Q) $pf)
      else
      let B ← mkFreshExprMVarQ q($prop)
      match pat.case, fromImp with
      | .intuitionistic p, some _ =>
        let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently false $A1 $B)
          | throwIPMError "{A1} not persistent"
        let pf ← iCasesCore hyps A2 p q(true) B (iIntroCore · · pats k)
        return q(imp_intro_intuitionistic (Q := $Q) $pf)
      | .intuitionistic p, none =>
        let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
          | throwIPMError "{Q} not a wand"
        let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently false $A1 $B)
          | throwIPMError "{A1} not persistent"
        let .some _ ← trySynthInstanceQ q(TCOr (Affine $A1) (Absorbing $A2))
          | throwIPMError "{A1} not affine and the goal not absorbing"
        let pf ← iCasesCore hyps A2 p q(true) B (iIntroCore · · pats k)
        return q(wand_intro_intuitionistic (A1 := $A1) (Q := $Q) $pf)
      | _, some _ =>
        -- should always succeed
        let _ ← ProofModeM.synthInstanceQ q(FromAffinely $B $A1)
        let .some _ ← trySynthInstanceQ q(TCOr (Persistent $A1) (Intuitionistic $P))
          | throwIPMError "{A1} is not persistent and spatial context is non-empty"
        let pf ← iCasesCore hyps A2 pat q(false) B (iIntroCore · · pats k)
        return q(imp_intro_spatial (Q := $Q) $pf)
      | _, none =>
        let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $Q .out $A1 $A2)
          | throwIPMError "{Q} not a wand"
        let pf ← iCasesCore hyps A2 pat q(false) A1 (iIntroCore · · pats k)
        return q(wand_intro_spatial (A1 := $A1) (Q := $Q) $pf)

/--
  `iintro pats` introduces hypotheses using the introduction pattern `pats`.
-/
elab "iintro " pats:(colGt ppSpace introPat)* : tactic => do
  -- parse syntax
  let pats ← liftMacroM <| pats.mapM <| IntroPat.parse

  ProofModeM.runTactic `iintro λ mvar { hyps, goal, .. } => do
    let pf ← iIntroCore hyps goal pats.toList

    mvar.assign pf
