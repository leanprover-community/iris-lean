/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Tactics.Cases

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem imp_intro_drop [BI PROP] {P Q A1 A2 : PROP} [inst : FromImp Q A1 A2] (h : P ⊢ A2) : P ⊢ Q :=
  BI.imp_intro (and_elim_l' h) |>.trans inst.1

theorem from_forall_intro [BI PROP] {P Q : PROP} {Φ : α → PROP} [inst : FromForall Q Φ]
    (h : ∀ a, P ⊢ Φ a) : P ⊢ Q :=
  (forall_intro h).trans inst.1

theorem imp_intro_intuitionistic [BI PROP] {P Q A1 A2 B : PROP}
    [FromImp Q A1 A2] [inst : IntoPersistently false A1 B] (h : P ∗ □ B ⊢ A2) : P ⊢ Q := by
  refine BI.imp_intro ?_ |>.trans from_imp
  exact (and_mono_r inst.1).trans <| persistently_and_intuitionistically_sep_r.1.trans h

theorem wand_intro_intuitionistic [BI PROP] {P Q A1 A2 B : PROP}
    [FromWand Q A1 A2] [inst : IntoPersistently false A1 B] [or : TCOr (Affine A1) (Absorbing A2)]
    (h : P ∗ □ B ⊢ A2) : P ⊢ Q := by
  refine (wand_intro ?_).trans from_wand
  exact match or with
  | TCOr.l => (sep_mono_r <| (affine_affinely A1).2.trans (affinely_mono inst.1)).trans h
  | TCOr.r => (sep_mono_r <| inst.1.trans absorbingly_intuitionistically.2).trans <|
      absorbingly_sep_r.1.trans <| (absorbingly_mono h).trans absorbing

theorem imp_intro_spatial [BI PROP] {P Q A1 A2 B : PROP}
    [FromImp Q A1 A2] [inst : FromAffinely B A1] [or : TCOr (Persistent A1) (Intuitionistic P)]
    (h : P ∗ B ⊢ A2) : P ⊢ Q := by
  refine (BI.imp_intro ?_).trans from_imp
  refine Entails.trans ?_ <| (sep_mono_r inst.1).trans h
  exact match or with
  | TCOr.l => persistent_and_affinely_sep_r_1
  | TCOr.r (u := u) =>
    (and_mono_l u.1).trans <| affinely_and_lr.1.trans <|
    persistently_and_intuitionistically_sep_l.1.trans <| sep_mono_l intuitionistically_elim

theorem wand_intro_spatial [BI PROP] {P Q A1 A2 : PROP}
    [FromWand Q A1 A2] (h : P ∗ A1 ⊢ A2) : P ⊢ Q := (wand_intro h).trans from_wand

variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
partial def iIntroCore
    {P} (hyps : Hyps bi P) (Q : Q($prop)) (pats : List iCasesPat)
    (k : ∀ {P}, Hyps bi P → (Q : Q($prop)) → MetaM Q($P ⊢ $Q)) :
    MetaM (Q($P ⊢ $Q)) := do
  match pats with
  | [] => k hyps Q
  | pat :: pats =>
    let A1 ← mkFreshExprMVarQ q($prop)
    let A2 ← mkFreshExprMVarQ q($prop)
    let fromImp ← try? (α := Q(FromImp $Q $A1 $A2)) do
      synthInstanceQ q(FromImp $Q $A1 $A2)
    if let (.clear, some _) := (pat, fromImp) then
      let pf ← iIntroCore hyps A2 pats k
      return q(imp_intro_drop (Q := $Q) $pf)
    else
    let alres ← try? (α := _ × (v : Level) × (α : Q(Sort v)) × (Φ : Q($α → $prop)) ×
        Q(FromForall $Q $Φ)) do
      let .one n := pat | failure
      let v ← mkFreshLevelMVar
      let α ← mkFreshExprMVarQ q(Sort v)
      let Φ ← mkFreshExprMVarQ q($α → $prop)
      Pure.pure ⟨n, v, α, Φ, ← synthInstanceQ q(FromForall $Q $Φ)⟩
    if let some ⟨n, _, α, Φ, _⟩ := alres then
      let (n, ref) ← getFreshName n
      withLocalDeclDQ n α fun x => do
        addLocalVarInfo ref (← getLCtx) x α
        have B : Q($prop) := Expr.headBeta q($Φ $x)
        have : $B =Q $Φ $x := ⟨⟩
        let pf : Q(∀ x, $P ⊢ $Φ x) ← mkLambdaFVars #[x] <|← iIntroCore hyps B pats k
        return q(from_forall_intro (Q := $Q) $pf)
    else
    let B ← mkFreshExprMVarQ q($prop)
    match pat, fromImp with
    | .intuitionistic pat, some _ =>
      let _ ← synthInstanceQ q(IntoPersistently false $A1 $B)
      let pf ← iCasesCore bi hyps A2 q(true) q(iprop(□ $B)) B ⟨⟩ pat (iIntroCore · A2 pats k)
      return q(imp_intro_intuitionistic (Q := $Q) $pf)
    | .intuitionistic pat, none =>
      let _ ← synthInstanceQ q(FromWand $Q $A1 $A2)
      let _ ← synthInstanceQ q(IntoPersistently false $A1 $B)
      let _ ← synthInstanceQ q(TCOr (Affine $A1) (Absorbing $A2))
      let pf ← iCasesCore bi hyps A2 q(true) q(iprop(□ $B)) B ⟨⟩ pat (iIntroCore · A2 pats k)
      return q(wand_intro_intuitionistic (Q := $Q) $pf)
    | _, some _ =>
      let _ ← synthInstanceQ q(FromAffinely $B $A1)
      let _ ← synthInstanceQ q(TCOr (Persistent $A1) (Intuitionistic $P))
      let pf ← iCasesCore bi hyps A2 q(false) B B ⟨⟩ pat (iIntroCore · A2 pats k)
      return q(imp_intro_spatial (Q := $Q) $pf)
    | _, none =>
      let _ ← synthInstanceQ q(FromWand $Q $A1 $A2)
      let pf ← iCasesCore bi hyps A2 q(false) A1 A1 ⟨⟩ pat (iIntroCore · A2 pats k)
      return q(wand_intro_spatial (Q := $Q) $pf)


elab "iintro" pats:(colGt icasesPat)* : tactic => do
  -- parse syntax
  let pats ← liftMacroM <| pats.mapM <| iCasesPat.parse

  let (mvar, { bi, hyps, goal, .. }) ← istart (← getMainGoal)
  mvar.withContext do

  -- process patterns
  let gs ← Goals.new bi
  let pf ← iIntroCore bi hyps goal pats.toList <| gs.addGoal

  mvar.assign pf
  replaceMainGoal (← gs.getGoals)
