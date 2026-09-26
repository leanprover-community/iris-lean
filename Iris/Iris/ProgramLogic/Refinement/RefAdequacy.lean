/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.Refinement.RefWeakestPre

/-! # Adequacy of the refinement weakest precondition (Transfinite Iris)

This file ports `theories/program_logic/refinement/ref_adequacy.v` of Transfinite Iris:
*termination preservation*. If the source is strongly normalizing and the refinement weakest
precondition of `e` is satisfiable (relative to world satisfaction), then `e` has no infinite
execution (`rwp_adequacy`), i.e. `e` is strongly normalizing (`rwp_sn_preservation`).

The proof lifts `rwp` to thread pools (`rwpTp`, a least fixpoint) and unfolds it into `guarded`
propositions, which become true after finitely many source steps (`guarded_satisfiable`). The
existential property of satisfiability used here requires large step-indices (`SIdxLarge`), e.g.
ordinals.

The coinductive `ex_loop` of Rocq is replaced by the existence of an infinite execution
(`ExLoop`), as in `Iris.Examples.TransfiniteSimulations`.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris ProgramLogic Language Language.Notation Iris.Std Iris.BI OFE Relation

/-- An infinite execution along `R` starting at `x` (Rocq: `ex_loop`). -/
def ExLoop {X : Type _} (R : X → X → Prop) (x : X) : Prop :=
  ∃ f : Nat → X, f 0 = x ∧ ∀ n, R (f n) (f (n + 1))

theorem ExLoop.step {X : Type _} {R : X → X → Prop} {x : X} :
    ExLoop R x → ∃ x', R x x' ∧ ExLoop R x'
  | ⟨f, h0, hf⟩ => ⟨f 1, h0 ▸ hf 0, ⟨fun n => f (n + 1), rfl, fun n => hf (n + 1)⟩⟩

theorem ExLoop.of_step {X : Type _} {R : X → X → Prop} (P : X → Prop)
    (hstep : ∀ x, P x → ∃ x', R x x' ∧ P x') {x : X} (hx : P x) : ExLoop R x := by
  let g : Nat → {x // P x} := fun n =>
    n.rec ⟨x, hx⟩ fun _ y => ⟨Classical.choose (hstep y.1 y.2), (Classical.choose_spec (hstep y.1 y.2)).2⟩
  exact ⟨fun n => (g n).1, rfl, fun n => (Classical.choose_spec (hstep (g n).1 (g n).2)).1⟩

/-- Without an infinite execution, a relation is strongly normalizing (Rocq: `sn_not_ex_loop`). -/
theorem sn_of_not_exLoop {X : Type _} (R : X → X → Prop) (x : X) (h : ¬ExLoop R x) :
    StronglyNormalizing R x := by
  refine Classical.byContradiction fun hx => h (ExLoop.of_step (fun y => ¬Acc (flip R) y) ?_ hx)
  intro y hy
  refine Classical.byContradiction fun hno => hy ⟨_, fun z hz => ?_⟩
  exact Classical.byContradiction fun hz' => hno ⟨z, hz, hz'⟩

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} {A : Type _} [src : Source GF A] [ι : RefIrisGS Expr GF]

/-! ## Thread pools -/

/-- Thread pools, as arguments of the fixpoint `rwpTpF` (with the discrete OFE; the step-index
type is determined by `GF`). -/
structure TP (Expr : Type _) (GF : BundledGFunctors) where
  toList : List Expr

instance : OFE (TP Expr GF) := OFE.ofDiscrete _

/-- Rocq: `rwp_tp_pre`. -/
def rwpTpPre (rwpTp : TP Expr GF → IProp GF) (t₁ : TP Expr GF) : IProp GF :=
  iprop(∀ t₂ (σ σ' : State) (κ : List Obs) (a : A) (n : Nat),
    ⌜(t₁.toList, σ) -<κ>->ₜₚ (t₂, σ')⌝ -∗ src.interp a ∗ ι.refStateInterp σ n ={⊤,∅}=∗
      ∃ b : Bool, ▷?b |={∅,⊤}=> ∃ m, ι.refStateInterp σ' m ∗
        (if b then ∃ a' : A, ⌜TransGen src.rel a a'⌝ ∗ rwpTp ⟨t₂⟩ ∗ src.interp a'
          else rwpTp ⟨t₂⟩ ∗ src.interp a))

/-- Rocq: `rwp_tp_pre_mono`. -/
theorem rwpTpPre_mono (X Y : TP Expr GF → IProp GF) :
    ⊢ □ (∀ t, X t -∗ Y t) -∗ ∀ t, rwpTpPre (src := src) (ι := ι) X t -∗ rwpTpPre (src := src) Y t := by
  iintro #H %t Hwp
  unfold rwpTpPre
  iintro %t₂ %σ %σ' %κ %a %n %Hstep Hσ
  imod Hwp $$ %t₂ %σ %σ' %κ %a %n %Hstep Hσ with ⟨%b, Hwp⟩
  imodintro
  iexists b
  ihave Hwp := laterN_frame_intuitionistic (R := iprop(∀ t, X t -∗ Y t)) $$ [Hwp]
  · isplitr [Hwp]
    · imodintro
      iexact H
    · iexact Hwp
  iapply laterN_mono _ ?_ $$ Hwp
  iintro ⟨#H, Hwp⟩
  imod Hwp with ⟨%m, Hσ, Hwp⟩
  imodintro
  iexists m
  iframe Hσ
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · icases Hwp with ⟨Hwp, $⟩
    iapply H $$ Hwp
  · icases Hwp with ⟨%a', %Ha', Hwp, Hsrc⟩
    iexists a'
    iframe
    isplitr
    · ipureintro
      exact Ha'
    · iapply H $$ Hwp

instance rwpTpPre_monoPred : BIMonoPred (rwpTpPre (src := src) (ι := ι)) where
  mono_pred := by
    intro X Y _ _
    iintro #HXY %t HX
    iapply rwpTpPre_mono $$ [] HX
    iexact HXY
  mono_pred_ne {X} _ := ⟨fun {n} t₁ t₂ h => by
    obtain rfl : t₁ = t₂ := h
    exact .rfl⟩

/-- The fixpoint on thread pools. -/
def rwpTpF (t : TP Expr GF) : IProp GF :=
  bi_least_fixpoint (rwpTpPre (src := src) (ι := ι)) t

/-- The refinement weakest precondition of a thread pool (Rocq: `rwp_tp`). -/
abbrev rwpTp (t : List Expr) : IProp GF := rwpTpF (src := src) (ι := ι) ⟨t⟩

/-- Rocq: `rwp_tp_unfold`. -/
theorem rwpTp_unfold {t : List Expr} :
    rwpTp (src := src) (ι := ι) t ⊣⊢ rwpTpPre (src := src) (rwpTpF (src := src) (ι := ι)) ⟨t⟩ :=
  equiv_iff.mp (least_fixpoint_unfold (rwpTpPre (src := src) (ι := ι)))

/-- Rocq: `rwp_tp_ind`. -/
theorem rwpTp_ind (Ψ : List Expr → IProp GF) :
    ⊢ □ (∀ t, rwpTpPre (src := src) (ι := ι)
        (fun t => iprop(Ψ t.toList ∧ rwpTpF (src := src) (ι := ι) t)) ⟨t⟩ -∗ Ψ t) -∗
      ∀ t, rwpTp (src := src) (ι := ι) t -∗ Ψ t := by
  letI : NonExpansive (fun t : TP Expr GF => Ψ t.toList) := ⟨fun {n} t₁ t₂ h => by
    obtain rfl : t₁ = t₂ := h
    exact .rfl⟩
  iintro #IH %t
  unfold rwpTp rwpTpF
  iapply least_fixpoint_ind (F := rwpTpPre (src := src) (ι := ι)) (Φ := fun t => Ψ t.toList) $$ []
  iintro !> %⟨t'⟩
  iapply IH

theorem rwpTpPre_and_elim {Φ : TP Expr GF → IProp GF} {t : List Expr} :
    rwpTpPre (src := src) (ι := ι) (fun t => iprop(Φ t ∧ rwpTpF (src := src) (ι := ι) t)) ⟨t⟩ ⊢
      rwpTp (src := src) (ι := ι) t := by
  iintro H
  iapply rwpTp_unfold.mpr
  iapply rwpTpPre_mono $$ [] H
  iintro !> %t ⟨-, H⟩
  iexact H

/-- The empty thread pool. -/
theorem rwpTp_nil : ⊢ rwpTp (src := src) (ι := ι) ([] : List Expr) := by
  iapply rwpTp_unfold.mpr
  unfold rwpTpPre
  iintro %t₂ %σ %σ' %κ %a %n %Hstep
  exfalso
  simp only at Hstep
  generalize hρ : (([] : List Expr), σ) = ρ at Hstep
  cases Hstep with
  | atomic _ l₁ l₂ => simp at hρ

/-- Rocq: `rwp_tp_Permutation`. -/
theorem rwpTp_perm {t₁ t₁' : List Expr} (h : t₁.Perm t₁') :
    rwpTp (src := src) (ι := ι) t₁ ⊢ rwpTp (src := src) (ι := ι) t₁' := by
  iintro H
  iapply rwpTp_ind (Ψ := fun t => iprop(∀ t' : List Expr, ⌜t.Perm t'⌝ -∗
    rwpTp (src := src) (ι := ι) t')) $$ [] H %t₁' %h
  iintro !> %t IH %t' %Ht
  iapply rwpTp_unfold.mpr
  unfold rwpTpPre
  iintro %t₂ %σ %σ' %κ %a %n %Hstep Hσ
  obtain ⟨t₂', Ht₂, Hstep'⟩ := perm_of_step Ht.symm Hstep
  imod IH $$ %t₂' %σ %σ' %κ %a %n %Hstep' Hσ with ⟨%b, IH⟩
  imodintro
  iexists b
  iapply laterN_mono _ ?_ $$ IH
  iintro IH
  imod IH with ⟨%m, Hσ, IH⟩
  imodintro
  iexists m
  iframe Hσ
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · icases IH with ⟨⟨IH, -⟩, $⟩
    iapply IH $$ %t₂ %Ht₂.symm
  · icases IH with ⟨%a', %Ha', ⟨IH, -⟩, Hsrc⟩
    iexists a'
    iframe
    isplitr
    · ipureintro
      exact Ha'
    · iapply IH $$ %t₂ %Ht₂.symm

/-- Rocq: `rwp_tp_app`. -/
theorem rwpTp_app {t₁ t₂ : List Expr} :
    ⊢ rwpTp (src := src) (ι := ι) t₁ -∗ rwpTp (src := src) (ι := ι) t₂ -∗
      rwpTp (src := src) (ι := ι) (t₁ ++ t₂) := by
  iintro H₁
  iapply rwpTp_ind (Ψ := fun t₁ => iprop(∀ t₂ : List Expr, rwpTp (src := src) (ι := ι) t₂ -∗
    rwpTp (src := src) (ι := ι) (t₁ ++ t₂))) $$ [] H₁
  iintro !> %t₁ IH₁ %t₂ H₂
  iapply rwpTp_ind (Ψ := fun t₂ => iprop(∀ t₁ : List Expr, rwpTpPre (src := src) (ι := ι)
      (fun t => iprop((∀ t₂ : List Expr, rwpTp (src := src) (ι := ι) t₂ -∗
        rwpTp (src := src) (ι := ι) (t.toList ++ t₂)) ∧ rwpTpF (src := src) (ι := ι) t)) ⟨t₁⟩ -∗
      rwpTp (src := src) (ι := ι) (t₁ ++ t₂))) $$ [] H₂ IH₁
  iintro !> %t₂ IH₂ %t₁ IH₁
  ihave IH₂ := and_intro rwpTpPre_and_elim .rfl $$ IH₂
  iapply rwpTp_unfold.mpr
  unfold rwpTpPre
  iintro %t'' %σ₁ %σ₂ %κ %a %n %Hstep Hσ
  generalize hρ : (t₁ ++ t₂, σ₁) = ρ at Hstep
  generalize hρ' : (t'', σ₂) = ρ' at Hstep
  cases Hstep with
  | @atomic e σ obs e' σ' efs Hprim l₁ l₂ =>
  simp only [Prod.mk.injEq] at hρ hρ'
  obtain ⟨hl, rfl⟩ := hρ
  obtain ⟨rfl, rfl⟩ := hρ'
  rcases List.append_eq_append_iff.mp hl.symm with ⟨m, ht₁, hm⟩ | ⟨c, hl₁, ht₂⟩
  · cases m with
    | nil =>
      -- the step is at the head of `t₂`
      simp only [List.append_nil, List.nil_append] at ht₁ hm
      subst ht₁
      have hstep₂ : (t₂, σ₁) -<κ>->ₜₚ (e' :: l₂ ++ efs, σ₂) := by
        rw [← hm]
        exact Step.of_primStep (t₁ := []) Hprim
      icases IH₂ with ⟨-, IH₂⟩
      imod IH₂ $$ %_ %σ₁ %σ₂ %κ %a %n %hstep₂ Hσ with ⟨%b, IH₂⟩
      imodintro
      iexists b
      iapply laterN_wand_frame₁ ?h $$ IH₁ IH₂
      case h =>
        iintro ⟨IH₁, IH₂⟩
        imod IH₂ with ⟨%m', Hσ, IH₂⟩
        imodintro
        iexists m'
        iframe Hσ
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · icases IH₂ with ⟨⟨IH₂, -⟩, $⟩
          ihave H := IH₂ $$ %_ IH₁
          try simp only [List.cons_append, List.append_assoc]
          iexact H
        · icases IH₂ with ⟨%a', %Ha', ⟨IH₂, -⟩, Hsrc⟩
          iexists a'
          iframe Hsrc
          isplitr
          · ipureintro
            exact Ha'
          · ihave H := IH₂ $$ %_ IH₁
            try simp only [List.cons_append, List.append_assoc]
            iexact H
    | cons x m =>
      -- the step is in `t₁`
      simp only [List.cons_append, List.cons.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have hstep₁ : (t₁, σ₁) -<κ>->ₜₚ (l₁ ++ e' :: m ++ efs, σ₂) := by
        rw [ht₁]
        exact Step.of_primStep Hprim
      icases IH₂ with ⟨H₂, -⟩
      imod IH₁ $$ %_ %σ₁ %σ₂ %κ %a %n %hstep₁ Hσ with ⟨%b, IH₁⟩
      imodintro
      iexists b
      have hperm : ((l₁ ++ e' :: m ++ efs) ++ t₂).Perm
          (l₁ ++ e' :: (m ++ t₂) ++ efs) := by
        simp only [List.append_assoc, List.cons_append]
        exact List.Perm.append_left l₁ (List.Perm.cons e' (List.Perm.append_left m List.perm_append_comm))
      iapply laterN_wand_frame₁ ?h $$ H₂ IH₁
      case h =>
        iintro ⟨H₂, IH₁⟩
        imod IH₁ with ⟨%m', Hσ, IH₁⟩
        imodintro
        iexists m'
        iframe Hσ
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · icases IH₁ with ⟨⟨IH₁, -⟩, $⟩
          ihave H := IH₁ $$ %t₂ H₂
          iapply rwpTp_perm hperm $$ H
        · icases IH₁ with ⟨%a', %Ha', ⟨IH₁, -⟩, Hsrc⟩
          iexists a'
          iframe Hsrc
          isplitr
          · ipureintro
            exact Ha'
          · ihave H := IH₁ $$ %t₂ H₂
            iapply rwpTp_perm hperm $$ H
  · -- the step is in `t₂`, after its head
    subst hl₁
    have hstep₂ : (t₂, σ₁) -<κ>->ₜₚ (c ++ e' :: l₂ ++ efs, σ₂) := by
      rw [ht₂]
      exact Step.of_primStep Hprim
    icases IH₂ with ⟨-, IH₂⟩
    imod IH₂ $$ %_ %σ₁ %σ₂ %κ %a %n %hstep₂ Hσ with ⟨%b, IH₂⟩
    imodintro
    iexists b
    iapply laterN_wand_frame₁ ?h $$ IH₁ IH₂
    case h =>
      iintro ⟨IH₁, IH₂⟩
      imod IH₂ with ⟨%m', Hσ, IH₂⟩
      imodintro
      iexists m'
      iframe Hσ
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · icases IH₂ with ⟨⟨IH₂, -⟩, $⟩
        ihave H := IH₂ $$ %t₁ IH₁
        try simp only [List.append_assoc, List.cons_append]
        iexact H
      · icases IH₂ with ⟨%a', %Ha', ⟨IH₂, -⟩, Hsrc⟩
        iexists a'
        iframe Hsrc
        isplitr
        · ipureintro
          exact Ha'
        · ihave H := IH₂ $$ %t₁ IH₁
          try simp only [List.append_assoc, List.cons_append]
          iexact H


theorem rwpTp_bigSepL {efs : List Expr} {Q : Expr → IProp GF} :
    ([∗list] ef ∈ efs, iprop((⌜(⊤ : CoPset) = ⊤⌝ -∗ rwpTp (src := src) (ι := ι) [ef]) ∧ Q ef)) ⊢
      rwpTp (src := src) (ι := ι) efs := by
  induction efs with
  | nil => exact Affine.affine.trans rwpTp_nil
  | cons ef efs ih =>
    iintro H
    icases BigSepL.bigSepL_cons.mp $$ H with ⟨⟨H₁, -⟩, H₂⟩
    rw [show ef :: efs = [ef] ++ efs from rfl]
    iapply rwpTp_app (t₁ := [ef]) (t₂ := efs) $$ [H₁] [H₂]
    · iapply H₁
      ipureintro
      rfl
    · iapply ih $$ H₂

/-- `rwp` subsumes `rwpTp` (Rocq: `rwp_rwp_tp`). -/
theorem rwp_rwpTp {s : Stuckness} {e : Expr} {Φ : Val → IProp GF} :
    rwp (src := src) (ι := ι) s ⊤ e Φ ⊢ rwpTp (src := src) (ι := ι) [e] := by
  iintro H
  ihave H := rwp_strong_ind s (fun E e _ => iprop(⌜E = ⊤⌝ -∗ rwpTp (src := src) (ι := ι) [e]))
    (by intro _ _ _ _ _ _; exact .rfl) $$ [] %e %⊤ %Φ H
  rotate_left
  · iapply H
    ipureintro
    rfl
  iintro !> %e %E %Φ IH %HE
  subst HE
  iapply rwpTp_unfold.mpr
  unfold rwpTpPre
  iintro %t' %σ %σ' %κ %a %n %Hstep ⟨Ha, Hσ⟩
  simp only at Hstep
  generalize hρ : ([e], σ) = ρ at Hstep
  generalize hρ' : (t', σ') = ρ' at Hstep
  cases Hstep with
  | @atomic e₀ σ₀ obs e₀' σ₀' efs Hprim l₁ l₂ =>
  simp only [Prod.mk.injEq] at hρ hρ'
  obtain ⟨hl, rfl⟩ := hρ
  obtain ⟨rfl, rfl⟩ := hρ'
  obtain ⟨rfl, rfl, rfl⟩ : l₁ = [] ∧ e₀ = e ∧ l₂ = [] := by
    cases l₁ with
    | nil => simp only [List.nil_append, List.cons.injEq] at hl; exact ⟨rfl, hl.1.symm, hl.2.symm⟩
    | cons x l => simp at hl
  unfold rwpPre
  rw [Language.val_stuck Hprim]
  dsimp only
  unfold rwpStep
  imod IH $$ %σ %n %a [$Ha $Hσ] with ⟨%b, IH⟩
  imodintro
  iexists b
  iapply laterN_mono _ ?_ $$ IH
  iintro IH
  imod IH with ⟨-, IH⟩
  imod IH $$ %e₀' %σ' %efs %κ %Hprim with ⟨Hsrc, Hσ, ⟨IH, -⟩, Hefs⟩
  imodintro
  iexists (efs.length + n)
  iframe Hσ
  ihave Htp : rwpTp (src := src) (ι := ι) ([e₀'] ++ efs) $$ [IH Hefs]
  · iapply rwpTp_app (t₁ := [e₀']) (t₂ := efs) $$ [IH] [Hefs]
    · iapply IH
      ipureintro
      rfl
    · iapply rwpTp_bigSepL $$ Hefs
  simp only [List.nil_append]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · iframe
  · icases Hsrc with ⟨%a', %Ha', Hsrc⟩
    iexists a'
    iframe
    ipureintro
    exact Ha'

/-! ## Guarded propositions -/

omit ι in
/-- Rocq: `guarded_pre`. -/
def guardedPre [W : WsatGS GF] (grd : A → IProp GF → IProp GF) (a : A) (P : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ((|={∅,⊤}=> P) ∨ ▷ |={∅,⊤}=> ∃ a' : A, ⌜TransGen src.rel a a'⌝ ∗ grd a' P))

omit ι in
instance guardedPre_contractive [W : WsatGS GF] : Contractive (guardedPre (src := src) (W := W)) where
  distLater_dist {n g₁ g₂} H := fun a P => by
    unfold guardedPre
    refine BIFUpdate.ne.ne (or_ne.ne .rfl ?_)
    refine Contractive.distLater_dist fun k hk => ?_
    exact BIFUpdate.ne.ne (exists_ne fun a' => sep_ne.ne .rfl (H k hk a' P))

omit ι in
/-- Guarded propositions: `P` holds after finitely many source steps (Rocq: `guarded`). -/
def guarded [W : WsatGS GF] : A → IProp GF → IProp GF := fixpoint (guardedPre (src := src) (W := W))

omit ι in
/-- Rocq: `guarded_unfold`. -/
theorem guarded_unfold [W : WsatGS GF] (a : A) (P : IProp GF) :
    guarded (src := src) (W := W) a P = guardedPre (src := src) (guarded (src := src)) a P :=
  congrFun (congrFun (fixpoint_unfold (guardedPre (src := src) (W := W)).toContractiveHom) a) P

omit ι in
/-- Guarded propositions become true if the source is strongly normalizing
(Rocq: `guarded_satisfiable`). -/
theorem guarded_satisfiable [W : WsatGS GF] {A : Type u} [src : Source GF A] [SIdxLarge.{u} SI]
    {a : A} {P : IProp GF} (hsn : StronglyNormalizing src.rel a)
    (hsat : satisfiableAt ⊤ (guarded (src := src) a P)) : satisfiableAt ⊤ P := by
  have hsn' := (sn_transGen _ _).mp hsn
  clear hsn
  induction hsn' with
  | intro a _ IH =>
    rw [guarded_unfold] at hsat
    unfold guardedPre at hsat
    rcases satisfiableAt_or (satisfiableAt_fupd hsat) with h | h
    · exact satisfiableAt_fupd h
    · obtain ⟨a', h⟩ := satisfiableAt_exists (satisfiableAt_fupd (satisfiableAt_later h))
      obtain ⟨h₁, h₂⟩ := satisfiableAt_sep h
      exact IH a' (satisfiableAt_pure h₁) h₂

/-- Rocq: `rwp_tp_guarded_false`. -/
theorem rwpTp_guarded_false {t : List Expr} :
    rwpTp (src := src) (ι := ι) t ⊢ ∀ σ a n, ⌜ExLoop ErasedStep (t, σ)⌝ -∗ src.interp a -∗
      ι.refStateInterp σ n -∗ guarded (src := src) a iprop(False) := by
  iintro H
  iapply rwpTp_ind (Ψ := fun t => iprop(∀ σ a n, ⌜ExLoop ErasedStep (t, σ)⌝ -∗ src.interp a -∗
    ι.refStateInterp σ n -∗ guarded (src := src) a iprop(False))) $$ [] H
  iintro !> %t IH %σ %a %n %Hloop Ha Hσ
  obtain ⟨⟨t', σ'⟩, ⟨κ, Hstep⟩, Hloop'⟩ := Hloop.step
  unfold rwpTpPre
  ihave H := IH $$ %t' %σ %σ' %κ %a %n %Hstep [$Ha $Hσ]
  rw [guarded_unfold]
  unfold guardedPre
  imod H with ⟨%b, H⟩
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, laterIf_false, laterIf_true]
  · imod H with ⟨%m, Hσ, ⟨Hev, -⟩, Ha⟩
    ihave G := Hev $$ %σ' %a %m %Hloop' Ha Hσ
    rw [guarded_unfold]
    unfold guardedPre
    iexact G
  · imodintro
    iright
    inext
    imod H with ⟨%m, Hσ, %a', %Ha', ⟨Hev, -⟩, Hsrc⟩
    imodintro
    iexists a'
    isplitr
    · ipureintro
      exact Ha'
    · iapply Hev $$ %σ' %a' %m %Hloop' Hsrc Hσ

/-- Termination preservation: a satisfiable refinement weakest precondition, with a strongly
normalizing source, has no infinite execution (Rocq: `rwp_adequacy`). -/
theorem rwp_adequacy {A : Type u} [src : Source GF A] [SIdxLarge.{u} SI] {Φ : Val → IProp GF}
    {a : A} {e : Expr} {σ : State} {n : Nat} {s : Stuckness}
    (hsn : StronglyNormalizing src.rel a) (hloop : ExLoop ErasedStep ([e], σ))
    (hsat : satisfiableAt ⊤ iprop(src.interp a ∗ ι.refStateInterp σ n ∗
      rwp (src := src) (ι := ι) s ⊤ e Φ)) : False := by
  refine satisfiableAt_pure (guarded_satisfiable hsn (satisfiableAt_mono hsat ?_))
  iintro ⟨Ha, Hσ, Hwp⟩
  ihave H := rwp_rwpTp $$ Hwp
  iapply rwpTp_guarded_false $$ H %σ %a %n %hloop Ha Hσ

/-- Rocq: `rwp_sn_preservation`. -/
theorem rwp_sn_preservation {A : Type u} [src : Source GF A] [SIdxLarge.{u} SI]
    {Φ : Val → IProp GF} {a : A} {e : Expr} {σ : State} {n : Nat} {s : Stuckness}
    (hsn : StronglyNormalizing src.rel a)
    (hsat : satisfiableAt ⊤ iprop(src.interp a ∗ ι.refStateInterp σ n ∗
      rwp (src := src) (ι := ι) s ⊤ e Φ)) :
    StronglyNormalizing ErasedStep ([e], σ) :=
  sn_of_not_exLoop _ _ fun hloop => rwp_adequacy hsn hloop hsat

end Iris.Transfinite
