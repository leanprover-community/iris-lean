/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.WeakestPreTransfinite
public import Iris.ProgramLogic.Adequacy
public import Iris.Instances.UPred.Transfinite

/-! # Adequacy of the weakest precondition of Transfinite Iris

This file ports `theories/program_logic/adequacy.v` of Transfinite Iris. Each program step of a
thread pool is simulated by a *logical step* (`gstep ∅ ⊤ ⊤`). The soundness of iterated logical
steps for pure propositions (`lstep_fupd_soundness`) requires transfinite step-indices
(`SIdxTransfinite`), and holds in particular for the natural numbers and for ordinals.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris ProgramLogic Language.Notation Iris.Std Iris.BI OFE LawfulSet PrimStep ToVal

theorem repeat_succ_inner {α : Type _} (f : α → α) (n : Nat) (a : α) :
    Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f ih

section BigLater

variable [BI PROP] [BIFUpdate PROP] {E : CoPset} {P : PROP}

/-- The big later implies `eventually` (Rocq: `big_later_eventually`). -/
@[rocq_alias big_later_eventually]
theorem bigLater_eventually : ⧍ P ⊢ eventually E P := by
  refine exists_elim fun n => ?_
  refine .trans ?_ (eventuallyN_eventually n)
  induction n with
  | zero => exact eventuallyN_intro
  | succ n ih => exact (later_mono ih).trans (eventuallyN_step_left n)

/-- An `eventually` at the empty mask is a logical step. -/
theorem eventually_lstep : eventually ∅ P ⊢ gstep ∅ E E P :=
  (fupd_mask_intro_frame empty_subset).trans <|
    fupd_mono (eventually_frame_right.trans (eventually_mono fupd_close))

/-- The big later is a logical step. -/
theorem bigLater_lstep : ⧍ P ⊢ gstep ∅ E E P :=
  bigLater_eventually.trans eventually_lstep

theorem bigLater_pure_and {φ ψ : Prop} : ⧍ ⌜φ⌝ ∗ ⧍ ⌜ψ⌝ ⊢ (⧍ ⌜φ ∧ ψ⌝ : PROP) :=
  bigLater_sep.trans (bigLater_mono pure_sep.mp)

end BigLater

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}

section adequacy

variable [ι : IrisGS Expr GF]

/-- The weakest preconditions of a thread pool (Rocq: `wptp`). -/
abbrev wptp (s : Stuckness) (t : List Expr) : IProp GF :=
  iprop([∗list] ef ∈ t, wp s ⊤ ef ι.forkPost)

/-- Rocq: `wp_step`. -/
theorem wp_step {s : Stuckness} {e₁ : Expr} {σ₁ : State} {κ κs : List Obs} {e₂ : Expr}
    {σ₂ : State} {efs : List Expr} {m : Nat} {Φ : Val → IProp GF}
    (Hstep : (e₁, σ₁) -<κ>-> (e₂, σ₂, efs)) :
    ⊢ ι.stateInterp σ₁ (κ ++ κs) m -∗ wp s ⊤ e₁ Φ -∗
      gstep ∅ ⊤ ⊤ iprop(ι.stateInterp σ₂ κs (efs.length + m) ∗ wp s ⊤ e₂ Φ ∗ wptp s efs) := by
  rw [wp_unfold]
  simp only [wpPre, Language.val_stuck Hstep]
  iintro Hσ H
  iapply gstep_fupd_right (E2 := ∅)
  iapply lstep_squash
  iapply gstep_fupd_right (E2 := ∅)
  imod H $$ %σ₁ %κ %κs %m Hσ with ⟨-, H⟩
  iapply H $$ %e₂ %σ₂ %efs %Hstep

/-- Rocq: `wptp_step`. -/
theorem wptp_step {s : Stuckness} {e₁ : Expr} {t₁ t₂ : List Expr} {κ κs : List Obs}
    {σ₁ σ₂ : State} {Φ : Val → IProp GF} (Hstep : (e₁ :: t₁, σ₁) -<κ>->ₜₚ (t₂, σ₂)) :
    ⊢ ι.stateInterp σ₁ (κ ++ κs) t₁.length -∗ wp s ⊤ e₁ Φ -∗ wptp s t₁ -∗
      ∃ e₂ t₂', ⌜t₂ = e₂ :: t₂'⌝ ∗
        gstep ∅ ⊤ ⊤ iprop(ι.stateInterp σ₂ κs t₂'.length ∗ wp s ⊤ e₂ Φ ∗ wptp s t₂') := by
  generalize hρ : (e₁ :: t₁, σ₁) = ρ at Hstep
  generalize hρ' : (t₂, σ₂) = ρ' at Hstep
  cases Hstep with
  | @atomic e σ obs e' σ' efs H l₁ l₂ =>
  simp only [Prod.mk.injEq] at hρ hρ'
  obtain ⟨h₁, rfl⟩ := hρ
  obtain ⟨rfl, rfl⟩ := hρ'
  cases l₁ with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h₁
    obtain ⟨he, hl⟩ := h₁
    subst e l₂
    iintro Hσ He Ht
    iexists e', t₁ ++ efs
    isplitr
    · ipureintro; simp
    imod wp_step H $$ Hσ He with ⟨Hσ, He, Hefs⟩
    have hl : efs.length + t₁.length = (t₁ ++ efs).length := by simp; omega
    rw [hl]
    iframe Hσ He
    iapply BigSepL.bigSepL_append.mpr
    iframe
  | cons x l₁' =>
    simp only [List.cons_append, List.cons.injEq] at h₁
    obtain ⟨hx, ht⟩ := h₁
    subst x t₁
    iintro Hσ He₁ Ht
    iexists e₁, l₁' ++ e' :: l₂ ++ efs
    isplitr
    · ipureintro; simp
    icases BigSepL.bigSepL_append.mp $$ Ht with ⟨Ht₁, Ht₂⟩
    icases BigSepL.bigSepL_cons.mp $$ Ht₂ with ⟨He, Ht₂⟩
    imod wp_step H $$ Hσ He with ⟨Hσ, He', Hefs⟩
    have hl : efs.length + (l₁' ++ e :: l₂).length = (l₁' ++ e' :: l₂ ++ efs).length := by
      simp; omega
    rw [hl]
    iframe Hσ He₁
    iapply BigSepL.bigSepL_append.mpr
    iframe Ht₁
    isplitl [He' Ht₂]
    · iapply BigSepL.bigSepL_cons.mpr
      iframe
    · iframe

/-- Rocq: `wptp_steps`. -/
@[rocq_alias wptp_steps]
theorem wptp_steps {s : Stuckness} {n : Nat} {e₁ : Expr} {t₁ t₂ : List Expr} {κs κs' : List Obs}
    {σ₁ σ₂ : State} {Φ : Val → IProp GF} (Hsteps : (e₁ :: t₁, σ₁) -<κs>->ₜₚ^[n] (t₂, σ₂)) :
    ⊢ ι.stateInterp σ₁ (κs ++ κs') t₁.length -∗ wp s ⊤ e₁ Φ -∗ wptp s t₁ -∗
      Nat.repeat (gstep ∅ ⊤ ⊤) n iprop(∃ e₂ t₂', ⌜t₂ = e₂ :: t₂'⌝ ∗
        ι.stateInterp σ₂ κs' t₂'.length ∗ wp s ⊤ e₂ Φ ∗ wptp s t₂') := by
  generalize hρ : (e₁ :: t₁, σ₁) = ρ at Hsteps
  generalize hρ' : (t₂, σ₂) = ρ' at Hsteps
  induction Hsteps generalizing e₁ t₁ σ₁ κs' with
  | refl ρ =>
    subst hρ; cases hρ'
    dsimp only [Nat.repeat]
    iintro Hσ He Ht
    iexists e₁, t₁
    simp only [List.nil_append]
    iframe
  | @cons n ρ₁ ρ₂ ρ₃ obs obs' hstep _ ih =>
    subst hρ hρ'
    obtain ⟨t_mid, σ_mid⟩ := ρ₂
    dsimp only [Nat.repeat]
    iintro Hσ He Ht
    rw [List.append_assoc]
    icases wptp_step hstep $$ Hσ He Ht with ⟨%e₂, %t₂', %Heq, H⟩
    subst Heq
    imod H with ⟨Hσ, He, Ht⟩
    iapply ih rfl rfl $$ Hσ He Ht

/-- Rocq: `wp_safe`. -/
@[rocq_alias wp_safe]
theorem wp_safe {κs : List Obs} {m : Nat} {e : Expr} {σ : State} {Φ : Val → IProp GF} :
    ⊢ ι.stateInterp σ κs m -∗ wp .NotStuck ⊤ e Φ ={⊤}=∗ ⧍ ⌜NotStuck (e, σ)⌝ := by
  rw [wp_unfold]
  unfold wpPre
  match h : toVal e with
  | some v =>
    dsimp only
    iintro _ _
    imodintro
    iapply bigLater_intro
    ipureintro
    exact .inl (by rw [h]; rfl)
  | none =>
    dsimp only
    iintro Hσ H
    ispecialize H $$ %σ %([]) %κs %m
    rw [List.nil_append]
    iapply lstep_fupd_plain (E2 := ∅)
    imod H $$ Hσ with ⟨%Hred, -⟩
    ipureintro
    exact .inr Hred

/-- Safety of a thread, keeping its resources. -/
theorem wp_safe_keep {κs : List Obs} {m : Nat} {e : Expr} {σ : State} {Φ : Val → IProp GF} :
    ι.stateInterp σ κs m ∗ wp .NotStuck ⊤ e Φ ⊢
      |={⊤}=> ⧍ ⌜NotStuck (e, σ)⌝ ∗ (ι.stateInterp σ κs m ∗ wp .NotStuck ⊤ e Φ) := by
  iintro H
  iapply fupd_keep_plain_sep (E' := ⊤) $$ [] H
  iintro ⟨Hσ, Hwp⟩
  iapply wp_safe $$ Hσ Hwp

/-- Safety of a thread pool, keeping its resources. -/
theorem wptp_safe_keep {κs : List Obs} {m : Nat} {σ : State} (t : List Expr) :
    ι.stateInterp σ κs m ∗ wptp .NotStuck t ⊢
      |={⊤}=> ⧍ ⌜∀ e ∈ t, NotStuck (e, σ)⌝ ∗ (ι.stateInterp σ κs m ∗ wptp .NotStuck t) := by
  induction t with
  | nil =>
    iintro H
    imodintro
    isplitr
    · iapply bigLater_intro; ipureintro; simp
    iexact H
  | cons e t ih =>
    iintro ⟨Hσ, Ht⟩
    icases BigSepL.bigSepL_cons.mp $$ Ht with ⟨He, Ht⟩
    imod wp_safe_keep $$ [$Hσ $He] with ⟨Ha, Hσ, He⟩
    imod ih $$ [$Hσ $Ht] with ⟨Hb, Hσ, Ht⟩
    imodintro
    isplitl [Ha Hb]
    · ihave H := bigLater_pure_and $$ [$Ha $Hb]
      iapply bigLater_mono (pure_mono fun ⟨h₁, h₂⟩ => List.forall_mem_cons.mpr ⟨h₁, h₂⟩) $$ H
    iframe Hσ
    iapply BigSepL.bigSepL_cons.mpr
    iframe

/-- Safety of the main thread and the thread pool, for any stuckness. -/
theorem wptp_safe_gen {s : Stuckness} {κs : List Obs} {m : Nat} {σ : State} {e : Expr}
    {Φ : Val → IProp GF} (t : List Expr) :
    ι.stateInterp σ κs m ∗ wp s ⊤ e Φ ∗ wptp s t ⊢
      |={⊤}=> ⧍ ⌜∀ e', s = .NotStuck → e' ∈ e :: t → NotStuck (e', σ)⌝ ∗
        (ι.stateInterp σ κs m ∗ wp s ⊤ e Φ ∗ wptp s t) := by
  cases s with
  | MaybeStuck =>
    iintro H
    imodintro
    isplitr
    · iapply bigLater_intro; ipureintro; intro _ h; cases h
    iexact H
  | NotStuck =>
    iintro ⟨Hσ, He, Ht⟩
    imod wp_safe_keep $$ [$Hσ $He] with ⟨Ha, Hσ, He⟩
    imod wptp_safe_keep t $$ [$Hσ $Ht] with ⟨Hb, Hσ, Ht⟩
    imodintro
    isplitl [Ha Hb]
    · ihave H := bigLater_pure_and $$ [$Ha $Hb]
      iapply bigLater_mono (pure_mono fun ⟨h₁, h₂⟩ e' _ hmem => (List.forall_mem_cons (p := fun e => NotStuck (e, σ))).mpr ⟨h₁, h₂⟩ e' hmem) $$ H
    iframe

/-- The value of a thread satisfies its postcondition. -/
theorem wp_postcondition {s : Stuckness} {e : Expr} {Φ : Val → IProp GF} :
    wp s ⊤ e Φ ⊢ |={⊤}=> (toVal e).elim iprop(True) Φ := by
  cases h : toVal e with
  | none => exact true_intro.trans fupd_intro
  | some v =>
    obtain rfl := (toVal_eq_iff_coe e v).mpr h
    exact wp_value_inv' s ⊤ Φ v

/-- The values in a thread pool satisfy the postcondition of forked threads. -/
theorem wptp_postconditions {s : Stuckness} (t : List Expr) :
    wptp s t ⊢ |={⊤}=> [∗list] v ∈ t.filterMap toVal, ι.forkPost v := by
  rw [BigSepL.bigSepL_filterMap]
  refine .trans (BigSepL.bigSepL_mono fun {k x} _ => ?_) (BigSepL2.bigSepL_fupd ⊤ _ t)
  cases h : toVal x with
  | none => exact Affine.affine.trans fupd_intro
  | some v =>
    obtain rfl := (toVal_eq_iff_coe x v).mpr h
    exact wp_value_inv' s ⊤ _ v

/-- Rocq: `wptp_strong_adequacy`. -/
@[rocq_alias wptp_strong_adequacy]
theorem wptp_strong_adequacy {s : Stuckness} {n : Nat} {e₁ : Expr} {t₁ t₂ : List Expr}
    {κs κs' : List Obs} {σ₁ σ₂ : State} {Φ : Val → IProp GF}
    (Hsteps : (e₁ :: t₁, σ₁) -<κs>->ₜₚ^[n] (t₂, σ₂)) :
    ⊢ ι.stateInterp σ₁ (κs ++ κs') t₁.length -∗ wp s ⊤ e₁ Φ -∗ wptp s t₁ -∗
      Nat.repeat (gstep ∅ ⊤ ⊤) (n + 1) iprop(∃ e₂ t₂', ⌜t₂ = e₂ :: t₂'⌝ ∗
        ⌜∀ e₂, s = .NotStuck → e₂ ∈ t₂ → NotStuck (e₂, σ₂)⌝ ∗
        ι.stateInterp σ₂ κs' t₂'.length ∗
        (toVal e₂).elim iprop(True) Φ ∗
        [∗list] v ∈ t₂'.filterMap toVal, ι.forkPost v) := by
  rw [repeat_succ_inner]
  iintro Hσ He Ht
  ihave H := wptp_steps (κs' := κs') Hsteps $$ Hσ He Ht
  imod H with ⟨%e₂, %t₂', %Heq, Hσ, He, Ht⟩
  subst Heq
  iapply gstep_fupd_left (E2 := ⊤)
  imod wptp_safe_gen t₂' $$ [$Hσ $He $Ht] with ⟨Hsafe, Hσ, He, Ht⟩
  imodintro
  iapply gstep_fupd_right (E2 := ⊤)
  ihave Hs := bigLater_lstep (E := ⊤) $$ Hsafe
  imod Hs with %Hsafe
  imod wp_postcondition $$ He with He
  imod wptp_postconditions t₂' $$ Ht with Ht
  imodintro
  iexists e₂, t₂'
  iframe
  ipureintro
  exact ⟨rfl, Hsafe⟩

end adequacy

/-- The adequacy theorem of Transfinite Iris (Rocq: `wp_strong_adequacy`). -/
theorem wp_strong_adequacy [SIdxTransfinite SI] [WsatGpreS GF] (s : Stuckness) (e₁ : Expr)
    (σ₁ : State) (n : Nat) (κs : List Obs) (t₂ : List Expr) (σ₂ : State) (φ : Prop)
    (Hwp : ∀ (W : WsatGS GF), ⊢ |={⊤}=> ∃ (stateI : State → List Obs → Nat → IProp GF)
        (Φ forkPost : Val → IProp GF),
      letI _ : IrisGS Expr GF := { toWsatGS := W, stateInterp := stateI, forkPost := forkPost }
      iprop(stateI σ₁ κs 0 ∗ wp s ⊤ e₁ Φ ∗
        (∀ e₂ t₂', ⌜t₂ = e₂ :: t₂'⌝ -∗
          ⌜∀ e₂, s = .NotStuck → e₂ ∈ t₂ → NotStuck (e₂, σ₂)⌝ -∗
          stateI σ₂ [] t₂'.length -∗
          (toVal e₂).elim iprop(True) Φ -∗
          ([∗list] v ∈ t₂'.filterMap toVal, forkPost v) -∗
          |={⊤,∅}=> ⌜φ⌝)))
    (Hsteps : ([e₁], σ₁) -<κs>->ₜₚ^[n] (t₂, σ₂)) : φ := by
  apply lstep_fupd_soundness (GF := GF) φ (n + 3)
  intro W
  change ⊢ gstep ∅ ⊤ ⊤ (Nat.repeat (gstep ∅ ⊤ ⊤) (n + 1 + 1) iprop(⌜φ⌝))
  rw [repeat_succ_inner _ (n + 1)]
  iapply gstep_fupd_left (E2 := ⊤)
  imod Hwp W with ⟨%stateI, %Φ, %forkPost, Hσ, He, Hφ⟩
  letI ι : IrisGS Expr GF := { toWsatGS := W, stateInterp := stateI, forkPost := forkPost }
  imodintro
  iapply lstep_intro
  imodintro
  ihave H := wptp_strong_adequacy (ι := ι) (κs' := []) (t₁ := []) Hsteps $$ [Hσ] He []
  · simp only [List.append_nil, List.length_nil]; iexact Hσ
  · iapply BigSepL.bigSepL_nil.mpr; itrivial
  imod H with ⟨%e₂, %t₂', %Heq, %Hsafe, Hσ, HΦ, Hfork⟩
  iapply lstep_intro
  iapply fupd_plain_mask (E' := ∅)
  iapply Hφ $$ %e₂ %t₂' %Heq %Hsafe Hσ HΦ Hfork

/-- Rocq: `wp_adequacy`. -/
theorem wp_adequacy [SIdxTransfinite SI] [WsatGpreS GF] (s : Stuckness) (e : Expr) (σ : State)
    (φ : Val → Prop)
    (Hwp : ∀ (W : WsatGS GF) (κs : List Obs), ⊢ |={⊤}=> ∃ (stateI : State → List Obs → IProp GF)
        (forkPost : Val → IProp GF),
      letI _ : IrisGS Expr GF :=
        { toWsatGS := W, stateInterp := fun σ κs _ => stateI σ κs, forkPost := forkPost }
      iprop(stateI σ κs ∗ wp s ⊤ e fun v => iprop(⌜φ v⌝))) :
    adequate s e σ (fun v _ => φ v) := by
  refine (adequate_alt s e σ (fun v _ => φ v)).mpr ?_
  intro t₂ σ₂ hreach
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  refine wp_strong_adequacy (GF := GF) s e σ n κs t₂ σ₂ _ (fun W => ?_) hsteps
  imod Hwp W κs with ⟨%stateI, %forkPost, Hσ, He⟩
  iexists (fun σ κs _ => stateI σ κs), (fun v => iprop(⌜φ v⌝)), forkPost
  imodintro
  iframe
  iintro %e₂ %t₂' %Heq %Hsafe _ HΦ _
  iapply fupd_mask_intro_discard empty_subset
  subst Heq
  cases h : toVal e₂
  · ipureintro
    refine ⟨fun v₂ t h' => ?_, Hsafe⟩
    cases h'
    simp [toVal_coe] at h
  · dsimp only [Option.elim_some]
    icases HΦ with %HΦ
    ipureintro
    refine ⟨fun v₂ t h' => ?_, Hsafe⟩
    cases h'
    simp only [toVal_coe, Option.some.injEq] at h
    exact h ▸ HΦ

/-- Rocq: `wp_invariance`. -/
theorem wp_invariance [SIdxTransfinite SI] [WsatGpreS GF] (s : Stuckness) (e₁ : Expr)
    (σ₁ : State) (t₂ : List Expr) (σ₂ : State) (φ : Prop)
    (Hwp : ∀ (W : WsatGS GF) (κs : List Obs), ⊢ |={⊤}=> ∃ (stateI : State → List Obs → Nat → IProp GF)
        (forkPost : Val → IProp GF),
      letI _ : IrisGS Expr GF := { toWsatGS := W, stateInterp := stateI, forkPost := forkPost }
      iprop(stateI σ₁ κs 0 ∗ wp s ⊤ e₁ (fun _ => iprop(True)) ∗
        (stateI σ₂ [] (t₂.length - 1) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)))
    (Hsteps : ([e₁], σ₁) -·->ₜₚ* (t₂, σ₂)) : φ := by
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp Hsteps
  refine wp_strong_adequacy (GF := GF) s e₁ σ₁ n κs t₂ σ₂ _ (fun W => ?_) hsteps
  imod Hwp W κs with ⟨%stateI, %forkPost, Hσ, He, Hφ⟩
  iexists stateI, (fun _ => iprop(True)), forkPost
  imodintro
  iframe
  iintro %e₂ %t₂' %Heq _ Hσ _ _
  subst Heq
  simp only [List.length_cons, Nat.add_sub_cancel]
  icases Hφ $$ Hσ with ⟨%E, Hφ⟩
  imod Hφ with %Hφ
  iapply fupd_mask_intro_discard empty_subset
  ipureintro
  exact Hφ

end Iris.Transfinite
