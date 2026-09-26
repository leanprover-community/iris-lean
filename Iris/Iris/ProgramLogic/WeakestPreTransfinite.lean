/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.Lib.FUpdTransfinite
public import Iris.BI.Lib.LogicalStep
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProofMode

/-! # The weakest precondition of Transfinite Iris

This file ports `theories/program_logic/weakestpre.v` of Transfinite Iris. The weakest
precondition is defined over an arbitrary type of step-indices, using the credit-free fancy updates
of `Iris.Instances.Lib.FUpdTransfinite`. Instead of taking exactly one later per program step, a
step may be preceded by a *logical step* (`gstep`, `Iris.BI.Lib.LogicalStep`), i.e. finitely many
laters interleaved with fancy updates.

The *strong* weakest precondition `swp k s E e Φ` (Rocq: `SWP e at k @ s; E {{ Φ }}`) takes exactly
`k` logical steps before the next program step.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris ProgramLogic Language.Notation Iris.Std Iris.BI OFE

/-- The ghost state and state interpretation of the transfinite program logic (Rocq: `irisG`). -/
@[rocq_alias irisG]
class IrisGS (Expr : Type _) {Val State Obs : Type _} [Language Expr State Obs Val]
    (GF : BundledGFunctors) extends WsatGS GF where
  /-- The state interpretation, given the remaining observations and the number of forked
  threads. -/
  stateInterp : State → List Obs → Nat → IProp GF
  /-- The postcondition of forked threads. -/
  forkPost : Val → IProp GF

attribute [instance] IrisGS.toWsatGS

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS Expr GF]

/-- The body of the weakest precondition (Rocq: `wp_pre`). -/
def wpPre (s : Stuckness) (wp : CoPset → Expr → (Val → IProp GF) → IProp GF) (E : CoPset)
    (e₁ : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(∀ (σ₁ : State) (κ κs : List Obs) (n : Nat),
    ι.stateInterp σ₁ (κ ++ κs) n -∗ gstep ∅ E ∅ iprop(
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ -∗
        |={∅,∅}=> ▷ |={∅,E}=> (ι.stateInterp σ₂ κs (efs.length + n) ∗
          wp E e₂ Φ ∗ [∗list] ef ∈ efs, wp ⊤ ef ι.forkPost)))

/-- Rocq: `wp_pre_contractive`. -/
instance wpPre_contractive (s : Stuckness) : Contractive (wpPre (ι := ι) s) where
  distLater_dist := by
    intro n wp wp' Hwp E e₁ Φ
    unfold wpPre
    cases toVal e₁
    case some _ => exact .rfl
    case none =>
      refine forall_ne fun σ₁ => forall_ne fun κ => forall_ne fun κs => forall_ne fun m => ?_
      refine wand_ne.ne .rfl ?_
      refine (gstep_ne _ _ _).ne ?_
      refine sep_ne.ne .rfl ?_
      refine forall_ne fun e₂ => forall_ne fun σ₂ => forall_ne fun efs => ?_
      refine wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine Contractive.distLater_dist fun k hk => ?_
      refine BIFUpdate.ne.ne ?_
      refine sep_ne.ne .rfl (sep_ne.ne (Hwp k hk _ _ _) ?_)
      exact BigSepL.bigSepL_dist fun _ => Hwp k hk _ _ _

/-- The weakest precondition of Transfinite Iris (Rocq: `wp_def`). -/
def wp (s : Stuckness) : CoPset → Expr → (Val → IProp GF) → IProp GF :=
  fixpoint (wpPre (ι := ι) s)

/-- Rocq: `wp_unfold`. -/
theorem wp_unfold (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    wp (ι := ι) s E e Φ = wpPre s (wp s) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold (wpPre (ι := ι) s).toContractiveHom) E) e) Φ

/-- The strong weakest precondition (Rocq: `swp_def`), written `SWP e at k @ s; E {{ Φ }}` in
Rocq: it takes exactly `k` logical steps before the next program step. -/
@[rocq_alias swp_def]
def swp (k : Nat) (s : Stuckness) (E : CoPset) (e₁ : Expr) (Φ : Val → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : State) (κ κs : List Obs) (n : Nat),
    ι.stateInterp σ₁ (κ ++ κs) n -∗ gstepN k ∅ E ∅ iprop(
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ -∗
        |={∅,∅}=> ▷ |={∅,E}=> (ι.stateInterp σ₂ κs (efs.length + n) ∗
          wp s E e₂ Φ ∗ [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)))

/-- Rocq: `wp_ne`. -/
theorem wp_ne (s : Stuckness) (E : CoPset) (e : Expr) {n : SI} {Φ Ψ : Val → IProp GF}
    (h : ∀ v, Φ v ≡{n}≡ Ψ v) : wp (ι := ι) s E e Φ ≡{n}≡ wp s E e Ψ := by
  induction n using instSI.lt_wf.induction generalizing E e Φ Ψ with
  | _ n IH =>
    rw [wp_unfold, wp_unfold]
    unfold wpPre
    cases toVal e
    case some v => exact BIFUpdate.ne.ne (h v)
    case none =>
      refine forall_ne fun σ₁ => forall_ne fun κ => forall_ne fun κs => forall_ne fun m => ?_
      refine wand_ne.ne .rfl ?_
      refine (gstep_ne _ _ _).ne ?_
      refine sep_ne.ne .rfl ?_
      refine forall_ne fun e₂ => forall_ne fun σ₂ => forall_ne fun efs => ?_
      refine wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine Contractive.distLater_dist fun k hk => ?_
      refine BIFUpdate.ne.ne ?_
      exact sep_ne.ne .rfl (sep_ne.ne (IH k hk _ _ fun v => (h v).lt hk) .rfl)

/-- Rocq: `wp_value'`. -/
theorem wp_value' (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (v : Val) :
    Φ v ⊢ wp (ι := ι) s E (v : Expr) Φ := by
  rw [wp_unfold]; unfold wpPre; rw [toVal_coe]
  exact fupd_intro

/-- Rocq: `wp_value_inv'`. -/
theorem wp_value_inv' (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (v : Val) :
    wp (ι := ι) s E (v : Expr) Φ ⊢ |={E}=> Φ v := by
  rw [wp_unfold]; unfold wpPre; rw [toVal_coe]

theorem stuckness_mono {s₁ s₂ : Stuckness} (hs : s₁ ≤ s₂) {c : Expr × State}
    (h : s₁.MaybeReducible c) : s₂.MaybeReducible c := by
  simp only [LE.le] at hs
  grind [cases Stuckness]

/-- Rocq: `wp_strong_mono`. -/
theorem wp_strong_mono {s₁ s₂ : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF}
    (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ wp (ι := ι) s₁ E₁ e Φ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ wp s₂ E₂ e Ψ := by
  iloeb as IH generalizing %e %Φ %Ψ %E₁ %E₂ %hE
  rw [wp_unfold, wp_unfold]
  iintro H HΦ
  unfold wpPre
  match toVal e with
  | none =>
    dsimp only
    iintro %σ₁ %κ %κs %n Hσ
    iapply gstep_fupd_left (E2 := E₁)
    imod fupd_mask_subseteq (PROP := IProp GF) hE with Hclose
    imodintro
    imod H $$ Hσ with ⟨%h, H⟩
    isplit
    · ipureintro
      exact stuckness_mono hs h
    · iintro %e₂ %σ₂ %efs %hstep
      imod H $$ %e₂ %σ₂ %efs %hstep with H
      imodintro
      inext
      imod H with ⟨Hσ, H, Hefs⟩
      imod Hclose
      imodintro
      iframe Hσ
      isplitr [Hefs]
      · iapply IH $$ %e₂ %Φ %Ψ %E₁ %E₂ %hE H HΦ
      · iapply BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %e' %_ H
        iapply IH $$ %e' %_ %_ %⊤ %_ %LawfulSet.subset_refl H
        iintro %v H
        imodintro
        iassumption
  | some v =>
    dsimp only
    imod fupd_mask_mono hE $$ H with h
    iapply HΦ $$ h

/-- Rocq: `fupd_wp`. -/
theorem fupd_wp {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> wp (ι := ι) s E e Φ) ⊢ wp s E e Φ := by
  rw [wp_unfold]
  unfold wpPre
  iintro H
  match toVal e with
  | some v =>
    dsimp only
    imod H
    iassumption
  | none =>
    dsimp only
    iintro %σ₁ %κ %κs %n Hσ
    iapply gstep_fupd_left (E2 := E)
    imod H
    imodintro
    iapply H $$ Hσ

/-- Rocq: `wp_fupd`. -/
theorem wp_fupd {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    wp (ι := ι) s E e (fun v => iprop(|={E}=> Φ v)) ⊢ wp s E e Φ := by
  iintro H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  iexact H

/-- Rocq: `wp_mono`. -/
theorem wp_mono {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF}
    (h : ∀ v, Φ v ⊢ Ψ v) : wp (ι := ι) s E e Φ ⊢ wp s E e Ψ := by
  iintro H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iapply h
  iexact H

/-- Rocq: `wp_mask_mono`. -/
theorem wp_mask_mono {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF}
    (hE : E₁ ⊆ E₂) : wp (ι := ι) s E₁ e Φ ⊢ wp s E₂ e Φ := by
  iintro H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) hE $$ H
  iintro %v H
  imodintro
  iexact H

/-- Rocq: `wp_stuck_mono`. -/
theorem wp_stuck_mono {s₁ s₂ : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}
    (hs : s₁ ≤ s₂) : wp (ι := ι) s₁ E e Φ ⊢ wp s₂ E e Φ := by
  iintro H
  iapply wp_strong_mono hs LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iexact H

/-- Rocq: `wp_frame_l`. -/
theorem wp_frame_l {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    R ∗ wp (ι := ι) s E e Φ ⊢ wp s E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, H⟩
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iframe

/-- Rocq: `wp_frame_r`. -/
theorem wp_frame_r {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    wp (ι := ι) s E e Φ ∗ R ⊢ wp s E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨H, HR⟩
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iframe

/-- Rocq: `wp_wand`. -/
theorem wp_wand {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    wp (ι := ι) s E e Φ ⊢ (∀ v, Φ v -∗ Ψ v) -∗ wp s E e Ψ := by
  iintro H HΦ
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iapply HΦ $$ H

/-- Rocq: `wp_value`. -/
theorem wp_value {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (v : Val) :
    Φ v ⊢ wp (ι := ι) s E (v : Expr) Φ := wp_value' s E Φ v

/-- Rocq: `wp_value_fupd'`. -/
theorem wp_value_fupd' {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (v : Val) :
    (|={E}=> Φ v) ⊢ wp (ι := ι) s E (v : Expr) Φ :=
  (fupd_mono (wp_value' s E Φ v)).trans fupd_wp

/-! ## The strong weakest precondition -/

/-- Rocq: `swp_strong_mono`. -/
theorem swp_strong_mono {k₁ k₂ : Nat} {s₁ s₂ : Stuckness} {E₁ E₂ : CoPset} {e : Expr}
    {Φ Ψ : Val → IProp GF} (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) (hk : k₁ ≤ k₂) :
    ⊢ swp (ι := ι) k₁ s₁ E₁ e Φ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ swp k₂ s₂ E₂ e Ψ := by
  iintro H HΦ
  unfold swp
  iintro %σ₁ %κ %κs %n Hσ
  iapply gstepN_mono hk
  iapply gstepN_fupd_left (E2 := E₁)
  imod fupd_mask_subseteq (PROP := IProp GF) hE with Hclose
  imodintro
  imod H $$ Hσ with ⟨%h, H⟩
  isplit
  · ipureintro
    exact stuckness_mono hs h
  · iintro %e₂ %σ₂ %efs %hstep
    imod H $$ %e₂ %σ₂ %efs %hstep with H
    imodintro
    inext
    imod H with ⟨Hσ, H, Hefs⟩
    imod Hclose
    imodintro
    iframe Hσ
    isplitr [Hefs]
    · iapply wp_strong_mono hs hE $$ H HΦ
    · iapply BigSepL.bigSepL_impl $$ Hefs
      iintro !> %i %e' %_ H
      iapply wp_strong_mono hs LawfulSet.subset_refl $$ H
      iintro %v H
      imodintro
      iassumption

/-- Rocq: `fupd_swp`. -/
theorem fupd_swp {k : Nat} {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> swp (ι := ι) k s E e Φ) ⊢ swp k s E e Φ := by
  unfold swp
  iintro H %σ₁ %κ %κs %n Hσ
  iapply gstepN_fupd_left (E2 := E)
  imod H
  imodintro
  iapply H $$ Hσ

/-- Rocq: `swp_fupd`. -/
theorem swp_fupd {k : Nat} {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    swp (ι := ι) k s E e (fun v => iprop(|={E}=> Φ v)) ⊢ swp k s E e Φ := by
  iintro H
  iapply swp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl (Nat.le_refl k) $$ H
  iintro %v H
  iexact H

/-- Rocq: `swp_mono`. -/
theorem swp_mono {k : Nat} {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF}
    (h : ∀ v, Φ v ⊢ Ψ v) : swp (ι := ι) k s E e Φ ⊢ swp k s E e Ψ := by
  iintro H
  iapply swp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl (Nat.le_refl k) $$ H
  iintro %v H
  imodintro
  iapply h
  iexact H

/-- Rocq: `swp_wp`. -/
theorem swp_wp {k : Nat} {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}
    (he : toVal e = none) : swp (ι := ι) k s E e Φ ⊢ wp s E e Φ := by
  rw [wp_unfold]
  unfold wpPre swp
  rw [he]
  dsimp only
  iintro H %σ₁ %κ %κs %n Hσ
  iapply gstepN_gstep k
  iapply H $$ Hσ

/-- Rocq: `swp_step`. -/
theorem swp_step {k : Nat} {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    ▷ swp (ι := ι) k s E e Φ ⊢ swp (k + 1) s E e Φ := by
  unfold swp
  iintro H %σ₁ %κ %κs %n Hσ
  iapply gstepN_later k (by simp)
  inext
  iapply H $$ Hσ

/-! ## Binding -/

/-- Rocq: `wp_bind` and `wp_bind_inv`. -/
theorem wp_bind_iff (K : Expr → Expr) [κ : Language.Context K] {s : Stuckness} {E : CoPset}
    {e : Expr} {Φ : Val → IProp GF} :
    wp (ι := ι) s E e (fun v => wp s E (K (v : Expr)) Φ) ⊣⊢ wp s E (K e) Φ := by
  iloeb as IH generalizing %E %e %Φ
  rewrite (occs := [1]) [wp_unfold]
  simp only [wpPre]
  match h : toVal e with
  | some v =>
    dsimp only
    rw [ToVal.coe_of_toVal_eq_some h]
    isplit
    · iintro H; iapply fupd_wp $$ H
    · iintro H; imodintro; iexact H
  | none =>
    rw [wp_unfold]
    dsimp only
    simp only [wpPre, κ.toVal_eq_none_fill h]
    isplit <;>
      (iintro H %σ₁ %κ' %κs %n Hσ; imod H $$ [$] with ⟨%_, H⟩; isplit)
    · ipureintro; grind only [cases Stuckness, Language.Context.reducible_fill]
    · iintro %e₂ %σ₂ %efs %HKstep
      obtain ⟨e₂', rfl, Hstep⟩ := κ.primStep_fill_inv h HKstep
      imod H $$ %e₂' %σ₂ %efs %Hstep with H
      imodintro
      inext
      imod H with ⟨$, H, $⟩
      imodintro
      iapply IH $$ H
    · ipureintro; grind only [cases Stuckness, Language.Context.reducible_fill_inv]
    · iintro %e₂ %σ₂ %efs %Hstep
      imod H $$ %(K e₂) %σ₂ %efs %(κ.primStep_fill Hstep) with H
      imodintro
      inext
      imod H with ⟨$, H, $⟩
      imodintro
      iapply IH $$ H

/-- Rocq: `wp_bind`. -/
theorem wp_bind (K : Expr → Expr) [Language.Context K] {s : Stuckness} {E : CoPset} {e : Expr}
    {Φ : Val → IProp GF} :
    wp (ι := ι) s E e (fun v => wp s E (K (v : Expr)) Φ) ⊢ wp s E (K e) Φ := (wp_bind_iff (ι := ι) K).1

/-- Rocq: `wp_bind_inv`. -/
theorem wp_bind_inv (K : Expr → Expr) [Language.Context K] {s : Stuckness} {E : CoPset} {e : Expr}
    {Φ : Val → IProp GF} :
    wp (ι := ι) s E (K e) Φ ⊢ wp (ι := ι) s E e (fun v => wp s E (K (v : Expr)) Φ) :=
  (wp_bind_iff (ι := ι) K).2

/-! ## Atomic expressions -/

/-- Rocq: `wp_atomic`. -/
theorem wp_atomic {E₁ E₂ : CoPset} {e : Expr} {s : Stuckness} {Φ : Val → IProp GF}
    [hat : Language.Atomic (Val := Val) .StronglyAtomic e] :
    (|={E₁,E₂}=> wp (ι := ι) s E₂ e (fun v => iprop(|={E₂,E₁}=> Φ v))) ⊢ wp s E₁ e Φ := by
  rw [wp_unfold, wp_unfold]
  unfold wpPre
  match he : toVal e with
  | some v =>
    dsimp only
    iintro H
    imod H
    imod H
    iexact H
  | none =>
    dsimp only
    iintro H %σ₁ %κ %κs %n Hσ
    iapply gstep_fupd_left (E2 := E₂)
    imod H
    imodintro
    imod H $$ Hσ with ⟨$, H⟩
    iintro %e₂ %σ₂ %efs %hstep
    imod H $$ %e₂ %σ₂ %efs %hstep with H
    imodintro
    inext
    imod H with ⟨Hσ, H, Hefs⟩
    have hv := hat.atomic hstep
    simp only at hv
    obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp hv
    rw [wp_unfold]
    unfold wpPre
    rw [hv₂]
    dsimp only
    imod H
    imod H
    imodintro
    iframe
    iapply (show Φ v₂ ⊢ wp (ι := ι) s E₁ e₂ Φ by
      rw [wp_unfold]; unfold wpPre; rw [hv₂]; exact fupd_intro)
    iexact H

/-- Rocq: `swp_atomic`. -/
theorem swp_atomic {k : Nat} {E₁ E₂ : CoPset} {e : Expr} {s : Stuckness} {Φ : Val → IProp GF}
    [hat : Language.Atomic (Val := Val) .StronglyAtomic e] :
    (|={E₁,E₂}=> swp (ι := ι) k s E₂ e (fun v => iprop(|={E₂,E₁}=> Φ v))) ⊢ swp k s E₁ e Φ := by
  unfold swp
  iintro H %σ₁ %κ %κs %n Hσ
  iapply gstepN_fupd_left (E2 := E₂)
  imod H
  imodintro
  imod H $$ Hσ with ⟨$, H⟩
  iintro %e₂ %σ₂ %efs %hstep
  imod H $$ %e₂ %σ₂ %efs %hstep with H
  imodintro
  inext
  imod H with ⟨Hσ, H, Hefs⟩
  have hv := hat.atomic hstep
  simp only at hv
  obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp hv
  rw [wp_unfold, wp_unfold]
  unfold wpPre
  rw [hv₂]
  dsimp only
  imod H
  imod H
  imodintro
  iframe

end Iris.Transfinite
