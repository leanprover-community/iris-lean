/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.Fixpoint
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProofMode

namespace Iris

open ProgramLogic Language Language.Notation Std OFE BI

@[expose] public section

/-!
# Total weakest preconditions

This file provides the core definition and selected rules for total WP. Total WP
uses a least fixed point without a later modality and permits only
observation-free reductions. Further Iris-Rocq rules can be ported separately.
-/

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

/-- The stuckness-dependent reducibility condition for total WP. -/
abbrev Stuckness.MaybeReducibleNoObs : Stuckness → Expr × State → Prop
  | .NotStuck, ρ => PrimStep.ReducibleNoObs ρ
  | .MaybeStuck, _ => True

namespace twp

local instance : OFE CoPset := OFE.ofDiscrete _
local instance : OFE Expr := OFE.ofDiscrete _
local instance : OFE Val := OFE.ofDiscrete _

namespace Internal

abbrev Args (Expr Val : Type _) (GF : BundledGFunctors) :=
  CoPset × Expr × (Val → IProp GF)

end Internal

@[rocq_alias twp_pre]
def pre (s : Stuckness) (twp : CoPset → Expr → (Val → IProp GF) → IProp GF) (E : CoPset)
    (e₁ : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop% |={E}=> Φ v
  | none => iprop% ∀ (σ₁ : State) (ns : Nat) (obs : List Obs) (nt : Nat),
    stateInterp σ₁ ns obs nt ={E,∅}=∗
    ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
    ∀ (κ : List Obs) e₂ σ₂ eₜ,
      ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
      ⌜κ = []⌝ ∗
      stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
      twp E e₂ Φ ∗
      [∗list] e' ∈ eₜ, twp ⊤ e' ι.forkPost

namespace Internal

def pre' (s : Stuckness) (X : Args Expr Val GF → IProp GF) : Args Expr Val GF → IProp GF
  | (E, e, Φ) => pre s (fun E e Φ => X (E, e, Φ)) E e Φ

end Internal

@[rocq_alias twp_pre_mono]
theorem pre_mono (s : Stuckness) (X Y : CoPset → Expr → (Val → IProp GF) → IProp GF) :
    ⊢ □ (∀ E e Φ, X E e Φ -∗ Y E e Φ) -∗
      ∀ E e Φ, pre s X E e Φ -∗ pre s Y E e Φ := by
  iintro #H %E %e %Φ Hpre
  unfold pre
  cases toVal e with
  | some => itrivial
  | none =>
      iintro %σ₁ %ns %obs %nt Hσ
      imod Hpre $$ Hσ with ⟨%Hred, Hstep⟩
      iframe %Hred
      iintro !> %κ %e₂ %σ₂ %eₜ Hprim
      imod Hstep $$ Hprim with ⟨%hκ, Hσ, He₂, Hefs⟩
      iframe %hκ Hσ
      isplitl [He₂]
      · iapply H $$ He₂
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> !> %k %ef %Hef Hef
        iapply H $$ Hef

namespace Internal

instance pre'_mono (s : Stuckness) : BIMonoPred (pre' (ι := ι) s) where
  mono_pred := by
    intro X Y _ _
    iintro #HXY %⟨E, e, Φ⟩ HX
    unfold pre'
    iapply pre_mono s (fun E e Φ => X (E, e, Φ)) (fun E e Φ => Y (E, e, Φ)) $$ [] [$]
    iintro !> %E %e %Φ H
    iapply HXY $$ H
  mono_pred_ne.ne {n} := fun ⟨E₁, e₁, Φ₁⟩ ⟨E₂, e₂, Φ₂⟩ ⟨hE, he, hΦ⟩ =>
    (show E₁ = E₂ from hE) ▸ (show e₁ = e₂ from he) ▸ by
    simp only [pre', pre]
    match toVal e₁ with
    | some v => exact BIFUpdate.ne.ne (hΦ v)
    | none =>
      refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ =>
        wand_ne.ne .rfl <| BIFUpdate.ne.ne <| sep_ne.ne .rfl <| forall_ne fun _ => forall_ne fun e =>
        forall_ne fun _ => forall_ne fun _ => wand_ne.ne .rfl <| BIFUpdate.ne.ne <|
        sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne ?_ .rfl
      exact NonExpansive.ne (show (E₁, e, Φ₁) ≡{n}≡ (E₁, e, Φ₂) from ⟨.rfl, .rfl, hΦ⟩)

def get (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  bi_least_fixpoint (pre' s) (E, e, Φ)

end Internal

instance instTotalWp : TotalWp (IProp GF) Expr Val Stuckness where
  totalWp := Internal.get

section Rules

@[rocq_alias twp_unfold]
theorem unfold {s E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊣⊢ pre s (TotalWp.totalWp s) E e Φ :=
  BI.equiv_iff.1 (least_fixpoint_unfold (Internal.pre' s))

@[rocq_alias twp_ind]
theorem induction (s : Stuckness) (Ψ : CoPset → Expr → (Val → IProp GF) → IProp GF)
    [HΨ : NonExpansive (fun x : Internal.Args Expr Val GF => Ψ x.1 x.2.1 x.2.2)] :
    (⊢ □ (∀ E e Φ, pre s (fun E e Φ => iprop(Ψ E e Φ ∧ WP e @ s ; E [{ Φ }])) E e Φ -∗ Ψ E e Φ)) →
    ⊢ ∀ E e Φ, WP e @ s ; E [{ Φ }] -∗ Ψ E e Φ := fun H => by
  iintro %E %e %Φ
  change ⊢ bi_least_fixpoint (Internal.pre' s) (E, e, Φ) -∗ Ψ E e Φ
  iapply least_fixpoint_ind (F := Internal.pre' s) (Φ := fun x => Ψ x.1 x.2.1 x.2.2) $$ []
  iintro !> %⟨E, e, Φ⟩
  simp only [Internal.pre', TotalWp.totalWp, Internal.get] at H ⊢
  iapply H

@[rocq_alias twp_ne]
instance ne {s : Stuckness} {E} {e : Expr} :
    NonExpansive (TotalWp.totalWp (PROP := IProp GF) s E e) where
  ne {n Φ₁ Φ₂} HΦ := NonExpansive.ne (f := bi_least_fixpoint (Internal.pre' s))
    (show (E, e, Φ₁) ≡{n}≡ (E, e, Φ₂) from ⟨.rfl, .rfl, HΦ⟩)

@[rocq_alias twp_value_fupd']
theorem value_fupd' {s : Stuckness} {E} {Φ : Val → IProp GF} {v : Val} :
    WP (v : Expr) @ s ; E [{ Φ }] ⊣⊢ |={E}=> Φ v := by
  simp [unfold.to_eq, pre, toVal_coe]

@[rocq_alias twp_value_fupd]
theorem value_fupd {s : Stuckness} {E} {e : Expr} {v : Val} {Φ : Val → IProp GF} (h : e = v) :
    WP e @ s ; E [{ Φ }] ⊣⊢ |={E}=> Φ v := h ▸ value_fupd'

@[rocq_alias twp_strong_mono]
theorem strong_mono {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr}
    {Φ Ψ : Val → IProp GF} (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ WP e @ s₁ ; E₁ [{ Φ }] -∗
      (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ [{ Ψ }] := by
  let Pred := fun (E : CoPset) (e : Expr) (Φ : Val → IProp GF) => iprop%
    ∀ E₂ Ψ, ⌜E ⊆ E₂⌝ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ [{ Ψ }]
  have hPred : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) :=
    ⟨fun _ _ _ ⟨hE, he, hΦ⟩ => hE ▸ he ▸ forall_ne fun _ => forall_ne fun _ => wand_ne.ne .rfl <|
      wand_ne.ne (forall_ne fun v => wand_ne.ne (hΦ v) .rfl) .rfl⟩
  iintro H HΦ
  iapply induction s₁ Pred $$ H [//] [$]
  · iintro !> %E %e₁ %Φ₁ IH %E' %Ψ' %hE'
    simp only [(unfold (s := s₂) (E := E') (e := e₁) (Φ := Ψ')).to_eq, pre]
    cases hval : toVal e₁
    all_goals iintro Hpost
    next =>
      iintro %σ₁ %ns %obs %nt Hσ
      imod fupd_mask_subseteq hE' with Hclose
      imod IH $$ Hσ with ⟨%Hred, Hstep⟩
      have Hred' : s₂.MaybeReducibleNoObs (e₁, σ₁) := by
        simp only [LE.le] at hs
        grind [cases Stuckness]
      iframe %Hred'
      iintro !> %κ %e₂ %σ₂ %eₜ Hprim
      imod Hstep $$ Hprim with ⟨%hκ, Hσ, ⟨IH₂, -⟩, Hefs⟩
      imod Hclose
      iframe %hκ Hσ
      isplitl [IH₂ Hpost]
      · iapply IH₂ $$ [//] Hpost
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> !> %k %ef %Hef ⟨IHef, -⟩
        iapply IHef $$ %⊤ %ι.forkPost %LawfulSet.subset_refl
        iintro %v $
    next =>
      imod fupd_mask_mono hE' $$ IH with HΦv
      iapply Hpost $$ HΦv

private theorem strong_mono_with {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr} {Φ Ψ : Val → IProp GF}
    (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) (H : ∀ v, ⊢ Φ v ={E₂}=∗ Ψ v) :
    WP e @ s₁ ; E₁ [{ Φ }] ⊢ WP e @ s₂ ; E₂ [{ Ψ }] :=
  sep_elim_emp_valid_right (forall_intro H) (wand_elim (wand_entails (strong_mono hs hE)))

@[rocq_alias fupd_twp]
theorem fupd_twp {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> WP e @ s ; E [{ Φ }]) ⊢ WP e @ s ; E [{ Φ }] := by
  simp only [(unfold (e := e)).to_eq, pre]
  iintro H
  cases toVal e
  · iintro %σ %ns %obs %nt Hσ
    imod H $$ Hσ with $
  · imod H with $

@[rocq_alias twp_fupd]
theorem twp_fupd {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ v, |={E}=> Φ v }] ⊢ WP e @ s ; E [{ Φ }] :=
  strong_mono_with (Std.IsPreorder.le_refl _) LawfulSet.subset_refl fun _ => BI.wand_rfl

@[rocq_alias twp_atomic]
theorem atomic {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}
    {Φ : Val → IProp GF} [hatom : Language.Atomic ↑s e] :
    (|={E₁,E₂}=> WP e @ s ; E₂ [{ v, |={E₂,E₁}=> Φ v }]) ⊢ WP e @ s ; E₁ [{ Φ }] := by
  simp only [(unfold (e := e)).to_eq, pre]
  iintro H
  cases he : toVal e with
  | some v => icases H with > >$
  | none =>
    iintro %σ₁ %ns %obs %nt Hσ
    imod H $$ Hσ with >⟨$, Hstep⟩
    iintro !> %κ %e₂ %σ₂ %eₜ %Hprim
    cases s
    · imod Hstep $$ %κ %e₂ %σ₂ %eₜ %Hprim with ⟨%hκ, Hσ, He₂, Hefs⟩
      cases he₂ : toVal e₂ with
      | some v₂ =>
        imod (value_fupd (ToVal.coe_of_toVal_eq_some he₂).symm).mp $$ He₂ with >He₂
        iframe %hκ Hσ Hefs
        iapply (value_fupd (ToVal.coe_of_toVal_eq_some he₂).symm).mpr $$ He₂
      | none =>
        simp only [(unfold (e := e₂)).to_eq, pre, he₂]
        imod He₂ $$ %σ₂ %(ns + 1) %obs %(nt + eₜ.length) Hσ with ⟨%Hred₂, _⟩
        exact ((not_reducible_iff_irreducible.mpr (hatom.atomic Hprim)) (reducible_of_reducibleNoObs Hred₂)).elim
    · imod Hstep $$ [//] with ⟨%hκ, Hσ, He₂, Hefs⟩
      have ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp (hatom.atomic Hprim)
      imod (value_fupd (ToVal.coe_of_toVal_eq_some hv₂).symm).mp $$ He₂ with >He₂
      iframe %hκ Hσ Hefs
      iapply (value_fupd (ToVal.coe_of_toVal_eq_some hv₂).symm).mpr $$ He₂

@[rocq_alias twp_bind]
theorem bind (K : Expr → Expr) [ctx : Language.Context K]
    {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    TotalWp.totalWp s E e
      (fun v : Val => iprop(WP (K v) @ s ; E [{ Φ }])) ⊢ WP (K e) @ s ; E [{ Φ }] := by
  let Pred := fun (E : CoPset) (e : Expr) (Ψ : Val → IProp GF) => iprop%
    ∀ Φ, (∀ v, Ψ v -∗ WP (K v) @ s ; E [{ Φ }]) -∗
      WP (K e) @ s ; E [{ Φ }]
  letI : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) :=
    ⟨fun _ _ _ ⟨hE, he, hΨ⟩ => hE ▸ he ▸ BI.forall_ne fun _ =>
      BI.wand_ne.ne (BI.forall_ne fun v => BI.wand_ne.ne (hΨ v) .rfl) .rfl⟩
  iintro H
  iapply induction s Pred $$ H
  · iintro !> %E %e %Ψ
    cases he : toVal e
    all_goals
      simp only [pre, he]
      iintro Hpre %Φ Hcont
    next =>
      simp only [(unfold (e := K e)).to_eq, pre, ctx.toVal_eq_none_fill he]
      iintro %σ₁ %ns %obs %nt Hσ
      imod Hpre $$ Hσ with ⟨%Hred, Hstep⟩
      have Hred' : s.MaybeReducibleNoObs (K e, σ₁) := by grind [Language.Context.reducibleNoObs_fill]
      iframe %Hred'
      iintro !> %κ %e₂ %σ₂ %eₜ %HKstep
      obtain ⟨e₂', rfl, Hprim⟩ := ctx.primStep_fill_inv he HKstep
      imod Hstep $$ [//] with ⟨%hκ, Hσ, ⟨IH, -⟩, Hefs⟩
      iframe %hκ Hσ
      isplitl [IH Hcont]
      · iapply IH $$ Hcont
      · iapply BI.BigSepL.bigSepL_mono_of_forall BI.and_elim_r $$ Hefs
    next v =>
      rw [← (ToVal.coe_of_toVal_eq_some he)]
      ispecialize Hcont $$ %v
      iapply (fupd_wand_left (P := Ψ v)).trans fupd_twp $$ [$]
  · iintro %_ $

@[rocq_alias twp_bind_inv]
theorem bind_inv (K : Expr → Expr) [ctx : Language.Context K]
    {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    WP (K e) @ s ; E [{ Φ }] ⊢
      TotalWp.totalWp s E e (fun v : Val => iprop(WP (K v) @ s ; E [{ Φ }])) := by
  let Pred := fun (E : CoPset) (e' : Expr) (Φ : Val → IProp GF) => iprop%
    ∀ e, ⌜e' = K e⌝ -∗
      TotalWp.totalWp s E e (fun v : Val => iprop(WP (K v) @ s ; E [{ Φ }]))
  letI : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) :=
    ⟨fun _ _ _ ⟨hE, he, hΦ⟩ => hE ▸ he ▸ BI.forall_ne fun _ =>
      BI.wand_ne.ne .rfl (NonExpansive.ne fun _ => NonExpansive.ne hΦ)⟩
  iintro H
  iapply induction s Pred $$ H %e %rfl
  iintro !> %E %e' %Φ IH %e %heq
  rw [heq, unfold.to_eq]
  cases he : toVal e with
  | some v =>
      ihave IHfold : iprop(WP (K e) @ s ; E [{ Φ }]) $$ [IH]
      · rw [unfold.to_eq]
        iapply pre_mono s (fun E e Φ => iprop(Pred E e Φ ∧ WP e @ s ; E [{ Φ }])) $$ [] %E %(K e) %Φ IH
        iintro !> %E %e %Φ ⟨-, $⟩
      simp only [pre, ← ToVal.coe_of_toVal_eq_some he, toVal_coe]
      itrivial
  | none =>
      simp only [pre, he, ctx.toVal_eq_none_fill he]
      iintro %σ₁ %ns %obs %nt Hσ
      imod IH $$ Hσ with ⟨%Hred, Hstep⟩
      have Hred' : s.MaybeReducibleNoObs (e, σ₁) := by grind [Language.Context.reducibleNoObs_fill_inv]
      iframe %Hred'
      iintro !> %κ %e₂ %σ₂ %eₜ %Hprim
      imod Hstep $$ %_ %_ %_ %_ %(ctx.primStep_fill Hprim) with ⟨$, $, ⟨IH₂, -⟩, Hefs⟩
      isplitl [IH₂]
      · iapply IH₂ $$ %e₂ %rfl
      · iapply BI.BigSepL.bigSepL_mono_of_forall BI.and_elim_r $$ Hefs

@[rocq_alias twp_mono]
theorem mono {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF}
    (H : ∀ v, Φ v ⊢ Ψ v) :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ Ψ }] :=
  strong_mono_with (Std.IsPreorder.le_refl _) LawfulSet.subset_refl fun v => entails_wand ((H v).trans fupd_intro)

@[rocq_alias twp_stuck_mono]
theorem stuck_mono {s₁ s₂ : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} (H : s₁ ≤ s₂) :
    WP e @ s₁ ; E [{ Φ }] ⊢ WP e @ s₂ ; E [{ Φ }] :=
  strong_mono_with H LawfulSet.subset_refl fun _ => BI.entails_wand fupd_intro

@[rocq_alias twp_stuck_weaken]
theorem stuck_weaken {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ E ? [{ Φ }] :=
  stuck_mono Stuckness.le_MaybeStuck

@[rocq_alias twp_mask_mono]
theorem mask_mono {s : Stuckness} {E₁ E₂} {e : Expr} {Φ : Val → IProp GF}
    (H : E₁ ⊆ E₂) :
    WP e @ s ; E₁ [{ Φ }] ⊢ WP e @ s ; E₂ [{ Φ }] :=
  strong_mono_with (Std.IsPreorder.le_refl _) H fun _ => BI.entails_wand fupd_intro

@[rocq_alias twp_value']
theorem value' {s : Stuckness} {E} {v : Val} {Φ : Val → IProp GF} :
    Φ v ⊢ WP (v : Expr) @ s ; E [{ Φ }] := fupd_intro.trans value_fupd'.mpr

@[rocq_alias twp_value]
theorem value {s : Stuckness} {E} {e : Expr} {v : Val} {Φ : Val → IProp GF} (h : e = v) :
    Φ v ⊢ WP e @ s ; E [{ Φ }] := h ▸ value'

@[rocq_alias twp_frame_l]
theorem frame_l {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} :
    R ∗ WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ v, R ∗ Φ v }] :=
  (BI.sep_mono_left (BI.forall_intro fun _ => BI.wand_intro fupd_intro)).trans <|
    BI.wand_elim_swap (BI.wand_entails (strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl))

@[rocq_alias twp_frame_r]
theorem frame_r {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    WP e @ s ; E [{ Φ }] ∗ R ⊢ WP e @ s ; E [{ v, Φ v ∗ R }] :=
  BI.sep_comm.mp.trans (frame_l.trans (mono fun _ => BI.sep_comm.mp))

@[rocq_alias twp_wand]
theorem wand {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊢
      (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E [{ Ψ }] :=
  BI.wand_intro <| frame_r.trans <| mono fun v => (BI.sep_mono_right (BI.forall_elim v)).trans BI.wand_elim_right

@[rocq_alias twp_wand_l]
theorem wand_l {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF} :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ Ψ }] :=
  BI.wand_elim_swap wand

@[rocq_alias twp_wand_r]
theorem wand_r {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s ; E [{ Ψ }] :=
  BI.wand_elim wand

@[rocq_alias twp_frame_wand]
theorem frame_wand {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    R ⊢ (WP e @ s ; E [{ v, R -∗ Φ v }]) -∗ WP e @ s ; E [{ Φ }] :=
  BI.wand_intro_left (frame_r.trans (mono fun _ => BI.wand_elim_left))

@[rocq_alias twp_wp]
theorem to_wp {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E {{ Φ }} := by
  iloeb as IH generalizing %E %e %Φ
  simp only [(wp_unfold (e := e)).to_eq, (unfold (e := e)).to_eq, wp.pre, pre]
  cases hval : toVal e
  case some v => iintro $
  case none =>
    iintro H %σ %ns %κ %κs %nt Hσ
    imod H $$ Hσ with ⟨%Hred, H⟩
    have Hred' : s.MaybeReducible (e, σ) := by grind
    iframe %Hred'
    iintro !> %e₂ %σ₂ %eₜ %Hstep _
    iapply step_fupdN_intro Std.LawfulSet.empty_subset
    iintro !>
    imod H $$ %κ %e₂ %σ₂ %eₜ %Hstep with ⟨%⟨⟩, Hσ, He₂, Hefs⟩
    simp only [List.nil_append]
    iframe Hσ
    isplitl [He₂]
    · iapply IH $$ He₂
    · iapply BI.BigSepL.bigSepL_impl $$ Hefs
      iintro !> %k %ef %Hef !>Hef
      iapply IH $$ Hef

section ProofMode

open ProofMode

variable {s : Stuckness} {E E₁ E₂ : CoPset} {e : Expr}
variable {Φ Ψ : Val → IProp GF} {P R : IProp GF}

@[rocq_alias frame_twp]
instance frameTwp {p : Bool} [H : ∀ v, FrameInstantiateExistDisabled p R (Φ v) (Ψ v)] :
    Frame p R (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Ψ }]) where
  frame := frame_l.trans (mono fun v => (H v).frame_instantiatiate_exist_disabled.frame)

-- Iris-Rocq reuses the module-qualified name `is_except_0_wp` here; that alias
-- is already assigned to partial WP in Lean, so this instance is left unaliased.
instance isExcept0Twp : IsExcept0 (WP e @ s ; E [{ Φ }]) where
  is_except0 := (BI.except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_twp)

@[rocq_alias elim_modal_fupd_twp]
instance (priority := default + 10) elimModalFupdTwp p :
    ElimModal True p io false iprop(|={E}=> P) P (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Φ }]) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans (fupd_wand_right.trans fupd_twp)

@[rocq_alias elim_modal_bupd_twp]
instance elimModalBupdTwp p :
    ElimModal True p io false iprop(|==> P) P (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Φ }]) where
  elim_modal := fun ⟨⟩ =>
    (BI.sep_mono_left (BI.intuitionisticallyIf_mono (BIUpdateFUpdate.fupd_of_bupd (E := E)))).trans
      (elimModalFupdTwp _ |>.elim_modal ⟨⟩ (io := io))

/-- The same diagnostic as partial WP: changing masks through a non-atomic
TWP goal requires an explicit leading update. -/
@[rocq_alias elim_modal_fupd_twp_wrong_mask]
instance elimModalFupdTwp_wrongMask :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
    Use `iapply twp.fupd_twp; imod (fupd_mask_subseteq E₂)` to adjust the mask of your goal to `E₂`")
      p io false iprop(|={E₂}=> P) iprop(False)
      (WP e @ s ; E₁ [{ Φ }]) iprop(False) where
  elim_modal := nofun

@[rocq_alias elim_modal_fupd_twp_atomic]
instance elimModalFupdTwpAtomic :
    ElimModal (Language.Atomic ↑s e) p io false iprop(|={E₁,E₂}=> P) P
      (WP e @ s ; E₁ [{ Φ }]) (WP e @ s ; E₂ [{ v, |={E₂,E₁}=> Φ v }]) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans (fupd_wand_right.trans atomic)

@[rocq_alias elim_modal_fupd_twp_atomic_wrong_mask]
instance elimModalFupdTwpAtomic_wrongMask :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
    Use `iapply twp.fupd_twp; imod (fupd_mask_subseteq E₂)` to adjust the mask of your goal to `E₂`")
      p io false iprop(|={E₁,E₂}=> P) iprop(False)
      (WP e @ s ; E₁ [{ Φ }]) iprop(False) where
  elim_modal := nofun

end ProofMode

end Rules
end twp
end
end Iris
