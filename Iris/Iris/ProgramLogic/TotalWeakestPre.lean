/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Fornet, Zongyuan Liu
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

Total WP uses a least fixed point without a later modality and permits only
observation-free reductions.
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

abbrev pre' (s : Stuckness) (X : Args Expr Val GF → IProp GF) : Args Expr Val GF → IProp GF
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
      imod Hpre $$ Hσ with ⟨$, Hstep⟩
      iintro !> %κ %e₂ %σ₂ %eₜ Hprim
      imod Hstep $$ Hprim with ⟨%hκ, Hσ, He₂, Hefs⟩
      iframe %hκ Hσ
      isplitl [He₂]
      · iapply H $$ He₂
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> !> %k %ef %Hef Hef
        iapply H $$ Hef

namespace Internal

@[rocq_alias twp_pre_mono']
instance pre'_mono (s : Stuckness) : BIMonoPred (pre' (ι := ι) s) where
  mono_pred := by
    intro X Y _ _
    iintro #HXY %⟨E, e, Φ⟩ HX
    unfold pre'
    iapply pre_mono $$ [] [$]
    iintro !> %E %e %Φ H
    iapply HXY $$ H
  mono_pred_ne.ne {n} := fun ⟨E₁, e₁, Φ₁⟩ ⟨E₂, e₂, Φ₂⟩ ⟨hE, he, hΦ⟩ => by
    obtain rfl := show E₁ = E₂ from hE
    obtain rfl := show e₁ = e₂ from he
    simp only [pre', pre]
    match toVal e₁ with
    | some v => exact BIFUpdate.ne.ne (hΦ v)
    | none =>
      refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
      refine wand_ne.ne .rfl <| BIFUpdate.ne.ne <| sep_ne.ne .rfl ?_
      refine forall_ne fun _ => forall_ne fun e => forall_ne fun _ => forall_ne fun _ => ?_
      refine wand_ne.ne .rfl <| BIFUpdate.ne.ne <| sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne ?_ .rfl
      refine NonExpansive.ne ?_
      exact ⟨.rfl, .rfl, hΦ⟩

@[rocq_alias twp']
def get (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  bi_least_fixpoint (pre' s) (E, e, Φ)

#rocq_ignore twp_aux "Not needed"
#rocq_ignore twp_def "Not needed"
#rocq_ignore twp_unseal "Not needed"

end Internal

instance instTotalWp : TotalWp (IProp GF) Expr Val Stuckness where
  totalWp := Internal.get

section Rules

@[rocq_alias twp_unfold]
theorem unfold {s E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊣⊢ pre s (TotalWp.totalWp s) E e Φ :=
  equiv_iff.mp (least_fixpoint_unfold (Internal.pre' s))

@[rocq_alias twp_ind]
theorem induction (s : Stuckness) (Ψ : CoPset → Expr → (Val → IProp GF) → IProp GF)
    [HΨ : NonExpansive (fun x : Internal.Args Expr Val GF => Ψ x.1 x.2.1 x.2.2)] :
    □ (∀ e E Φ, pre s (fun E e Φ => iprop(Ψ E e Φ ∧ WP e @ s ; E [{ Φ }])) E e Φ -∗ Ψ E e Φ) -∗
    ∀ e E Φ, WP e @ s ; E [{ Φ }] -∗ Ψ E e Φ := by
  iintro #IH %e %E %Φ
  isimp only [TotalWp.totalWp, Internal.get]
  iapply least_fixpoint_ind (F := Internal.pre' s) (Φ := fun x => Ψ x.1 x.2.1 x.2.2) $$ []
  iintro !> %⟨_, _, _⟩
  isimp only [TotalWp.totalWp,Internal.get] at IH
  iapply IH

@[rocq_alias twp_ne]
instance ne {s : Stuckness} {E} {e : Expr} :
    NonExpansive (TotalWp.totalWp (PROP := IProp GF) s E e) where
  ne {n Φ₁ Φ₂} HΦ := by
    refine NonExpansive.ne (f := bi_least_fixpoint (Internal.pre' s)) ?_
    exact ⟨.rfl, .rfl, HΦ⟩

@[rocq_alias twp_value_fupd']
theorem value_fupd' {s : Stuckness} {E} {Φ : Val → IProp GF} {v : Val} :
    WP (v : Expr) @ s ; E [{ Φ }] ⊣⊢ |={E}=> Φ v := by
  simp [unfold.to_eq, pre]

@[rocq_alias twp_value_fupd]
theorem value_fupd {s : Stuckness} {E} {e : Expr} {v : Val} {Φ : Val → IProp GF} (h : IntoVal e v) :
    WP e @ s ; E [{ Φ }] ⊣⊢ |={E}=> Φ v := by
    obtain ⟨rfl⟩ := h
    exact value_fupd'

@[rocq_alias twp_strong_mono]
theorem strong_mono {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr} {Φ Ψ : Val → IProp GF}
  (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    WP e @ s₁ ; E₁ [{ Φ }] -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ [{ Ψ }] := by
  let Pred := fun (E : CoPset) (e : Expr) (Φ : Val → IProp GF) => iprop%
    ∀ E₂ Ψ, ⌜E ⊆ E₂⌝ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ [{ Ψ }]
  have hPred : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) :=
    ⟨fun _ _ _ ⟨hE, he, hΦ⟩ => hE ▸ he ▸ forall_ne fun _ => forall_ne fun _ => wand_ne.ne .rfl <|
      wand_ne.ne (forall_ne fun v => wand_ne.ne (hΦ v) .rfl) .rfl⟩
  iintro H HΦ
  iapply induction s₁ Pred $$ [] H [//] [$]
  · iintro !> %e₁ %E %Φ₁ IH %E' %Ψ' %hE' Hpost
    simp only [(unfold (e := e₁)).to_eq, pre]
    cases hval : toVal e₁
    · iintro %σ₁ %ns %obs %nt Hσ
      imod fupd_mask_subseteq hE' with Hclose
      imod IH $$ [$] with ⟨%_, Hstep⟩
      imodintro
      isplit
      · ipureintro
        simp only [LE.le] at hs
        grind [cases Stuckness]
      iintro %κ %e₂ %σ₂ %eₜ Hprim
      imod Hstep $$ Hprim with ⟨%hκ, Hσ, ⟨IH₂, -⟩, Hefs⟩
      imod Hclose
      imodintro
      iframe %hκ Hσ
      isplitl [IH₂ Hpost]
      · iapply IH₂ $$ [//] Hpost
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %_ ⟨IHef, -⟩
        iapply IHef $$ %⊤ %ι.forkPost %LawfulSet.subset_refl
        iintro %v $
    · imod fupd_mask_mono hE' $$ IH with HΦv
      iapply Hpost $$ HΦv

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
    WP e @ s ; E [{ v, |={E}=> Φ v }] ⊢ WP e @ s ; E [{ Φ }] := by
  iintro H
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %_ $

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
    imod Hstep $$ %κ %e₂ %σ₂ %eₜ %Hprim with ⟨%hκ, Hσ, He₂, Hefs⟩
    cases s
    · cases he₂ : toVal e₂ with
      | some v₂ =>
        imod (value_fupd ⟨ToVal.coe_of_toVal_eq_some he₂⟩).mp $$ He₂ with >He₂
        iframe %hκ Hσ Hefs
        iapply (value_fupd ⟨ToVal.coe_of_toVal_eq_some he₂⟩).mpr $$ He₂
      | none =>
        simp only [(unfold (e := e₂)).to_eq, pre, he₂]
        imod He₂ $$ Hσ with ⟨%Hred₂, _⟩
        exact ((not_reducible_iff_irreducible.mpr (hatom.atomic Hprim))
          (reducible_of_reducibleNoObs Hred₂)).elim
    · have ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp (hatom.atomic Hprim)
      rw [(value_fupd ⟨ToVal.coe_of_toVal_eq_some hv₂⟩).to_eq]
      imod He₂ with >He₂
      iframe %hκ Hσ Hefs
      iapply (value_fupd ⟨ToVal.coe_of_toVal_eq_some hv₂⟩) $$ [$]


@[rocq_alias twp_bind]
theorem bind (K : Expr → Expr) [ctx : Language.Context K]
    {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ v, WP (K (↑v : Val)) @ s ; E [{ Φ }]}] ⊢ WP (K e) @ s ; E [{ Φ }] := by
  let Pred := fun (E : CoPset) (e : Expr) (Ψ : Val → IProp GF) => iprop%
    ∀ Φ, (∀ v, Ψ v -∗ WP (K v) @ s ; E [{ Φ }]) -∗
      WP (K e) @ s ; E [{ Φ }]
  letI : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) :=
    ⟨fun _ _ _ ⟨hE, he, hΨ⟩ => hE ▸ he ▸ BI.forall_ne fun _ =>
      BI.wand_ne.ne (BI.forall_ne fun v => BI.wand_ne.ne (hΨ v) .rfl) .rfl⟩
  iintro H
  iapply induction s Pred $$ [] H
  · iintro !> %e %E %Ψ IH %Φ Hcont
    simp only [pre]
    cases he : toVal e
    · simp only [(unfold (e := K e)).to_eq, pre, ctx.toVal_eq_none_fill he]
      iintro %σ₁ %ns %obs %nt Hσ
      imod IH $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      isplit
      · ipureintro
        grind [Language.Context.reducibleNoObs_fill]
      iintro %κ %e₂ %σ₂ %eₜ %HKstep
      obtain ⟨e₂', rfl, Hprim⟩ := ctx.primStep_fill_inv he HKstep
      imod Hstep $$ [//] with ⟨%hκ, Hσ, ⟨IH, -⟩, Hefs⟩
      iframe %hκ Hσ
      isplitl [IH Hcont]
      · iapply IH $$ Hcont
      · iapply BI.BigSepL.bigSepL_mono_of_forall BI.and_elim_r $$ Hefs
    · rw [← (ToVal.coe_of_toVal_eq_some he)]
      iapply fupd_twp
      imod IH
      iapply Hcont $$ [$]
  · iintro %_ $

@[rocq_alias twp_bind_inv]
theorem bind_inv (K : Expr → Expr) [ctx : Language.Context K]
    {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    WP (K e) @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ v, WP (K (↑v : Val)) @ s ; E [{ Φ }]}] := by
  let Pred := fun (E : CoPset) (e' : Expr) (Φ : Val → IProp GF) => iprop%
    ∀ e, ⌜e' = K e⌝ -∗ WP e @ s ; E [{ v, WP (K (↑v : Val)) @ s ; E [{ Φ }]}]
  letI : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) :=
    ⟨fun _ _ _ ⟨hE, he, hΦ⟩ => hE ▸ he ▸ BI.forall_ne fun _ =>
      BI.wand_ne.ne .rfl (NonExpansive.ne fun _ => NonExpansive.ne hΦ)⟩
  iintro H
  iapply induction s Pred $$ [] H %e %rfl
  iintro !> %e' %E %Φ IH %e %heq
  rw [heq, unfold.to_eq]
  cases he : toVal e with
  | some v =>
      ihave IHfold : iprop(WP (K e) @ s ; E [{ Φ }]) $$ [IH]
      · rw [unfold.to_eq]
        iapply pre_mono $$ [] %E %(K e) %Φ IH
        iintro !> %E %e %Φ ⟨-, $⟩
      simp only [pre, ← ToVal.coe_of_toVal_eq_some he, toVal_coe]
      itrivial
  | none =>
      simp only [pre, he, ctx.toVal_eq_none_fill he]
      iintro %σ₁ %ns %obs %nt Hσ
      imod IH $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      isplit
      · ipureintro
        grind [Language.Context.reducibleNoObs_fill_inv]
      iintro %κ %e₂ %σ₂ %eₜ %Hprim
      imod Hstep $$ %_ %_ %_ %_ %(ctx.primStep_fill Hprim) with ⟨$, $, ⟨IH₂, -⟩, Hefs⟩
      isplitl [IH₂]
      · iapply IH₂ $$ %e₂ %rfl
      · iapply BI.BigSepL.bigSepL_mono_of_forall BI.and_elim_r $$ Hefs

@[rocq_alias twp_wp]
theorem to_wp {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] -∗ WP e @ s ; E {{ Φ }} := by
  iintro H
  iloeb as IH generalizing %E %e %Φ
  simp only [(wp_unfold (e := e)).to_eq, (unfold (e := e)).to_eq, wp.pre, pre]
  cases hval : toVal e
  case some v => itrivial
  case none =>
    iintro %σ %ns %κ %κs %nt Hσ
    imod H $$ Hσ with ⟨%Hred, H⟩
    imodintro
    isplitr
    · ipureintro
      grind
    iintro %e₂ %σ₂ %eₜ %Hstep _
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

@[rocq_alias twp_mono]
theorem mono {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF}
    (H : ∀ v, Φ v ⊢ Ψ v) :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ Ψ }] := by
  iintro H
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %v _
  iapply H $$ [$]

@[rocq_alias twp_stuck_mono]
theorem stuck_mono {s₁ s₂ : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} (H : s₁ ≤ s₂) :
    WP e @ s₁ ; E [{ Φ }] ⊢ WP e @ s₂ ; E [{ Φ }] := by
  iintro H
  iapply strong_mono H LawfulSet.subset_refl $$ H
  iintro %_ $

@[rocq_alias twp_stuck_weaken]
theorem stuck_weaken {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ E ? [{ Φ }] :=
  stuck_mono Stuckness.le_MaybeStuck

@[rocq_alias twp_mask_mono]
theorem mask_mono {s : Stuckness} {E₁ E₂} {e : Expr} {Φ : Val → IProp GF}
    (H : E₁ ⊆ E₂) :
    WP e @ s ; E₁ [{ Φ }] ⊢ WP e @ s ; E₂ [{ Φ }] := by
  iintro H
  iapply strong_mono (Std.IsPreorder.le_refl _) H $$ H
  iintro %_ $

@[rocq_alias twp_value']
theorem value' {s : Stuckness} {E} {v : Val} {Φ : Val → IProp GF} :
    Φ v ⊢ WP (v : Expr) @ s ; E [{ Φ }] := fupd_intro.trans value_fupd'.mpr

@[rocq_alias twp_value]
theorem value {s : Stuckness} {E} {e : Expr} {v : Val} {Φ : Val → IProp GF} (h : e = v) :
    Φ v ⊢ WP e @ s ; E [{ Φ }] := h ▸ value'

@[rocq_alias twp_frame_l]
theorem frame_l {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} :
    R ∗ WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ v, R ∗ Φ v }] := by
  iintro ⟨_, H⟩
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %_ $
  itrivial

@[rocq_alias twp_frame_r]
theorem frame_r {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    WP e @ s ; E [{ Φ }] ∗ R ⊢ WP e @ s ; E [{ v, Φ v ∗ R }] := by
  iintro ⟨H, _⟩
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %_ $
  itrivial

@[rocq_alias twp_wand]
theorem wand {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E [{ Ψ }] := by
  iintro H HΦ
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %_ _
  iapply HΦ $$ [$]

@[rocq_alias twp_wand_l]
theorem wand_l {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF} :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ Ψ }] := by
  iintro ⟨H, Hwp⟩
  iapply wand $$ Hwp H

@[rocq_alias twp_wand_r]
theorem wand_r {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s ; E [{ Ψ }] := by
  iintro ⟨Hwp, H⟩
  iapply wand $$ Hwp H

@[rocq_alias twp_frame_wand]
theorem frame_wand {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    R ⊢ (WP e @ s ; E [{ v, R -∗ Φ v }]) -∗ WP e @ s ; E [{ Φ }] := by
  iintro HR HWP
  iapply wand $$ HWP
  iintro %v HΦ
  iapply HΦ $$ [$]

@[rocq_alias twp_wp_step]
theorem wp_step {s : Stuckness} {E} {e: Expr} P {Φ : Val → IProp GF} (toVal_e : toVal e = none) :
    ▷ P -∗ WP e @ s; E [{ v, P ={E}=∗ Φ v }] -∗ WP e @ s; E {{ Φ }} := by
 iintro HP Hwp
 iapply wp_step_fupd toVal_e LawfulSet.subset_refl $$ [$HP]
 iapply to_wp $$ [$]

section ProofMode

open ProofMode

variable {s : Stuckness} {E E₁ E₂ : CoPset} {e : Expr}
variable {Φ Ψ : Val → IProp GF} {P R : IProp GF}

@[rocq_alias frame_twp]
instance frameTwp {p : Bool} [H : ∀ v, FrameInstantiateExistDisabled p R (Φ v) (Ψ v)] :
    Frame p R (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Ψ }]) where
  frame := frame_l.trans (mono fun v => (H v).frame_instantiatiate_exist_disabled.frame)

@[rocq_alias total_weakestpre.is_except_0_wp]
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

@[rocq_alias add_modal_fupd_twp]
instance addModalFupdTwp : AddModal iprop(|={E}=> P) P iprop(WP e @ s; E [{ Φ }]) where
  add_modal := fupd_wand_right.trans fupd_twp

@[rocq_alias elim_acc_twp_atomic]
instance (priority := low) elimAcc_twp_atomic (E₁ E₂ : CoPset) α β (γ : X → Option (IProp GF)) :
    ElimAcc (Language.Atomic ↑s e) (fupd E₁ E₂) (fupd E₂ E₁) α β γ
      (WP e @ s ; E₁ [{ Φ }]) (fun x => WP e @ s ; E₂ [{ v, |={E₂}=> β x ∗ (γ x -∗? Φ v) }]) where
  elim_acc := by
    dsimp only [accessor]
    iintro %atomic Hinner >⟨%x, Hα, Hclose⟩
    iapply twp.wand $$ (Hinner $$ Hα)
    iintro %v >⟨Hβ, HΦ⟩
    iapply HΦ
    iapply Hclose
    itrivial

end ProofMode

end Rules
end twp
end
end Iris
