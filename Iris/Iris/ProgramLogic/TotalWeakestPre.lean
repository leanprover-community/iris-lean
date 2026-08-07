/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.Fixpoint
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProofMode

namespace Iris

open ProgramLogic Language.Notation Std OFE

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
      imodintro
      iframe %hκ Hσ
      isplitl [He₂]
      · iapply H $$ He₂
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %Hef Hef
        iapply H $$ Hef

namespace Internal

instance pre'_mono (s : Stuckness) : BIMonoPred (pre' (ι := ι) s) where
  mono_pred := by
    intro X Y _ _
    iintro #HXY %x HX
    rcases x with ⟨E, e, Φ⟩
    unfold pre'
    iapply pre_mono s (fun E e Φ => X (E, e, Φ)) (fun E e Φ => Y (E, e, Φ)) $$ [] [$]
    iintro !> %E %e %Φ H
    iapply HXY $$ H
  mono_pred_ne.ne {n} := fun ⟨E₁, e₁, Φ₁⟩ ⟨E₂, e₂, Φ₂⟩ ⟨hE, he, hΦ⟩ => by
    change E₁ = E₂ at hE
    change e₁ = e₂ at he
    subst E₂
    subst e₂
    simp only [pre', pre]
    match toVal e₁ with
    | some v => exact BIFUpdate.ne.ne (hΦ v)
    | none =>
      refine BI.forall_ne fun _ => ?_
      refine BI.forall_ne fun _ => ?_
      refine BI.forall_ne fun _ => ?_
      refine BI.forall_ne fun _ => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.forall_ne fun _ => ?_
      refine BI.forall_ne fun _ => ?_
      refine BI.forall_ne fun _ => ?_
      refine BI.forall_ne fun _ => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.sep_ne.ne ?_ ?_
      · apply NonExpansive.ne
        exact ⟨.rfl, .rfl, hΦ⟩
      · rfl

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
    ⊢ ∀ E e Φ, WP e @ s ; E [{ Φ }] -∗ Ψ E e Φ := by
  intro H
  iintro %E %e %Φ
  change ⊢ bi_least_fixpoint (Internal.pre' s) (E, e, Φ) -∗ Ψ E e Φ
  iintro Htwp
  iapply least_fixpoint_ind (F := Internal.pre' s) (Φ := fun x => Ψ x.1 x.2.1 x.2.2) $$ [] Htwp
  iintro !> %⟨E, e, Φ⟩
  simp only [Internal.pre']
  simp only [TotalWp.totalWp, Internal.get] at H
  iapply H

@[rocq_alias twp_ne]
instance ne {s : Stuckness} {E} {e : Expr} :
    NonExpansive (TotalWp.totalWp (PROP := IProp GF) s E e) where
  ne {n Φ₁ Φ₂} HΦ := by
    change bi_least_fixpoint (Internal.pre' s) (E, e, Φ₁) ≡{n}≡ _
    apply NonExpansive.ne
    exact ⟨.rfl, .rfl, HΦ⟩

@[rocq_alias twp_value_fupd']
theorem value_fupd' {s : Stuckness} {E} {Φ : Val → IProp GF} {v : Val} :
    WP (v : Expr) @ s ; E [{ Φ }] ⊣⊢ |={E}=> Φ v := by
  simp [unfold.to_eq, pre, toVal_coe]

@[rocq_alias twp_strong_mono]
theorem strong_mono {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr}
    {Φ Ψ : Val → IProp GF} (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ WP e @ s₁ ; E₁ [{ Φ }] -∗
      (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ [{ Ψ }] := by
  let Pred := fun (E : CoPset) (e : Expr) (Φ : Val → IProp GF) => iprop%
    ∀ E₂ Ψ, ⌜E ⊆ E₂⌝ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ [{ Ψ }]
  have hPred : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) := by
    constructor
    intro n ⟨EX, eX, ΦX⟩ ⟨EY, eY, ΦY⟩ ⟨hE', he', hΦ⟩
    change EX = EY at hE'
    change eX = eY at he'
    subst EY
    subst eY
    refine BI.forall_ne fun _ => ?_
    refine BI.forall_ne fun _ => ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne ?_ .rfl
    refine BI.forall_ne fun v => ?_
    exact BI.wand_ne.ne (hΦ v) .rfl
  iintro H HΦ
  iapply induction s₁ Pred $$ H [//] [$]
  · iintro !> %E %e₁ %Φ₁ IH %E' %Ψ' %hE'
    rw [unfold.to_eq]
    unfold pre
    cases hval : toVal e₁ with
    | some v =>
      iintro HpostSome
      imod fupd_mask_mono hE' $$ IH with HΦv
      iapply HpostSome $$ HΦv
    | none =>
      iintro HpostNone
      iintro %σ₁ %ns %obs %nt Hσ
      imod fupd_mask_subseteq hE' with Hclose
      imod IH $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      isplit
      · ipureintro
        simp only [LE.le] at hs
        grind [cases Stuckness]
      · iintro %κ %e₂ %σ₂ %eₜ Hprim
        imod Hstep $$ Hprim with ⟨%hκ, Hσ, He₂, Hefs⟩
        imod Hclose
        imodintro
        iframe %hκ Hσ
        isplitl [He₂ HpostNone]
        · icases He₂ with ⟨IH₂, -⟩
          iapply IH₂ $$ [//] HpostNone
        · iapply BI.BigSepL.bigSepL_impl $$ Hefs
          iintro !> %k %ef %Hef Hef
          icases Hef with ⟨IHef, -⟩
          iapply IHef $$ %⊤ %ι.forkPost %LawfulSet.subset_refl
          iintro %v Hv
          itrivial

@[rocq_alias fupd_twp]
theorem fupd_twp {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> WP e @ s ; E [{ Φ }]) ⊢ WP e @ s ; E [{ Φ }] := by
  rw [unfold.to_eq]
  iintro H
  unfold pre
  cases toVal e
  · iintro %σ %ns %obs %nt Hσ
    imod H $$ Hσ with $
  · imod H with $

@[rocq_alias twp_fupd]
theorem twp_fupd {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ v, |={E}=> Φ v }] ⊢ WP e @ s ; E [{ Φ }] := by
  iintro H
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %v $

@[rocq_alias twp_atomic]
theorem atomic {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}
    {Φ : Val → IProp GF} [hatom : Language.Atomic ↑s e] :
    (|={E₁,E₂}=> WP e @ s ; E₂ [{ v, |={E₂,E₁}=> Φ v }]) ⊢ WP e @ s ; E₁ [{ Φ }] := by
  rw [unfold.to_eq, unfold.to_eq]
  iintro H
  unfold pre
  cases he : toVal e with
  | some v => icases H with > >$
  | none =>
    iintro %σ₁ %ns %obs %nt Hσ
    imod H $$ Hσ with >⟨$, Hstep⟩
    imodintro
    cases s
    · iintro %κ %e₂ %σ₂ %eₜ %Hprim
      imod Hstep $$ %κ %e₂ %σ₂ %eₜ %Hprim with ⟨%hκ, Hσ, He₂, Hefs⟩
      cases he₂ : toVal e₂ with
      | some v₂ =>
        rw [unfold.to_eq]
        simp only [pre, he₂]
        icases He₂ with > >He₂
        iframe %hκ Hσ Hefs
        simp only [unfold.to_eq, pre, he₂]
        itrivial
      | none =>
        rw [unfold.to_eq]
        simp only [pre, he₂]
        imod He₂ $$ %σ₂ %(ns + 1) %obs %(nt + eₜ.length) Hσ with ⟨%Hred₂, _⟩
        exact (Language.not_reducible_iff_irreducible.mpr (hatom.atomic Hprim))
          (Language.reducible_of_reducibleNoObs Hred₂) |>.elim
    · iintro %κ %e₂ %σ₂ %eₜ %Hprim
      imod Hstep $$ [//] with ⟨%hκ, Hσ, He₂, Hefs⟩
      have ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp (hatom.atomic Hprim)
      rw [unfold.to_eq]
      simp only [pre, hv₂]
      imod He₂ with >He₂
      iframe %hκ Hσ Hefs
      simp only [unfold.to_eq, pre, hv₂]
      itrivial

@[rocq_alias twp_bind]
theorem bind (K : Expr → Expr) [ctx : Language.Context K]
    {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    TotalWp.totalWp s E e
      (fun v : Val => iprop(WP (K v) @ s ; E [{ Φ }])) ⊢ WP (K e) @ s ; E [{ Φ }] := by
  let Pred := fun (E : CoPset) (e : Expr) (Ψ : Val → IProp GF) => iprop%
    ∀ Φ, (∀ v, Ψ v -∗ WP (K v) @ s ; E [{ Φ }]) -∗
      WP (K e) @ s ; E [{ Φ }]
  letI : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) := by
    constructor
    intro n ⟨EX, eX, ΨX⟩ ⟨EY, eY, ΨY⟩ ⟨hE, he, hΨ⟩
    change EX = EY at hE
    change eX = eY at he
    subst EY
    subst eY
    refine BI.forall_ne fun _ => ?_
    refine BI.wand_ne.ne ?_ .rfl
    refine BI.forall_ne fun v => ?_
    exact BI.wand_ne.ne (hΨ v) .rfl
  iintro H
  iapply induction s Pred $$ H
  · iintro !> %E %e %Ψ
    cases he : toVal e with
    | some v =>
      simp only [pre, he]
      iintro Hpre %Φ Hcont
      rw [← (ToVal.coe_of_toVal_eq_some he)]
      ispecialize Hcont $$ %v
      iapply fupd_twp
      iapply (fupd_wand_left (P := Ψ v))
      iframe
    | none =>
      simp only [pre, he]
      iintro Hpre %Φ Hcont
      rw [unfold.to_eq]
      unfold pre
      simp only [ctx.toVal_eq_none_fill he]
      iintro %σ₁ %ns %obs %nt Hσ
      imod Hpre $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      isplit
      · ipureintro
        cases s
        · exact Language.Context.reducibleNoObs_fill (K := K) Hred
        · trivial
      · iintro %κ %e₂ %σ₂ %eₜ %HKstep
        obtain ⟨e₂', rfl, Hprim⟩ := ctx.primStep_fill_inv he HKstep
        imod Hstep $$ [//] with ⟨%hκ, Hσ, He₂, Hefs⟩
        iframe %hκ Hσ
        isplitl [He₂ Hcont]
        · icases He₂ with ⟨IH, -⟩
          iapply IH $$ Hcont
        · iapply BI.BigSepL.bigSepL_impl $$ Hefs
          iintro !> %k %ef %Hef !>⟨-, $⟩
  · iintro %_ $

private theorem fold_induction_right
    (Ψ : CoPset → Expr → (Val → IProp GF) → IProp GF)
    (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    pre s (fun E e Φ => iprop(Ψ E e Φ ∧ WP e @ s ; E [{ Φ }])) E e Φ ⊢ WP e @ s ; E [{ Φ }] := by
  rw [unfold.to_eq]
  iintro Hpre
  iapply pre_mono s (fun E e Φ => iprop(Ψ E e Φ ∧ WP e @ s ; E [{ Φ }])) $$ [] %E %e %Φ Hpre
  iintro !> %E %e %Φ ⟨-, $⟩

@[rocq_alias twp_bind_inv]
theorem bind_inv (K : Expr → Expr) [ctx : Language.Context K]
    {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    WP (K e) @ s ; E [{ Φ }] ⊢
      TotalWp.totalWp s E e (fun v : Val => iprop(WP (K v) @ s ; E [{ Φ }])) := by
  let Pred := fun (E : CoPset) (e' : Expr) (Φ : Val → IProp GF) => iprop%
    ∀ e, ⌜e' = K e⌝ -∗
      TotalWp.totalWp s E e (fun v : Val => iprop(WP (K v) @ s ; E [{ Φ }]))
  letI : NonExpansive (fun x : Internal.Args Expr Val GF => Pred x.1 x.2.1 x.2.2) := by
    constructor
    intro n ⟨EX, eX, ΦX⟩ ⟨EY, eY, ΦY⟩ ⟨hE, he, hΦ⟩
    change EX = EY at hE
    change eX = eY at he
    subst EY
    subst eY
    refine BI.forall_ne fun _ => ?_
    refine BI.wand_ne.ne .rfl ?_
    apply NonExpansive.ne
    exact fun _ => NonExpansive.ne hΦ
  iintro H
  iapply induction s Pred $$ H %e %rfl
  iintro !> %E %e' %Φ IH %e %heq
  subst e'
  rw [unfold.to_eq]
  cases he : toVal e with
  | some v =>
      ihave IHfold := fold_induction_right $$ IH
      simp only [pre, he]
      rw [← (ToVal.coe_of_toVal_eq_some he)]
      itrivial
  | none =>
      simp only [pre, he, ctx.toVal_eq_none_fill he]
      iintro %σ₁ %ns %obs %nt Hσ
      imod IH $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      isplit
      · ipureintro
        cases s
        · exact Language.Context.reducibleNoObs_fill_inv (K := K) he Hred
        · trivial
      · iintro %κ %e₂ %σ₂ %eₜ %Hprim
        imod Hstep $$ %_ %_ %_ %_ %(ctx.primStep_fill Hprim) with ⟨$, $, He₂, Hefs⟩
        imodintro
        isplitl [He₂]
        · icases He₂ with ⟨IH₂, -⟩
          iapply IH₂ $$ %e₂ %rfl
        · iapply BI.BigSepL.bigSepL_impl $$ Hefs
          iintro !> %k %ef %Hef ⟨-, $⟩

@[rocq_alias twp_mono]
theorem mono {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF}
    (H : ∀ v, Φ v ⊢ Ψ v) :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ Ψ }] := by
  iintro Hwp
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ Hwp
  iintro %v Hv
  iapply H $$ [$]

@[rocq_alias twp_stuck_mono]
theorem stuck_mono {s₁ s₂ : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} (H : s₁ ≤ s₂) :
    WP e @ s₁ ; E [{ Φ }] ⊢ WP e @ s₂ ; E [{ Φ }] := by
  iintro Hwp
  iapply strong_mono H LawfulSet.subset_refl $$ Hwp
  iintro %v $

@[rocq_alias twp_stuck_weaken]
theorem stuck_weaken {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ E ? [{ Φ }] :=
  stuck_mono Stuckness.le_MaybeStuck

@[rocq_alias twp_mask_mono]
theorem mask_mono {s : Stuckness} {E₁ E₂} {e : Expr} {Φ : Val → IProp GF}
    (H : E₁ ⊆ E₂) :
    WP e @ s ; E₁ [{ Φ }] ⊢ WP e @ s ; E₂ [{ Φ }] := by
  iintro Hwp
  iapply strong_mono (Std.IsPreorder.le_refl _) H $$ Hwp
  iintro %v $

@[rocq_alias twp_value_fupd]
theorem value_fupd {s : Stuckness} {E} {e : Expr} {v : Val} {Φ : Val → IProp GF} (h : e = v) :
    WP e @ s ; E [{ Φ }] ⊣⊢ |={E}=> Φ v := by
  simp [h, value_fupd']

@[rocq_alias twp_value']
theorem value' {s : Stuckness} {E} {v : Val} {Φ : Val → IProp GF} :
    Φ v ⊢ WP (v : Expr) @ s ; E [{ Φ }] := by
  simp [value_fupd'.to_eq, fupd_intro]

@[rocq_alias twp_value]
theorem value {s : Stuckness} {E} {e : Expr} {v : Val} {Φ : Val → IProp GF} (h : e = v) :
    Φ v ⊢ WP e @ s ; E [{ Φ }] := by
  simp [h, value']

@[rocq_alias twp_frame_l]
theorem frame_l {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} :
    R ∗ WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ v, R ∗ Φ v }] := by
  iintro ⟨HR, Hwp⟩
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ Hwp
  iintro %v $ //

@[rocq_alias twp_frame_r]
theorem frame_r {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    WP e @ s ; E [{ Φ }] ∗ R ⊢ WP e @ s ; E [{ v, Φ v ∗ R }] := by
  rw [BI.sep_comm.to_eq]
  refine frame_l.trans (mono fun v => BI.sep_comm.mp)

@[rocq_alias twp_wand]
theorem wand {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊢
      (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E [{ Ψ }] := by
  iintro Hwp H
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ Hwp
  iintro %v Hv
  imodintro
  iapply H $$ Hv

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
  iintro HR Hwp
  iapply wand $$ Hwp
  iintro %v HΦ
  iapply HΦ $$ HR

@[rocq_alias twp_wp]
theorem to_wp {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E {{ Φ }} := by
  iloeb as IH generalizing %E %e %Φ
  rw [wp_unfold.to_eq, unfold.to_eq]
  unfold wp.pre pre
  cases hval : toVal e
  case some v => iintro $
  case none =>
    iintro H %σ %ns %κ %κs %nt Hσ
    imod H $$ Hσ with ⟨%Hred, H⟩
    imodintro
    isplit
    · ipureintro
      cases s
      · exact Language.reducible_of_reducibleNoObs Hred
      · trivial
    · iintro %e₂ %σ₂ %eₜ %Hstep _
      iapply step_fupdN_intro Std.LawfulSet.empty_subset
      rw [(BI.later_laterN _).to_eq]
      iintro !> !>
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
  frame := by
    refine frame_l.trans (mono fun v => ?_)
    exact (H v).frame_instantiatiate_exist_disabled.frame

-- Iris-Rocq reuses the module-qualified name `is_except_0_wp` here; that alias
-- is already assigned to partial WP in Lean, so this instance is left unaliased.
instance isExcept0Twp : IsExcept0 (WP e @ s ; E [{ Φ }]) where
  is_except0 :=
    calc iprop(◇ _)
      _ ⊢ ◇ |={E}=> _ := BI.except0_mono fupd_intro
      _ ⊢ |={E}=> _ := BIFUpdate.except0
      _ ⊢ WP e @ s ; E [{ Φ }] := fupd_twp

@[rocq_alias elim_modal_fupd_twp]
instance (priority := default + 10) elimModalFupdTwp p :
    ElimModal True p io false iprop(|={E}=> P) P (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Φ }]) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply fupd_twp
    imod H
    iapply G $$ H

@[rocq_alias elim_modal_bupd_twp]
instance elimModalBupdTwp p :
    ElimModal True p io false iprop(|==> P) P (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Φ }]) where
  elim_modal := by
    rintro ⟨⟩
    refine BI.sep_mono (BI.intuitionisticallyIf_mono
      (BIUpdateFUpdate.fupd_of_bupd (E := E))) .rfl |>.trans ?_
    apply elimModalFupdTwp _ |>.elim_modal ⟨⟩ (io := io)

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
  elim_modal := by
    rintro hatomic
    iintro ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply atomic
    imod H
    iapply G $$ H

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
