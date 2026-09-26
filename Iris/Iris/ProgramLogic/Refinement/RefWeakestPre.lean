/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.BI.Lib.Fixpoint
public import Iris.BI.Lib.LogicalStep
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Refinement.RefSource

/-! # The refinement weakest precondition of Transfinite Iris

This file ports `theories/program_logic/refinement/ref_weakestpre.v` of Transfinite Iris. The
refinement weakest precondition `rwp s E e Φ` (Rocq: `RWP e @ s; E ⟨⟨ Φ ⟩⟩`) is a *least*
fixpoint: every target step is simulated by source steps, where a target step may only take a later
(`▷?b` with `b = true`) if at least one source step is taken. Termination of the source then
implies termination of the target (see `RefAdequacy.lean`).

The strong refinement weakest precondition `rswp k s E e Φ` (Rocq: `RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩`)
takes the next target step without a source step, after `k` step-taking fancy updates.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris ProgramLogic Language Language.Notation Iris.Std Iris.BI OFE Relation

/-- The ghost state and state interpretation of the refinement program logic
(Rocq: `ref_irisG`). -/
class RefIrisGS (Expr : Type _) {Val State Obs : Type _} [Language Expr State Obs Val]
    (GF : BundledGFunctors) extends WsatGS GF where
  /-- The state interpretation, given the number of forked threads. -/
  refStateInterp : State → Nat → IProp GF
  /-- The postcondition of forked threads. -/
  refForkPost : Val → IProp GF

attribute [instance] RefIrisGS.toWsatGS

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} {A : Type _} [src : Source GF A] [ι : RefIrisGS Expr GF]

/-- A target step simulated by source steps (Rocq: `rwp_step`). -/
def rwpStep (E : CoPset) (s : Stuckness) (e₁ : Expr) (φ : Expr → List Expr → IProp GF) :
    IProp GF :=
  iprop(∀ (σ₁ : State) (n : Nat) (a : A), src.interp a ∗ ι.refStateInterp σ₁ n ={E,∅}=∗
    ∃ b : Bool, ▷?b |={∅}=> (⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ -∗ |={∅,E}=>
        ((if b then ∃ a' : A, ⌜TransGen src.rel a a'⌝ ∗ src.interp a' else src.interp a) ∗
          ι.refStateInterp σ₂ (efs.length + n) ∗ φ e₂ efs)))

/-- A target step without a source step, after `k` step-taking updates (Rocq: `rswp_step`). -/
def rswpStep (k : Nat) (E : CoPset) (s : Stuckness) (e₁ : Expr)
    (φ : Expr → List Expr → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : State) (n : Nat) (a : A), src.interp a ∗ ι.refStateInterp σ₁ n ={E,∅}=∗
    |={∅}[∅]▷=>^[k] (⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ -∗ |={∅,E}=>
        (src.interp a ∗ ι.refStateInterp σ₂ (efs.length + n) ∗ φ e₂ efs)))

/-- The body of the refinement weakest precondition (Rocq: `rwp_pre`). -/
def rwpPre (s : Stuckness) (rwp : CoPset → Expr → (Val → IProp GF) → IProp GF) (E : CoPset)
    (e₁ : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(∀ (σ : State) (n : Nat) (a : A), src.interp a ∗ ι.refStateInterp σ n ={E}=∗
      src.interp a ∗ ι.refStateInterp σ n ∗ Φ v)
  | none => rwpStep (src := src) E s e₁ fun e₂ efs =>
      iprop(rwp E e₂ Φ ∗ [∗list] ef ∈ efs, rwp ⊤ ef ι.refForkPost)

/-- An intuitionistic proposition can be moved below iterated laters. -/
theorem laterN_frame_intuitionistic {PROP : Type _} [BI PROP] {n : Nat} {R P : PROP} :
    □ R ∗ ▷^[n] P ⊢ ▷^[n] (□ R ∗ P) :=
  (sep_mono_left (laterN_intro n)).trans (laterN_sep_2 n)

/-- Rocq: `rwp_pre_mono`. -/
theorem rwpPre_mono (s : Stuckness) (X Y : CoPset → Expr → (Val → IProp GF) → IProp GF) :
    ⊢ □ (∀ E e Φ, X E e Φ -∗ Y E e Φ) -∗
      ∀ E e Φ, rwpPre (src := src) s X E e Φ -∗ rwpPre (src := src) s Y E e Φ := by
  iintro #H %E %e %Φ Hwp
  unfold rwpPre
  cases toVal e with
  | some => iexact Hwp
  | none =>
    unfold rwpStep
    iintro %σ₁ %n %a Hσ
    imod Hwp $$ %σ₁ %n %a Hσ with ⟨%b, Hwp⟩
    imodintro
    iexists b
    ihave Hwp := laterN_frame_intuitionistic (R := iprop(∀ E e Φ, X E e Φ -∗ Y E e Φ)) $$ [Hwp]
    · isplitr [Hwp]
      · imodintro
        iexact H
      · iexact Hwp
    iapply laterN_mono _ ?_ $$ Hwp
    iintro ⟨#H, Hwp⟩
    imod Hwp with ⟨$, Hwp⟩
    imodintro
    iintro %e₂ %σ₂ %efs %κ %Hstep
    imod Hwp $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hsrc, Hσ, Hwp, Hfork⟩
    imodintro
    iframe Hsrc Hσ
    isplitl [Hwp]
    · iapply H $$ Hwp
    · iapply BigSepL.bigSepL_impl $$ Hfork
      iintro !> %k %ef %_ Hef
      iapply H $$ Hef

namespace RefInternal


abbrev Args (Expr Val : Type _) (GF : BundledGFunctors) :=
  CoPset × Expr × (Val → IProp GF)

/-- The OFE on the arguments of the fixpoint: discrete on masks and expressions. The step-index
type is determined by `GF`. -/
@[reducible] def argsOFE : OFE (Args Expr Val GF) :=
  haveI : OFE CoPset := OFE.ofDiscrete _
  haveI : OFE Expr := OFE.ofDiscrete _
  inferInstance

attribute [local instance high] argsOFE

abbrev pre' (s : Stuckness) (X : Args Expr Val GF → IProp GF) : Args Expr Val GF → IProp GF
  | (E, e, Φ) => rwpPre (src := src) s (fun E e Φ => X (E, e, Φ)) E e Φ

instance pre'_mono (s : Stuckness) : BIMonoPred (pre' (src := src) (ι := ι) s) where
  mono_pred := by
    intro X Y _ _
    iintro #HXY %⟨E, e, Φ⟩ HX
    unfold pre'
    iapply rwpPre_mono $$ [] [$]
    iintro !> %E %e %Φ H
    iapply HXY $$ H
  mono_pred_ne {X} hX := ⟨fun {n} ⟨E₁, e₁, Φ₁⟩ ⟨E₂, e₂, Φ₂⟩ ⟨hE, he, hΦ⟩ => by
    obtain rfl := show E₁ = E₂ from hE
    obtain rfl := show e₁ = e₂ from he
    simp only [pre', rwpPre]
    match toVal e₁ with
    | some v =>
      refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
      exact wand_ne.ne .rfl (BIFUpdate.ne.ne (sep_ne.ne .rfl (sep_ne.ne .rfl (hΦ v))))
    | none =>
      simp only [rwpStep]
      refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
      refine wand_ne.ne .rfl <| BIFUpdate.ne.ne <| exists_ne fun _ => ?_
      refine (laterN_ne _).ne <| BIFUpdate.ne.ne <| sep_ne.ne .rfl ?_
      refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
      refine wand_ne.ne .rfl <| BIFUpdate.ne.ne <| sep_ne.ne .rfl <| sep_ne.ne .rfl ?_
      refine sep_ne.ne ?_ .rfl
      exact hX.ne ⟨rfl, rfl, hΦ⟩⟩

/-- Rocq: `rwp_def`. -/
def get (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  bi_least_fixpoint (pre' (src := src) (ι := ι) s) (E, e, Φ)

end RefInternal

attribute [local instance high] RefInternal.argsOFE

/-- The refinement weakest precondition (Rocq: `rwp`, notation `RWP e @ s; E ⟨⟨ Φ ⟩⟩`). -/
def rwp (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  RefInternal.get (src := src) (ι := ι) s E e Φ

/-- The strong refinement weakest precondition (Rocq: `rswp`, notation
`RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩`). -/
def rswp (k : Nat) (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  rswpStep (src := src) k E s e fun e₂ efs =>
    iprop(rwp (src := src) s E e₂ Φ ∗ [∗list] ef ∈ efs, rwp (src := src) s ⊤ ef ι.refForkPost)

/-- Rocq: `rwp_unfold`. -/
theorem rwp_unfold {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    rwp (src := src) (ι := ι) s E e Φ ⊣⊢ rwpPre (src := src) s (rwp (src := src) s) E e Φ :=
  equiv_iff.mp (least_fixpoint_unfold (RefInternal.pre' (src := src) (ι := ι) s))

/-- Rocq: `rwp_strong_ind`. -/
theorem rwp_strong_ind (s : Stuckness) (Ψ : CoPset → Expr → (Val → IProp GF) → IProp GF)
    (HΨ : ∀ {n} E e {Φ₁ Φ₂ : Val → IProp GF}, (∀ v, Φ₁ v ≡{n}≡ Φ₂ v) → Ψ E e Φ₁ ≡{n}≡ Ψ E e Φ₂) :
    ⊢ □ (∀ e E Φ, rwpPre (src := src) s
        (fun E e Φ => iprop(Ψ E e Φ ∧ rwp (src := src) (ι := ι) s E e Φ)) E e Φ -∗ Ψ E e Φ) -∗
      ∀ e E Φ, rwp (src := src) s E e Φ -∗ Ψ E e Φ := by
  letI : NonExpansive (fun x : RefInternal.Args Expr Val GF => Ψ x.1 x.2.1 x.2.2) :=
    ⟨fun {n} ⟨E₁, e₁, Φ₁⟩ ⟨E₂, e₂, Φ₂⟩ ⟨hE, he, hΦ⟩ => by
      obtain rfl := show E₁ = E₂ from hE
      obtain rfl := show e₁ = e₂ from he
      exact HΨ E₁ e₁ hΦ⟩
  iintro #IH %e %E %Φ
  isimp only [rwp, RefInternal.get]
  iapply least_fixpoint_ind (F := RefInternal.pre' (src := src) (ι := ι) s)
    (Φ := fun x => Ψ x.1 x.2.1 x.2.2) $$ []
  iintro !> %⟨_, _, _⟩
  isimp only [rwp, RefInternal.get] at IH
  iapply IH

/-- Rocq: `rwp_ne`. -/
instance rwp_ne {s : Stuckness} {E : CoPset} {e : Expr} :
    NonExpansive (rwp (src := src) (ι := ι) s E e) where
  ne {n Φ₁ Φ₂} HΦ := by
    refine NonExpansive.ne (f := bi_least_fixpoint (RefInternal.pre' (src := src) (ι := ι) s)) ?_
    exact ⟨rfl, rfl, HΦ⟩


theorem laterIf_false {PROP : Type _} [BI PROP] {P : PROP} : iprop(▷?false P) = P := rfl

theorem laterIf_true {PROP : Type _} [BI PROP] {P : PROP} : iprop(▷?true P) = iprop(▷ P) := rfl

/-- Frame a proposition below iterated laters. -/
theorem laterN_wand_frame₁ {PROP : Type _} [BI PROP] {n : Nat} {R P Q : PROP}
    (h : R ∗ P ⊢ Q) : ⊢ R -∗ ▷^[n] P -∗ ▷^[n] Q := by
  iintro H HP
  iapply laterN_mono n h
  iapply laterN_sep_2 n
  isplitl [H]
  · iapply laterN_intro n $$ H
  · iexact HP

/-- Frame two propositions below iterated laters. -/
theorem laterN_wand_frame₂ {PROP : Type _} [BI PROP] {n : Nat} {R₁ R₂ P Q : PROP}
    (h : R₁ ∗ R₂ ∗ P ⊢ Q) : ⊢ R₁ -∗ R₂ -∗ ▷^[n] P -∗ ▷^[n] Q := by
  iintro H₁ H₂ HP
  iapply laterN_mono n h
  ihave H := laterN_sep_2 n $$ [H₂ HP]
  · isplitl [H₂]
    · iapply laterN_intro n $$ H₂
    · iexact HP
  iapply laterN_sep_2 n
  isplitl [H₁]
  · iapply laterN_intro n $$ H₁
  · iexact H

section rwp

variable {s s₁ s₂ : Stuckness} {E E₁ E₂ : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF}

/-- Rocq: `rwp_value'`. -/
theorem rwp_value' (v : Val) : Φ v ⊢ rwp (src := src) (ι := ι) s E (v : Expr) Φ := by
  refine .trans ?_ rwp_unfold.mpr
  unfold rwpPre
  rw [toVal_coe]
  iintro HΦ %σ %n %a ⟨Ha, Hσ⟩
  imodintro
  iframe

/-- Rocq: `rwp_strong_mono'`. -/
theorem rwp_strong_mono' (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ rwp (src := src) (ι := ι) s₁ E₁ e Φ -∗
      (∀ σ n a v, src.interp a ∗ ι.refStateInterp σ n ∗ Φ v ={E₂}=∗
        src.interp a ∗ ι.refStateInterp σ n ∗ Ψ v) -∗
      rwp (src := src) s₂ E₂ e Ψ := by
  let Pred := fun (E : CoPset) (e : Expr) (Φ : Val → IProp GF) => iprop(
    ∀ E₂ Ψ, ⌜E ⊆ E₂⌝ -∗
      (∀ σ n a v, src.interp a ∗ ι.refStateInterp σ n ∗ Φ v ={E₂}=∗
        src.interp a ∗ ι.refStateInterp σ n ∗ Ψ v) -∗
      rwp (src := src) (ι := ι) s₂ E₂ e Ψ)
  have hPred : ∀ {n} E e {Φ₁ Φ₂ : Val → IProp GF}, (∀ v, Φ₁ v ≡{n}≡ Φ₂ v) →
      Pred E e Φ₁ ≡{n}≡ Pred E e Φ₂ := by
    intro _ _ _ _ _ hΦ
    exact forall_ne fun _ => forall_ne fun _ => wand_ne.ne .rfl <| wand_ne.ne
      (forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun v =>
        wand_ne.ne (sep_ne.ne .rfl (sep_ne.ne .rfl (hΦ v))) .rfl) .rfl
  iintro H HΦ
  iapply rwp_strong_ind s₁ Pred hPred $$ [] H [//] HΦ
  iintro !> %e₁ %E %Φ₁ IH %E' %Ψ' %hE' Hpost
  iapply rwp_unfold.mpr
  unfold rwpPre
  cases hv : toVal e₁ with
  | some v =>
    simp only [hv]
    iintro %σ %n %a Hσ
    ihave IH := IH $$ %σ %n %a Hσ
    imod fupd_mask_mono hE' $$ IH with H
    iapply Hpost $$ %σ %n %a %v H
  | none =>
    simp only [hv]
    unfold rwpStep
    iintro %σ₁ %n %a Hσ
    imod fupd_mask_subseteq hE' with Hclose
    imod IH $$ %σ₁ %n %a Hσ with ⟨%b, IH⟩
    imodintro
    iexists b
    iapply laterN_wand_frame₂ ?h $$ Hclose Hpost IH
    case h =>
      iintro ⟨Hclose, Hpost, IH⟩
      imod IH with ⟨%Hred, IH⟩
      imodintro
      isplitr
      · ipureintro
        cases s₁ <;> cases s₂ <;> simp_all [LE.le]
      iintro %e₂ %σ₂ %efs %κ %Hstep
      imod IH $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hsrc, Hσ, ⟨IH₂, -⟩, Hefs⟩
      imod Hclose
      imodintro
      iframe Hsrc Hσ
      isplitl [IH₂ Hpost]
      · iapply IH₂ $$ [//] Hpost
      · iapply BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %_ ⟨IHef, -⟩
        iapply IHef $$ %⊤ %ι.refForkPost %LawfulSet.subset_refl
        iintro %σ %n %a %v H
        imodintro
        iexact H

/-- Rocq: `rwp_strong_mono`. -/
theorem rwp_strong_mono (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ rwp (src := src) (ι := ι) s₁ E₁ e Φ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗
      rwp (src := src) s₂ E₂ e Ψ := by
  iintro H HΦ
  iapply rwp_strong_mono' hs hE $$ H
  iintro %σ %n %a %v ⟨Ha, Hσ, HΦv⟩
  imod HΦ $$ %v HΦv with HΨ
  imodintro
  iframe

/-- Rocq: `fupd_rwp`. -/
theorem fupd_rwp : (|={E}=> rwp (src := src) (ι := ι) s E e Φ) ⊢ rwp (src := src) s E e Φ := by
  refine .trans ?_ rwp_unfold.mpr
  refine (fupd_mono rwp_unfold.mp).trans ?_
  unfold rwpPre
  cases toVal e with
  | some v =>
    iintro H %σ %n %a Hσ
    imod H
    iapply H $$ %σ %n %a Hσ
  | none =>
    unfold rwpStep
    iintro H %σ %n %a Hσ
    imod H
    iapply H $$ %σ %n %a Hσ

/-- Rocq: `rwp_fupd`. -/
theorem rwp_fupd :
    rwp (src := src) (ι := ι) s E e (fun v => iprop(|={E}=> Φ v)) ⊢ rwp (src := src) s E e Φ := by
  iintro H
  iapply rwp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  iexact H

/-- Rocq: `rwp_mono`. -/
theorem rwp_mono (h : ∀ v, Φ v ⊢ Ψ v) :
    rwp (src := src) (ι := ι) s E e Φ ⊢ rwp (src := src) s E e Ψ := by
  iintro H
  iapply rwp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iapply h $$ H

/-- Rocq: `rwp_stuck_mono`. -/
theorem rwp_stuck_mono (hs : s₁ ≤ s₂) :
    rwp (src := src) (ι := ι) s₁ E e Φ ⊢ rwp (src := src) s₂ E e Φ := by
  iintro H
  iapply rwp_strong_mono hs LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iexact H

/-- Rocq: `rwp_mask_mono`. -/
theorem rwp_mask_mono (hE : E₁ ⊆ E₂) :
    rwp (src := src) (ι := ι) s E₁ e Φ ⊢ rwp (src := src) s E₂ e Φ := by
  iintro H
  iapply rwp_strong_mono (Std.IsPreorder.le_refl s) hE $$ H
  iintro %v H
  imodintro
  iexact H

/-- Rocq: `rwp_value_fupd'`. -/
theorem rwp_value_fupd' (v : Val) :
    (|={E}=> Φ v) ⊢ rwp (src := src) (ι := ι) s E (v : Expr) Φ :=
  (rwp_value' (Φ := fun v => iprop(|={E}=> Φ v)) v).trans rwp_fupd

/-- Rocq: `rwp_frame_l`. -/
theorem rwp_frame_l {R : IProp GF} :
    R ∗ rwp (src := src) (ι := ι) s E e Φ ⊢ rwp (src := src) s E e fun v => iprop(R ∗ Φ v) := by
  iintro ⟨HR, H⟩
  iapply rwp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v HΦ
  imodintro
  iframe

/-- Rocq: `rwp_frame_r`. -/
theorem rwp_frame_r {R : IProp GF} :
    rwp (src := src) (ι := ι) s E e Φ ∗ R ⊢ rwp (src := src) s E e fun v => iprop(Φ v ∗ R) := by
  iintro ⟨H, HR⟩
  iapply rwp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v HΦ
  imodintro
  iframe

/-- Rocq: `rwp_wand`. -/
theorem rwp_wand :
    ⊢ rwp (src := src) (ι := ι) s E e Φ -∗ (∀ v, Φ v -∗ Ψ v) -∗ rwp (src := src) s E e Ψ := by
  iintro H HΦ
  iapply rwp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iapply HΦ $$ H

end rwp

section rswp

variable {k : Nat} {s s₁ s₂ : Stuckness} {E E₁ E₂ : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF}

/-- Rocq: `rswp_strong_mono`. -/
theorem rswp_strong_mono (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ rswp (src := src) (ι := ι) k s₁ E₁ e Φ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗
      rswp (src := src) k s₂ E₂ e Ψ := by
  unfold rswp rswpStep
  iintro H HΦ %σ₁ %n %a Hσ
  imod fupd_mask_subseteq hE with Hclose
  imod H $$ %σ₁ %n %a Hσ with H
  imodintro
  iapply step_fupdN_wand $$ H
  iintro ⟨%Hred, H⟩
  isplitr
  · ipureintro
    cases s₁ <;> cases s₂ <;> simp_all [LE.le]
  iintro %e₂ %σ₂ %efs %κ %Hstep
  imod H $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hsrc, Hσ, H, Hefs⟩
  imod Hclose
  imodintro
  iframe Hsrc Hσ
  isplitl [H HΦ]
  · iapply rwp_strong_mono hs hE $$ H HΦ
  · iapply BigSepL.bigSepL_impl $$ Hefs
    iintro !> %k' %ef %_ H
    iapply rwp_strong_mono hs LawfulSet.subset_refl $$ H
    iintro %v H
    imodintro
    iexact H

/-- Rocq: `fupd_rswp`. -/
theorem fupd_rswp :
    (|={E}=> rswp (src := src) (ι := ι) k s E e Φ) ⊢ rswp (src := src) k s E e Φ := by
  unfold rswp rswpStep
  iintro H %σ %n %a Hσ
  imod H
  iapply H $$ %σ %n %a Hσ

/-- Rocq: `rswp_fupd`. -/
theorem rswp_fupd :
    rswp (src := src) (ι := ι) k s E e (fun v => iprop(|={E}=> Φ v)) ⊢
      rswp (src := src) k s E e Φ := by
  iintro H
  iapply rswp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  iexact H

/-- Rocq: `rswp_mono`. -/
theorem rswp_mono (h : ∀ v, Φ v ⊢ Ψ v) :
    rswp (src := src) (ι := ι) k s E e Φ ⊢ rswp (src := src) k s E e Ψ := by
  iintro H
  iapply rswp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iapply h $$ H

/-- Rocq: `rswp_wand`. -/
theorem rswp_wand :
    ⊢ rswp (src := src) (ι := ι) k s E e Φ -∗ (∀ v, Φ v -∗ Ψ v) -∗
      rswp (src := src) k s E e Ψ := by
  iintro H HΦ
  iapply rswp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  iapply HΦ $$ H

/-- Do not take a source step: the target step is taken without laters (Rocq: `rwp_no_step`). -/
theorem rwp_no_step (he : toVal e = none) :
    rswp (src := src) (ι := ι) 0 s E e Φ ⊢ rwp (src := src) s E e Φ := by
  refine .trans ?_ rwp_unfold.mpr
  unfold rswp rswpStep rwpPre
  rw [he]
  dsimp only
  unfold rwpStep
  iintro H %σ₁ %n %a Hσ
  imod H $$ %σ₁ %n %a Hσ with H
  dsimp only [Nat.repeat]
  imodintro
  iexists false
  rw [laterIf_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨$, H⟩
  imodintro
  iintro %e₂ %σ₂ %efs %κ %Hstep
  iapply H $$ %e₂ %σ₂ %efs %κ %Hstep

/-- Take a source step: the target step may take a later (Rocq: `rwp_take_step`). -/
theorem rwp_take_step {P : IProp GF} (he : toVal e = none) :
    ⊢ (P -∗ rswp (src := src) (ι := ι) 1 s E e Φ) -∗ srcUpdate (src := src) E P -∗
      rwp (src := src) s E e Φ := by
  iintro Hswp Hsrc
  iapply rwp_unfold.mpr
  unfold rswp rswpStep rwpPre
  rw [he]
  dsimp only
  unfold rwpStep srcUpdate
  iintro %σ₁ %n %a ⟨Ha, Hσ⟩
  imod Hsrc $$ %a Ha with ⟨%a', %Ha', Ha', HP⟩
  ihave Hswp := Hswp $$ HP
  imod Hswp $$ %σ₁ %n %a' [$Ha' $Hσ] with Hswp
  dsimp only [Nat.repeat]
  imod Hswp
  imodintro
  iexists true
  rw [laterIf_true]
  simp only [↓reduceIte]
  inext
  imod Hswp with ⟨$, Hswp⟩
  imodintro
  iintro %e₂ %σ₂ %efs %κ %Hstep
  imod Hswp $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hsrc, $, $⟩
  imodintro
  iexists a'
  iframe
  ipureintro
  exact Ha'

/-- Rocq: `rswp_do_step`. -/
theorem rswp_do_step :
    ▷ rswp (src := src) (ι := ι) k s E e Φ ⊢ rswp (src := src) (k + 1) s E e Φ := by
  unfold rswp rswpStep
  iintro H %σ₁ %n %a Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  dsimp only [Nat.repeat]
  imodintro
  inext
  imod Hclose with -
  iapply H $$ %σ₁ %n %a Hσ

end rswp


section rwp_more

variable {s : Stuckness} {E E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF}

theorem maybeReducible_fill (K : Expr → Expr) [Language.Context K] {σ : State}
    (h : s.MaybeReducible (e, σ)) : s.MaybeReducible (K e, σ) := by
  cases s
  · exact Language.Context.reducible_fill K h
  · trivial

/-- Rocq: `fupd_rwp'`. -/
theorem fupd_rwp' :
    (∀ σ n a, src.interp a ∗ ι.refStateInterp σ n ={E}=∗
      src.interp a ∗ ι.refStateInterp σ n ∗ rwp (src := src) (ι := ι) s E e Φ) ⊢
    rwp (src := src) s E e Φ := by
  iintro H
  iapply rwp_unfold.mpr
  cases hv : toVal e with
  | some v =>
    unfold rwpPre
    simp only [hv]
    iintro %σ %n %a Hσ
    imod H $$ %σ %n %a Hσ with ⟨Ha, Hσ, Hwp⟩
    ihave Hwp := rwp_unfold.mp $$ Hwp
    unfold rwpPre
    simp only [hv]
    iapply Hwp $$ %σ %n %a [$Ha $Hσ]
  | none =>
    unfold rwpPre
    simp only [hv]
    unfold rwpStep
    iintro %σ %n %a Hσ
    imod H $$ %σ %n %a Hσ with ⟨Ha, Hσ, Hwp⟩
    ihave Hwp := rwp_unfold.mp $$ Hwp
    unfold rwpPre rwpStep
    simp only [hv]
    iapply Hwp $$ %σ %n %a [$Ha $Hσ]

/-- Rocq: `rwp_weaken'`. -/
theorem rwp_weaken' {P : IProp GF} (he : toVal e = none) :
    ⊢ (P -∗ rwp (src := src) (ι := ι) s E e Φ) -∗ weakSrcUpdate (src := src) E P -∗
      rwp (src := src) s E e Φ := by
  iintro Hwp Hsrc
  iapply rwp_unfold.mpr
  unfold rwpPre weakSrcUpdate
  rw [he]
  dsimp only
  unfold rwpStep
  iintro %σ₁ %n %a ⟨Ha, Hσ⟩
  imod Hsrc $$ %a Ha with ⟨%a', %Haa', Ha', HP⟩
  ihave Hwp := Hwp $$ HP
  ihave Hwp := rwp_unfold.mp $$ Hwp
  unfold rwpPre rwpStep
  rw [he]
  dsimp only
  imod Hwp $$ %σ₁ %n %a' [$Ha' $Hσ] with ⟨%b, Hwp⟩
  imodintro
  cases Haa' with
  | refl =>
    iexists b
    iexact Hwp
  | tail hab hbc =>
    have htc : TransGen src.rel a a' := transGen_of_reflTransGen_transGen hab (.single hbc)
    iexists true
    cases b
    · rw [laterIf_true, laterIf_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      inext
      imod Hwp with ⟨$, Hwp⟩
      imodintro
      iintro %e₂ %σ₂ %efs %κ %Hstep
      imod Hwp $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hsrc, $, $⟩
      imodintro
      iexists a'
      iframe
      ipureintro
      exact htc
    · simp only [laterIf_true, ↓reduceIte]
      inext
      imod Hwp with ⟨$, Hwp⟩
      imodintro
      iintro %e₂ %σ₂ %efs %κ %Hstep
      imod Hwp $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨⟨%a'', %Ha'', Hsrc⟩, $, $⟩
      imodintro
      iexists a''
      iframe
      ipureintro
      exact TransGen.trans htc Ha''

/-- Rocq: `rwp_weaken`. -/
theorem rwp_weaken {P : IProp GF} (he : toVal e = none) :
    ⊢ (P -∗ rwp (src := src) (ι := ι) s E e Φ) -∗ srcUpdate (src := src) E P -∗
      rwp (src := src) s E e Φ := by
  iintro Hwp Hsrc
  iapply rwp_weaken' he $$ Hwp
  iapply srcUpdate_weakSrcUpdate $$ Hsrc

/-- Rocq: `rwp_bind`. -/
theorem rwp_bind (K : Expr → Expr) [ctx : Language.Context K] :
    rwp (src := src) (ι := ι) s E e (fun v => rwp (src := src) s E (K (v : Expr)) Φ) ⊢
      rwp (src := src) s E (K e) Φ := by
  let Pred := fun (E : CoPset) (e : Expr) (Ψ : Val → IProp GF) => iprop(
    ∀ Φ, (∀ v, Ψ v -∗ rwp (src := src) (ι := ι) s E (K (v : Expr)) Φ) -∗
      rwp (src := src) s E (K e) Φ)
  have hPred : ∀ {n} E e {Φ₁ Φ₂ : Val → IProp GF}, (∀ v, Φ₁ v ≡{n}≡ Φ₂ v) →
      Pred E e Φ₁ ≡{n}≡ Pred E e Φ₂ := by
    intro _ _ _ _ _ hΦ
    exact forall_ne fun _ => wand_ne.ne (forall_ne fun v => wand_ne.ne (hΦ v) .rfl) .rfl
  iintro H
  iapply rwp_strong_ind s Pred hPred $$ [] H
  · iintro !> %e %E %Ψ IH %Φ Hcont
    unfold rwpPre
    cases he : toVal e with
    | some v =>
      simp only [he]
      rw [← ToVal.coe_of_toVal_eq_some he]
      iapply fupd_rwp'
      iintro %σ %n %a Hσ
      imod IH $$ %σ %n %a Hσ with ⟨$, $, HΨ⟩
      iapply Hcont $$ HΨ
    | none =>
      simp only [he]
      iapply rwp_unfold.mpr
      unfold rwpPre
      rw [ctx.toVal_eq_none_fill he]
      dsimp only
      unfold rwpStep
      iintro %σ₁ %n %a Hσ
      imod IH $$ %σ₁ %n %a Hσ with ⟨%b, IH⟩
      imodintro
      iexists b
      iapply laterN_wand_frame₁ ?h $$ Hcont IH
      case h =>
        iintro ⟨Hcont, IH⟩
        imod IH with ⟨%Hred, IH⟩
        imodintro
        isplitr
        · ipureintro
          exact maybeReducible_fill K Hred
        iintro %e₂ %σ₂ %efs %κ %Hstep
        obtain ⟨e₂', rfl, Hprim⟩ := ctx.primStep_fill_inv he Hstep
        imod IH $$ %e₂' %σ₂ %efs %κ %Hprim with ⟨Hsrc, Hσ, ⟨IH, -⟩, Hefs⟩
        imodintro
        iframe Hsrc Hσ
        isplitl [IH Hcont]
        · iapply IH $$ Hcont
        · iapply BigSepL.bigSepL_mono_of_forall and_elim_r $$ Hefs
  · iintro %v H
    iexact H

/-- Rocq: `rwp_atomic`. -/
theorem rwp_atomic [hat : Language.Atomic (Val := Val) .StronglyAtomic e] :
    (|={E₁,E₂}=> rwp (src := src) (ι := ι) s E₂ e (fun v => iprop(|={E₂,E₁}=> Φ v))) ⊢
      rwp (src := src) s E₁ e Φ := by
  iintro H
  iapply rwp_unfold.mpr
  cases hv : toVal e with
  | some v =>
    unfold rwpPre
    simp only [hv]
    iintro %σ %n %a Hσ
    imod H
    ihave H := rwp_unfold.mp $$ H
    unfold rwpPre
    simp only [hv]
    imod H $$ %σ %n %a Hσ with ⟨Ha, Hσ, H⟩
    imod H
    imodintro
    iframe
  | none =>
    unfold rwpPre
    simp only [hv]
    unfold rwpStep
    iintro %σ₁ %n %a Hσ
    imod H
    ihave H := rwp_unfold.mp $$ H
    unfold rwpPre rwpStep
    simp only [hv]
    imod H $$ %σ₁ %n %a Hσ with ⟨%b, H⟩
    imodintro
    iexists b
    iapply laterN_mono _ ?_ $$ H
    iintro H
    imod H with ⟨$, H⟩
    imodintro
    iintro %e₂ %σ₂ %efs %κ %Hstep
    imod H $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hsrc, Hσ, H, Hefs⟩
    obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp (hat.atomic Hstep)
    obtain rfl := (ToVal.toVal_eq_iff_coe e₂ v₂).mpr hv₂
    ihave H := rwp_unfold.mp $$ H
    unfold rwpPre
    rw [toVal_coe]
    dsimp only
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      imod H $$ %σ₂ %(efs.length + n) %a [$Hsrc $Hσ] with ⟨Hsrc, Hσ, HΦ⟩
      imod HΦ
      imodintro
      isplitl [Hsrc]
      · iexact Hsrc
      isplitl [Hσ]
      · iexact Hσ
      isplitr [Hefs]
      · iapply rwp_value' $$ HΦ
      · iexact Hefs
    · simp only [↓reduceIte]
      icases Hsrc with ⟨%a', %Ha', Hsrc⟩
      imod H $$ %σ₂ %(efs.length + n) %a' [$Hsrc $Hσ] with ⟨Hsrc, Hσ, HΦ⟩
      imod HΦ
      imodintro
      isplitl [Hsrc]
      · iexists a'
        iframe
        ipureintro
        exact Ha'
      isplitl [Hσ]
      · iexact Hσ
      isplitr [Hefs]
      · iapply rwp_value' $$ HΦ
      · iexact Hefs

end rwp_more

section rswp_more

variable {k : Nat} {s : Stuckness} {E E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF}

/-- Rocq: `rswp_bind`. -/
theorem rswp_bind (K : Expr → Expr) [ctx : Language.Context K] (he : toVal e = none) :
    rswp (src := src) (ι := ι) k s E e (fun v => rwp (src := src) s E (K (v : Expr)) Φ) ⊢
      rswp (src := src) k s E (K e) Φ := by
  unfold rswp rswpStep
  iintro H %σ₁ %n %a Hσ
  imod H $$ %σ₁ %n %a Hσ with H
  imodintro
  iapply step_fupdN_wand $$ H
  iintro ⟨%Hred, H⟩
  isplitr
  · ipureintro
    exact maybeReducible_fill K Hred
  iintro %e₂ %σ₂ %efs %κ %Hstep
  obtain ⟨e₂', rfl, Hprim⟩ := ctx.primStep_fill_inv he Hstep
  imod H $$ %e₂' %σ₂ %efs %κ %Hprim with ⟨Hsrc, Hσ, H, Hefs⟩
  imodintro
  dsimp only
  isplitl [Hsrc]
  · iexact Hsrc
  isplitl [Hσ]
  · iexact Hσ
  isplitr [Hefs]
  · iapply rwp_bind K $$ H
  · iexact Hefs

/-- Rocq: `rswp_atomic`. -/
theorem rswp_atomic [hat : Language.Atomic (Val := Val) .StronglyAtomic e] :
    (|={E₁,E₂}=> rswp (src := src) (ι := ι) k s E₂ e (fun v => iprop(|={E₂,E₁}=> Φ v))) ⊢
      rswp (src := src) k s E₁ e Φ := by
  unfold rswp rswpStep
  iintro H %σ₁ %n %a Hσ
  imod H
  imod H $$ %σ₁ %n %a Hσ with H
  imodintro
  iapply step_fupdN_wand $$ H
  iintro ⟨$, H⟩
  iintro %e₂ %σ₂ %efs %κ %Hstep
  imod H $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hsrc, Hσ, H, Hefs⟩
  obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp (hat.atomic Hstep)
  obtain rfl := (ToVal.toVal_eq_iff_coe e₂ v₂).mpr hv₂
  ihave H := rwp_unfold.mp $$ H
  unfold rwpPre
  rw [toVal_coe]
  dsimp only
  imod H $$ %σ₂ %(efs.length + n) %a [$Hsrc $Hσ] with ⟨Hsrc, Hσ, HΦ⟩
  imod HΦ
  imodintro
  isplitl [Hsrc]
  · iexact Hsrc
  isplitl [Hσ]
  · iexact Hσ
  isplitr [Hefs]
  · iapply rwp_value' $$ HΦ
  · iexact Hefs

end rswp_more

/-! ## Proof mode instances -/

section ProofMode

open ProofMode

variable {k : Nat} {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}

instance elimModal_fupd_rwp p io (P : IProp GF) :
    ElimModal True p io false iprop(|={E}=> P) P (rwp (src := src) (ι := ι) s E e Φ)
      (rwp (src := src) s E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (fupd_mono wand_elim_right).trans fupd_rwp

instance elimModal_fupd_rswp p io (P : IProp GF) :
    ElimModal True p io false iprop(|={E}=> P) P (rswp (src := src) (ι := ι) k s E e Φ)
      (rswp (src := src) k s E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (fupd_mono wand_elim_right).trans fupd_rswp

instance isExcept0_rwp : IsExcept0 (rwp (src := src) (ι := ι) s E e Φ) where
  is_except0 := (except0_mono fupd_intro).trans <| BIFUpdate.except0.trans fupd_rwp

instance isExcept0_rswp : IsExcept0 (rswp (src := src) (ι := ι) k s E e Φ) where
  is_except0 := (except0_mono fupd_intro).trans <| BIFUpdate.except0.trans fupd_rswp

end ProofMode

end Iris.Transfinite
