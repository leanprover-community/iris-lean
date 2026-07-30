/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
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

This is the least-fixed-point total weakest precondition from Iris-Rocq.  In
contrast to ordinary WP, recursive occurrences are not guarded by a later.
Consequently, membership in TWP is a finite derivation and adequacy can turn it
into strong normalization.

The definition remains fork-aware to stay compatible with Iris.  Wasm clients
are expected to use the no-fork lifting rules in `TotalLifting`: the initial
target is single-threaded Wasm, so concurrency-specific derived libraries are
deliberately not duplicated here.

As in Iris-Rocq, TWP only accepts silent operational steps.  A language with
observable reductions must expose a silent administrative semantics or provide
a future trace-sensitive generalization instead of discarding observations.

For Wasm, traps must therefore be represented deliberately: either as values
in the language's result type, or as non-values excluded by the reducibility
obligation. TWP does not silently reinterpret a stuck trap as successful
termination.
-/

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

/-- The stuckness-dependent reducibility condition used by total WP.

Unlike partial WP's `Stuckness.MaybeReducible`, the `NotStuck` case requires
the existence of a *silent* primitive step.  This matches Iris-Rocq's
`reducible_no_obs` premise and prevents an observable transition from being
used to justify TWP only to be rejected by the step clause immediately
afterwards. -/
abbrev Stuckness.MaybeReducibleNoObs : Stuckness → Expr × State → Prop
  | .NotStuck, ρ => PrimStep.ReducibleNoObs ρ
  | .MaybeStuck, _ => True

namespace twp

local instance : OFE CoPset := OFE.ofDiscrete _
local instance : OFE Expr := OFE.ofDiscrete _
local instance : OFE Val := OFE.ofDiscrete _

abbrev Args (Expr Val : Type _) (GF : BundledGFunctors) :=
  (CoPset × Expr) × (Val → IProp GF)

@[rocq_alias twp_pre]
def pre (s : Stuckness)
    (twp : CoPset → Expr → (Val → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(∀ (σ₁ : State) (ns : Nat) (obs : List Obs) (nt : Nat),
      stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ (κ : List Obs) e₂ σ₂ eₜ,
        ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        twp E e₂ Φ ∗
        [∗list] e' ∈ eₜ, twp ⊤ e' ι.forkPost)

def pre' (s : Stuckness)
    (X : Args Expr Val GF → IProp GF) : Args Expr Val GF → IProp GF
  | ((E, e), Φ) => pre s (fun E e Φ => X ((E, e), Φ)) E e Φ

instance pre'_mono (s : Stuckness) : BIMonoPred (pre' (ι := ι) s) where
  mono_pred := by
    intro X Y _ _
    iintro #HXY %x
    rcases x with ⟨⟨E, e⟩, Φ⟩
    simp only [pre', pre]
    iintro HX
    cases toVal e
    case some => iexact HX
    case none =>
      iintro %σ₁ %ns %obs %nt Hσ
      imod HX $$ Hσ with ⟨%Hred, H⟩
      imodintro
      isplit
      · ipureintro
        exact Hred
      · iintro %κ %e₂ %σ₂ %eₜ %Hstep
        imod H $$ %κ %e₂ %σ₂ %eₜ %Hstep with ⟨%hκ, Hσ, He, Hefs⟩
        imodintro
        iframe %hκ Hσ
        isplitl [He]
        · iapply HXY $$ %((E, e₂), Φ) He
        · iapply BI.BigSepL.bigSepL_impl $$ Hefs
          iintro !> %k %ef %Hef Hef
          iapply HXY $$ %((⊤, ef), ι.forkPost) Hef
  mono_pred_ne.ne {X} a b h := by
    rcases a with ⟨⟨E₁, e₁⟩, Φ₁⟩
    rcases b with ⟨⟨E₂, e₂⟩, Φ₂⟩
    rcases h with ⟨⟨hE, he⟩, hΦ⟩
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
        exact ⟨⟨.rfl, .rfl⟩, hΦ⟩
      · exact .rfl

@[rocq_alias twp_pre_mono]
theorem pre_mono (s : Stuckness)
    (X Y : CoPset → Expr → (Val → IProp GF) → IProp GF)
    [NonExpansive (fun x : Args Expr Val GF => X x.1.1 x.1.2 x.2)]
    [NonExpansive (fun x : Args Expr Val GF => Y x.1.1 x.1.2 x.2)] :
    ⊢ □ (∀ E e Φ, X E e Φ -∗ Y E e Φ) -∗
      ∀ E e Φ, pre s X E e Φ -∗ pre s Y E e Φ := by
  iintro #H %E %e %Φ Hpre
  unfold pre
  cases hval : toVal e with
  | some v =>
      imod Hpre with Hpre
      imodintro
      iexact Hpre
  | none =>
      iintro %σ₁ %ns %obs %nt Hσ
      imod Hpre $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      iframe %Hred
      iintro %κ %e₂ %σ₂ %eₜ %Hprim
      imod Hstep $$ %κ %e₂ %σ₂ %eₜ %Hprim with
        ⟨%hκ, Hσ, He₂, Hefs⟩
      imodintro
      iframe %hκ Hσ
      isplitl [He₂]
      · iapply H $$ %E %e₂ %Φ He₂
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %Hef Hef
        iapply H $$ %⊤ %ef %ι.forkPost Hef

def get (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  letI : OFE CoPset := OFE.ofDiscrete _
  letI : OFE Expr := OFE.ofDiscrete _
  letI : OFE Val := OFE.ofDiscrete _
  bi_least_fixpoint (pre' (ι := ι) s) ((E, e), Φ)

instance instTotalWp : TotalWp (IProp GF) Expr Val Stuckness where
  totalWp := get

section Rules

local instance : OFE CoPset := OFE.ofDiscrete _
local instance : OFE Expr := OFE.ofDiscrete _
local instance : OFE Val := OFE.ofDiscrete _

@[rocq_alias twp_unfold]
theorem unfold {s E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ⊣⊢ pre s (TotalWp.totalWp (PROP := IProp GF) s) E e Φ := by
  change bi_least_fixpoint (pre' (ι := ι) s) ((E, e), Φ) ⊣⊢ _
  exact BI.equiv_iff.1 (least_fixpoint_unfold (pre' (ι := ι) s))

@[rocq_alias twp_ind]
theorem induction (s : Stuckness)
    (Ψ : CoPset → Expr → (Val → IProp GF) → IProp GF)
    [HΨ : NonExpansive (fun x : Args Expr Val GF => Ψ x.1.1 x.1.2 x.2)] :
    (⊢ □ (∀ E e Φ,
      pre s (fun E e Φ => iprop(Ψ E e Φ ∧ WP e @ s ; E [{ Φ }])) E e Φ -∗
      Ψ E e Φ)) →
    ⊢ ∀ E e Φ, WP e @ s ; E [{ Φ }] -∗ Ψ E e Φ := by
  intro H
  have H' : ⊢ □ (∀ E e Φ,
      pre s (fun E e Φ =>
        iprop(Ψ E e Φ ∧ bi_least_fixpoint (pre' (ι := ι) s) ((E, e), Φ)))
        E e Φ -∗ Ψ E e Φ) := by
    simpa only [TotalWp.totalWp, instTotalWp, get] using H
  iintro %E %e %Φ
  change ⊢ bi_least_fixpoint (pre' (ι := ι) s) ((E, e), Φ) -∗ Ψ E e Φ
  iintro Htwp
  iapply least_fixpoint_ind (F := pre' (ι := ι) s)
      (Φ := fun x => Ψ x.1.1 x.1.2 x.2) $$ [] Htwp
  iintro !> %x
  rcases x with ⟨⟨E, e⟩, Φ⟩
  simp only [pre']
  iintro Hx
  iapply H'
  iexact Hx

@[rocq_alias twp_ne]
instance ne {s : Stuckness} {E} {e : Expr} :
    NonExpansive (TotalWp.totalWp (PROP := IProp GF) s E e) where
  ne {n Φ₁ Φ₂} HΦ := by
    change bi_least_fixpoint (pre' (ι := ι) s) ((E, e), Φ₁) ≡{n}≡
      bi_least_fixpoint (pre' (ι := ι) s) ((E, e), Φ₂)
    apply NonExpansive.ne
    exact ⟨⟨.rfl, .rfl⟩, fun v => HΦ v⟩

@[rocq_alias twp_value_fupd']
theorem value_fupd' {s : Stuckness} {E} {Φ : Val → IProp GF} {v : Val} :
    WP (v : Expr) @ s ; E [{ Φ }] ⊣⊢ |={E}=> Φ v := by
  simp [unfold.to_eq, pre, toVal_coe, BI.BIBase.BiEntails.rfl]

@[rocq_alias twp_strong_mono]
theorem strong_mono {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr}
    {Φ Ψ : Val → IProp GF} (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ WP e @ s₁ ; E₁ [{ Φ }] -∗
      (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ [{ Ψ }] := by
  let Pred := fun (E : CoPset) (e : Expr) (Φ : Val → IProp GF) => iprop(
    ∀ E₂ Ψ, ⌜E ⊆ E₂⌝ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗
      WP e @ s₂ ; E₂ [{ Ψ }])
  have hPred : NonExpansive
      (fun x : Args Expr Val GF => Pred x.1.1 x.1.2 x.2) := by
    constructor
    intro n x y h
    rcases x with ⟨⟨EX, eX⟩, ΦX⟩
    rcases y with ⟨⟨EY, eY⟩, ΦY⟩
    rcases h with ⟨⟨hE', he'⟩, hΦ⟩
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
  letI := hPred
  iintro H HΦ
  iapply induction s₁ Pred (ι := ι) ?_ $$ H
  · iintro !> %E %e₁ %Φ₁ IH %E' %Ψ' %hE'
    rw [unfold.to_eq]
    unfold pre
    cases hval : toVal e₁ with
    | some v =>
      dsimp only
      iintro HpostSome
      imod fupd_mask_mono hE' $$ IH with HΦv
      iapply HpostSome $$ HΦv
    | none =>
      dsimp only
      iintro HpostNone
      iintro %σ₁ %ns %obs %nt Hσ
      imod fupd_mask_subseteq hE' with Hclose
      imod IH $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      isplit
      · ipureintro
        simp only [LE.le] at hs
        grind [cases Stuckness]
      · iintro %κ %e₂ %σ₂ %eₜ %Hprim
        imod Hstep $$ %κ %e₂ %σ₂ %eₜ %Hprim with
          ⟨%hκ, Hσ, He₂, Hefs⟩
        imod Hclose
        imodintro
        iframe %hκ Hσ
        isplitl [He₂ HpostNone]
        · icases He₂ with ⟨IH₂, -⟩
          iapply IH₂ $$ %E' %Ψ' %hE' HpostNone
        · iapply BI.BigSepL.bigSepL_impl $$ Hefs
          iintro !> %k %ef %Hef Hef
          icases Hef with ⟨IHef, -⟩
          iapply IHef $$ %⊤ %ι.forkPost %LawfulSet.subset_refl
          iintro %v Hv
          imodintro
          iexact Hv
  · ipureintro
    exact hE
  · iexact HΦ

@[rocq_alias fupd_twp]
theorem fupd_twp {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> WP e @ s ; E [{ Φ }]) ⊢ WP e @ s ; E [{ Φ }] := by
  rw [unfold.to_eq]
  iintro H
  unfold pre
  cases toVal e
  · iintro %σ %ns %obs %nt Hσ
    imod H with H
    iapply H $$ Hσ
  · imod H
    iassumption

@[rocq_alias twp_fupd]
theorem twp_fupd {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E [{ v, |={E}=> Φ v }] ⊢ WP e @ s ; E [{ Φ }] := by
  iintro H
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %v Hv
  iexact Hv

@[rocq_alias twp_atomic]
theorem atomic {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}
    {Φ : Val → IProp GF} [hatom : Language.Atomic ↑s e] :
    (|={E₁,E₂}=> WP e @ s ; E₂ [{ v, |={E₂,E₁}=> Φ v }])
      ⊢ WP e @ s ; E₁ [{ Φ }] := by
  rw [unfold.to_eq, unfold.to_eq]
  iintro H
  unfold pre
  cases he : toVal e with
  | some v =>
    dsimp only
    imod H
    imod H
    iassumption
  | none =>
    dsimp only
    iintro %σ₁ %ns %obs %nt Hσ
    imod H
    imod H $$ Hσ with ⟨%Hred, Hstep⟩
    imodintro
    iframe %Hred
    cases s
    · iintro %κ %e₂ %σ₂ %eₜ %Hprim
      imod Hstep $$ %κ %e₂ %σ₂ %eₜ %Hprim with
        ⟨%hκ, Hσ, He₂, Hefs⟩
      cases he₂ : toVal e₂ with
      | some v₂ =>
        icases unfold $$ He₂ with He₂
        simp only [pre, he₂]
        imod He₂
        imod He₂
        imodintro
        iframe %hκ Hσ Hefs
        rw [unfold.to_eq]
        simp only [pre, he₂]
        imodintro
        iexact He₂
      | none =>
        icases unfold $$ He₂ with He₂
        simp only [pre, he₂]
        imod He₂ $$ %σ₂ %(ns + 1) %obs %(nt + eₜ.length) Hσ with
          ⟨%Hred₂, _⟩
        exact (Language.not_reducible_iff_irreducible.mpr
          (hatom.atomic Hprim))
          (Language.reducible_of_reducibleNoObs Hred₂) |>.elim
    · iintro %κ %e₂ %σ₂ %eₜ %Hprim
      imod Hstep $$ %κ %e₂ %σ₂ %eₜ %Hprim with
        ⟨%hκ, Hσ, He₂, Hefs⟩
      have ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp (hatom.atomic Hprim)
      icases unfold $$ He₂ with He₂
      simp only [pre, hv₂]
      imod He₂
      imod He₂
      imodintro
      iframe %hκ Hσ Hefs
      rw [unfold.to_eq]
      simp only [pre, hv₂]
      imodintro
      iexact He₂

@[rocq_alias twp_bind]
theorem bind (K : Expr → Expr) [ctx : Language.Context K]
    {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    TotalWp.totalWp s E e
      (fun v : Val => iprop(WP (K (v : Expr)) @ s ; E [{ Φ }]))
      ⊢ WP (K e) @ s ; E [{ Φ }] := by
  let Pred := fun (E : CoPset) (e : Expr) (Ψ : Val → IProp GF) => iprop(
    ∀ Φ, (∀ v, Ψ v -∗ WP (K (v : Expr)) @ s ; E [{ Φ }]) -∗
      WP (K e) @ s ; E [{ Φ }])
  have hPred : NonExpansive
      (fun x : Args Expr Val GF => Pred x.1.1 x.1.2 x.2) := by
    constructor
    intro n x y hxy
    rcases x with ⟨⟨EX, eX⟩, ΨX⟩
    rcases y with ⟨⟨EY, eY⟩, ΨY⟩
    rcases hxy with ⟨⟨hE, he⟩, hΨ⟩
    change EX = EY at hE
    change eX = eY at he
    subst EY
    subst eY
    refine BI.forall_ne fun _ => ?_
    refine BI.wand_ne.ne ?_ .rfl
    refine BI.forall_ne fun v => ?_
    exact BI.wand_ne.ne (hΨ v) .rfl
  letI := hPred
  iintro H
  iapply induction s Pred (ι := ι) ?_ $$ H
  · iintro !> %E %e %Ψ
    cases he : toVal e with
    | some v =>
      simp only [pre, he]
      iintro Hpre %Φ Hcont
      have heq := ToVal.coe_of_toVal_eq_some he
      rw [← heq]
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
        imod Hstep $$ %κ %e₂' %σ₂ %eₜ %Hprim with
          ⟨%hκ, Hσ, He₂, Hefs⟩
        imodintro
        iframe %hκ Hσ
        isplitl [He₂ Hcont]
        icases He₂ with ⟨IH, -⟩
        iapply IH $$ %Φ Hcont
        iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %Hef Hef
        icases Hef with ⟨-, Hef⟩
        iexact Hef
  · iintro %v Hv
    iexact Hv

private theorem fold_induction_right
    (Ψ : CoPset → Expr → (Val → IProp GF) → IProp GF)
    (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    (match toVal e with
    | some v => iprop(|={E}=> Φ v)
    | none => iprop(
        ∀ (σ₁ : State) (ns : Nat) (obs : List Obs) (nt : Nat),
          stateInterp σ₁ ns obs nt ={E,∅}=∗
          ⌜s.MaybeReducibleNoObs (e, σ₁)⌝ ∗
          ∀ (κ : List Obs) e₂ σ₂ eₜ,
            ⌜(e, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
            ⌜κ = []⌝ ∗
            stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
            (Ψ E e₂ Φ ∧ WP e₂ @ s ; E [{ Φ }]) ∗
            [∗list] e' ∈ eₜ,
              (Ψ ⊤ e' ι.forkPost ∧
                WP e' @ s ; ⊤ [{ ι.forkPost }]))) ⊢
    WP e @ s ; E [{ Φ }] := by
  rw [unfold.to_eq]
  unfold pre
  cases hval : toVal e with
  | some =>
      exact .rfl
  | none =>
      iintro H
      iintro %σ₁ %ns %obs %nt Hσ
      imod H $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      iframe %Hred
      iintro %κ %e₂ %σ₂ %eₜ %Hprim
      imod Hstep $$ %κ %e₂ %σ₂ %eₜ %Hprim with
        ⟨%hκ, Hσ, He₂, Hefs⟩
      imodintro
      iframe %hκ Hσ
      isplitl [He₂]
      · icases He₂ with ⟨-, He₂⟩
        iexact He₂
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %Hef Hef
        icases Hef with ⟨-, Hef⟩
        iexact Hef

@[rocq_alias twp_bind_inv]
theorem bind_inv (K : Expr → Expr) [ctx : Language.Context K]
    {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    WP (K e) @ s ; E [{ Φ }] ⊢
      TotalWp.totalWp s E e
        (fun v : Val => iprop(WP (K (v : Expr)) @ s ; E [{ Φ }])) := by
  let Pred := fun (E : CoPset) (e' : Expr) (Φ : Val → IProp GF) => iprop(
    ∀ e, ⌜e' = K e⌝ -∗
      TotalWp.totalWp s E e
        (fun v : Val => iprop(WP (K (v : Expr)) @ s ; E [{ Φ }])))
  have hPred : NonExpansive
      (fun x : Args Expr Val GF => Pred x.1.1 x.1.2 x.2) := by
    constructor
    intro n x y hxy
    rcases x with ⟨⟨EX, eX⟩, ΦX⟩
    rcases y with ⟨⟨EY, eY⟩, ΦY⟩
    rcases hxy with ⟨⟨hE, he⟩, hΦ⟩
    change EX = EY at hE
    change eX = eY at he
    subst EY
    subst eY
    refine BI.forall_ne fun _ => ?_
    refine BI.wand_ne.ne .rfl ?_
    apply NonExpansive.ne
    exact fun _ => NonExpansive.ne hΦ
  letI := hPred
  iintro H
  iapply induction s Pred (ι := ι) ?_ $$ H %e %rfl
  iintro !> %E %e' %Φ IH %e %heq
  subst e'
  rw [unfold.to_eq]
  unfold pre
  cases he : toVal e with
  | some v =>
      dsimp only
      have heq := ToVal.coe_of_toVal_eq_some he
      subst e
      imodintro
      iapply fold_induction_right Pred s E (K (v : Expr)) Φ
      iexact IH
  | none =>
      dsimp only
      have hK : toVal (K e) = none := ctx.toVal_eq_none_fill he
      let unfolded := iprop(
        ∀ (σ₁ : State) (ns : Nat) (obs : List Obs) (nt : Nat),
            stateInterp σ₁ ns obs nt ={E,∅}=∗
            ⌜s.MaybeReducibleNoObs (K e, σ₁)⌝ ∗
            ∀ (κ : List Obs) e₂ σ₂ eₜ,
              ⌜(K e, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
              ⌜κ = []⌝ ∗
              stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
              (Pred E e₂ Φ ∧ WP e₂ @ s ; E [{ Φ }]) ∗
              [∗list] e' ∈ eₜ,
                (Pred ⊤ e' ι.forkPost ∧
                  WP e' @ s ; ⊤ [{ ι.forkPost }]))
      have hIH :
          (match toVal (K e) with
          | some v => iprop(|={E}=> Φ v)
          | none => unfolded) ⊢ unfolded := by
        simp only [hK]
        exact .rfl
      icases hIH $$ IH with IH
      iintro %σ₁ %ns %obs %nt Hσ
      imod IH $$ Hσ with ⟨%Hred, Hstep⟩
      imodintro
      isplit
      · ipureintro
        cases s
        · exact Language.Context.reducibleNoObs_fill_inv (K := K) he Hred
        · trivial
      · iintro %κ %e₂ %σ₂ %eₜ %Hprim
        imod Hstep $$ %κ %(K e₂) %σ₂ %eₜ
          %(ctx.primStep_fill Hprim) with ⟨%hκ, Hσ, He₂, Hefs⟩
        imodintro
        iframe %hκ Hσ
        isplitl [He₂]
        · icases He₂ with ⟨IH₂, -⟩
          iapply IH₂ $$ %e₂ %rfl
        · iapply BI.BigSepL.bigSepL_impl $$ Hefs
          iintro !> %k %ef %Hef Hef
          icases Hef with ⟨-, Hef⟩
          iexact Hef

@[rocq_alias twp_mono]
theorem mono {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF}
    (H : ∀ v, Φ v ⊢ Ψ v) :
    WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ Ψ }] := by
  iintro Hwp
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ Hwp
  iintro %v Hv
  imodintro
  iapply H v
  iexact Hv

@[rocq_alias twp_stuck_mono]
theorem stuck_mono {s₁ s₂ : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF}
    (H : s₁ ≤ s₂) :
    WP e @ s₁ ; E [{ Φ }] ⊢ WP e @ s₂ ; E [{ Φ }] := by
  iintro Hwp
  iapply strong_mono H LawfulSet.subset_refl $$ Hwp
  iintro %v Hv
  imodintro
  iexact Hv

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
  iintro %v Hv
  imodintro
  iexact Hv

@[rocq_alias twp_value_fupd]
theorem value_fupd {s : Stuckness} {E} {e : Expr} {v : Val}
    {Φ : Val → IProp GF} (h : e = (v : Expr)) :
    WP e @ s ; E [{ Φ }] ⊣⊢ |={E}=> Φ v := by
  subst e
  exact value_fupd'

@[rocq_alias twp_value']
theorem value' {s : Stuckness} {E} {v : Val} {Φ : Val → IProp GF} :
    Φ v ⊢ WP (v : Expr) @ s ; E [{ Φ }] := by
  rw [value_fupd'.to_eq]
  exact fupd_intro

@[rocq_alias twp_value]
theorem value {s : Stuckness} {E} {e : Expr} {v : Val} {Φ : Val → IProp GF}
    (h : e = (v : Expr)) : Φ v ⊢ WP e @ s ; E [{ Φ }] := by
  subst e
  exact value'

@[rocq_alias twp_frame_l]
theorem frame_l {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} :
    R ∗ WP e @ s ; E [{ Φ }] ⊢ WP e @ s ; E [{ v, R ∗ Φ v }] := by
  iintro ⟨HR, Hwp⟩
  iapply strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ Hwp
  iintro %v HΦ
  imodintro
  iframe

@[rocq_alias twp_frame_r]
theorem frame_r {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} :
    WP e @ s ; E [{ Φ }] ∗ R ⊢ WP e @ s ; E [{ v, Φ v ∗ R }] := by
  rw [(BI.sep_comm (P := WP e @ s ; E [{ Φ }]) (Q := R)).to_eq]
  refine frame_l.trans ?_
  apply mono
  intro v
  exact BI.sep_comm.mp

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
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s ; E [{ Φ }] ⊢
      WP e @ s ; E [{ Ψ }] := by
  iintro ⟨H, Hwp⟩
  iapply wand $$ Hwp H

@[rocq_alias twp_wand_r]
theorem wand_r {s : Stuckness} {E} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E [{ Φ }] ∗ (∀ v, Φ v -∗ Ψ v) ⊢
      WP e @ s ; E [{ Ψ }] := by
  iintro ⟨Hwp, H⟩
  iapply wand $$ Hwp H

@[rocq_alias twp_frame_wand]
theorem frame_wand {s : Stuckness} {E} {e : Expr}
    {Φ : Val → IProp GF} {R : IProp GF} :
    R ⊢ (WP e @ s ; E [{ v, R -∗ Φ v }]) -∗
      WP e @ s ; E [{ Φ }] := by
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
  case some v =>
    iintro H
    iexact H
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
      ihave Hnext := H $$ %κ %e₂ %σ₂ %eₜ %Hstep
      iapply step_fupdN_intro Std.LawfulSet.empty_subset
      rw [(BI.later_laterN _).to_eq]
      iintro !>
      iapply BI.laterN_intro
      imod Hnext with ⟨%hκ, Hσ, He₂, Hefs⟩
      subst hκ
      simp only [List.nil_append]
      imodintro
      iframe Hσ
      isplitl [He₂]
      · iapply IH $$ He₂
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %Hef Hef
        iapply IH $$ Hef

section ProofMode

open ProofMode

variable {s : Stuckness} {E E₁ E₂ : CoPset} {e : Expr}
variable {Φ Ψ : Val → IProp GF} {P R : IProp GF}

@[rocq_alias frame_twp]
instance frameTwp {p : Bool} [H : ∀ v, Frame p R (Φ v) (Ψ v)] :
    Frame p R (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Ψ }]) where
  frame := by
    refine frame_l.trans ?_
    apply mono
    exact fun v => (H v).frame

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
    ElimModal True p io false iprop(|={E}=> P) P
      (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Φ }]) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply fupd_twp
    imod H
    imodintro
    iapply G $$ H

@[rocq_alias elim_modal_bupd_twp]
instance elimModalBupdTwp p :
    ElimModal True p io false iprop(|==> P) P
      (WP e @ s ; E [{ Φ }]) (WP e @ s ; E [{ Φ }]) where
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
      (WP e @ s ; E₁ [{ Φ }])
      (WP e @ s ; E₂ [{ v, |={E₂,E₁}=> Φ v }]) where
  elim_modal := by
    rintro hatomic
    iintro ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply atomic
    imod H
    imodintro
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
