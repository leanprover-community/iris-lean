/-
Copyright (c) 2026 Fernando Leal, Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.WeakestPre

namespace Iris

open ProgramLogic Language.Notation Std

@[expose] public section

export StateInterp (stateInterp)

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

abbrev Stuckness.MaybeReducibleNoObs : Stuckness → Expr × State → Prop
| .NotStuck, (e₁, σ₁) => PrimStep.ReducibleNoObs (e₁, σ₁)
| _, _ => True

@[rocq_alias twp_pre]
def twp.pre (s : Stuckness) (wp : CoPset -> Expr -> (Val -> IProp GF) -> IProp GF) (E : CoPset)
    (e₁ : Expr) (Φ : Val -> IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(∀ (σ₁ : State) (ns : Nat) (obs' : List Obs) (nt : Nat),
    stateInterp σ₁ ns obs' nt ={E,∅}=∗
    ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
    ∀ obs e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ ={E,∅}=∗
      ⌜obs = []⌝ ∗ stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
      wp E e₂ Φ ∗ [∗list] e' ∈ eₜ, wp ⊤ e' ι.forkPost)

@[rocq_alias twp_pre_mono]
theorem twp.pre_mono (s : Stuckness) (wp₁ wp₂ : CoPset -> Expr -> (Val -> IProp GF) -> IProp GF) :
    ⊢ (□ ∀ E e Φ, wp₁ E e Φ -∗ wp₂ E e Φ) →
      ∀ E e Φ, twp.pre s wp₁ E e Φ -∗ twp.pre s wp₂ E e Φ := by
  iintro #H %E %e %Φ Hwp
  unfold pre
  split
  · iassumption
  · iintro %σ₁ %ns %obs' %nt Hσ
    imod Hwp $$ Hσ with ⟨$, Hwp⟩
    imodintro
    iintro %obs %e₂ %σ₂ %et Hstep
    imod Hwp $$ Hstep with ⟨$, Hσ, Hwp, Hfork⟩
    imodintro
    iframe Hσ
    isplitl [Hwp]
    · iapply H $$ Hwp
    · iapply BI.BigSepL.bigSepL_impl $$ Hfork
      iintro !> %k %e %_ Hwp
      iapply H $$ Hwp

open Function in
@[rocq_alias twp_pre']
def twp.pre' (s : Stuckness) (wp : (CoPset × Expr) × (Val -> IProp GF) -> IProp GF) :=
    uncurry <| uncurry <| @twp.pre hlc Expr State Obs Val Λ GF ι s (curry <| curry wp)
