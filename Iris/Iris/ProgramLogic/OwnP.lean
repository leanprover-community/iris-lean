/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.Lib.ExclAuth
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.EctxLifting

/-!
# Iris-2.0-style ownership of the global state

This module provides an interface to handling ownership of the global state that
works more like Iris 2.0 did. The state interpretation (in WP) is fixed to be
authoritative ownership of the entire state (using the `Excl` RA). Users can
then put the corresponding fragment into an invariant on their own to establish
a more interesting notion of ownership, such as the standard heap with disjoint
union.
-/

namespace Iris.ProgramLogic

open BI ExclAuth Language Language.Notation Std.LawfulSet

@[expose] public section

/-- The ghost state of `ownP`: exclusive authoritative ownership of a state. -/
abbrev ownPRF (State : Type) : COFE.OFunctorPre := constOF (ExclAuthR (A := stateO State))

/-- Unlike Iris Rocq's `ownPGS Λ Σ`, this is indexed by the state rather than by the language:
`ownP` owns a state and nothing else, so keying the class on the language would leave it
undetermined at every use site. The language enters only through `ownPG_irisGS`.

As in Iris Rocq, `invGS` is fixed at `HasLC` and is a plain field rather than a parent: making
it an instance would give `InvGS_gen` a second resolution path alongside `IrisGS_gen.invGS`. -/
@[rocq_alias ownPGS]
class OwnPGS (State : Type) (GF : BundledGFunctors) where
  -- not an instance on purpose to avoid diamonds with `IrisGS_gen`
  [invGS : InvGS GF]
  [inG : ElemG GF (ownPRF State)]
  name : GName

attribute [reducible, instance] OwnPGS.inG

/-- Indexed by the state rather than by the language, like `OwnPGS`. -/
@[rocq_alias ownPGpreS]
class OwnPGpreS (State : Type) (GF : BundledGFunctors) extends InvGpreS GF where
  inG : ElemG GF (ownPRF State)

attribute [reducible, instance] OwnPGpreS.inG

#rocq_ignore «ownPΣ» "Superseded by the `OwnPGpreS` typeclass on `BundledGFunctors`."
#rocq_ignore «subG_ownPΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."
#rocq_ignore ownp.reducible_not_val_inhabitant "Rocq-specific `auto` resolve hint; not needed."

variable {Expr : Type _} {State : Type} {Obs Val : Type _}
variable {GF : BundledGFunctors}

section Language

variable [Language Expr State Obs Val]

/-- The side condition of the `ownP` lifting lemmas: a `NotStuck` expression must be reducible,
a `MaybeStuck` one must at least not be a value. Contrast `Stuckness.MaybeReducible`, which is
always accompanied by a separate "not a value" hypothesis. -/
abbrev ReducibleOrNotVal : Stuckness → Expr × State → Prop
  | .NotStuck, ρ => PrimStep.Reducible ρ
  | _, (e, _) => toVal e = none

@[rocq_alias ownPG_irisGS]
instance ownPG_irisGS [ι : OwnPGS State GF] : IrisGS_gen .hasLC Expr GF where
  toStateInterp := ⟨fun σ _ _ _ => iOwn (E := ι.inG) ι.name (●E ⟨σ⟩)⟩
  invGS := ι.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := let _ := ι.invGS; fupd_intro

/-! ## Ownership -/

@[rocq_alias ownP]
def ownP [ι : OwnPGS State GF] (σ : State) : IProp GF :=
  iOwn (E := ι.inG) ι.name (◯E ⟨σ⟩)

/-! ## Adequacy -/

@[rocq_alias ownP_adequacy]
theorem ownP_adequacy [OwnPGpreS State GF] (s : Stuckness) (e : Expr) (σ : State) (φ : Val → Prop)
    (Hwp : ∀ [OwnPGS State GF], ownP (GF := GF) σ ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate s e σ (fun v _ => φ v) := by
  unfold ownP at Hwp
  refine wp_adequacy (GF := GF) s e σ φ ?_
  intro _ κs
  imod iOwn_alloc (F := ownPRF State)
    ((●E (⟨σ⟩ : stateO State)) • ◯E (⟨σ⟩ : stateO State)) valid with ⟨%γ, Hσ, Hσf⟩
  letI : OwnPGS State GF := ⟨γ⟩
  imodintro
  iexists (fun σ (_ : List Obs) => iOwn (F := ownPRF State) γ (●E ⟨σ⟩)), (fun _ => iprop(True))
  iframe Hσ
  iapply Hwp $$ [$Hσf]

@[rocq_alias ownP_invariance]
theorem ownP_invariance [OwnPGpreS State GF] (s : Stuckness) (e : Expr) (σ₁ : State)
    (t₂ : List Expr) (σ₂ : State) (φ : State → Prop)
    (Hwp : ∀ [OwnPGS State GF],
      ownP (GF := GF) σ₁ ={⊤}=∗ WP e @ s; ⊤ {{ _v, True }} ∗ |={⊤,∅}=> ∃ σ', ownP σ' ∧ ⌜φ σ'⌝)
    (Hsteps : ([e], σ₁) -·->ₜₚ* (t₂, σ₂)) :
    φ σ₂ := by
  unfold ownP at Hwp
  refine wp_invariance (GF := GF) s e σ₁ σ₂ t₂ _ ?_ Hsteps
  intro _ κs
  imod iOwn_alloc (F := ownPRF State)
    ((●E (⟨σ₁⟩ : stateO State)) • ◯E (⟨σ₁⟩ : stateO State)) valid with ⟨%γ, Hσ, Hσf⟩
  letI : OwnPGS State GF := ⟨γ⟩
  imod Hwp $$ [$Hσf] with ⟨Hwp, Hφ⟩
  imodintro
  iexists (fun σ (_ : List Obs) (_ : Nat) => iOwn (F := ownPRF State) γ (●E ⟨σ⟩)),
    (fun _ => iprop(True))
  iframe Hσ Hwp
  iintro Hσ
  iexists ∅
  imod Hφ with ⟨%σ', Hσf, %Hφ⟩
  icombine Hσ Hσf gives %Hvalid
  ipureintro; exact DiscreteO.eqv_inj (agree Hvalid) ▸ Hφ

/-! ## Lifting

All lifting lemmas defined here discard later credits. -/

section Lifting

variable [ι : OwnPGS State GF]
variable {s : Stuckness} {E : CoPset} {e e₁ e₂ : Expr} {Φ : Val → IProp GF}
variable {σ σ₁ σ₂ : State} {ns nt : Nat} {κs : List Obs}

theorem stateInterp_eq : stateInterp σ₁ ns κs nt = iOwn (E := ι.inG) ι.name (●E ⟨σ₁⟩) := rfl

@[rocq_alias ownP_eq]
theorem ownP_eq : ⊢@{IProp GF} stateInterp σ₁ ns κs nt -∗ ownP σ₂ -∗ ⌜σ₁ = σ₂⌝ := by
  simp only [stateInterp_eq, ownP]
  iintro Hauth Hfrag
  icombine Hauth Hfrag gives %Hvalid
  ipureintro; exact DiscreteO.eqv_inj (agree Hvalid)

@[rocq_alias ownP_state_twice]
theorem ownP_state_twice : ownP σ₁ ∗ ownP σ₂ ⊢ (False : IProp GF) := by
  unfold ownP
  iintro ⟨H₁, H₂⟩
  icombine H₁ H₂ gives %Hvalid
  exact (frag_op_valid.mp Hvalid).elim

@[rocq_alias ownP_timeless]
instance ownP_timeless : Timeless (ownP (GF := GF) σ) := by unfold ownP; infer_instance

@[rocq_alias ownP_lift_step]
theorem ownP_lift_step :
    (|={E,∅}=> ∃ σ₁, ⌜ReducibleOrNotVal s (e₁, σ₁)⌝ ∗ ▷ ownP σ₁ ∗
      ▷ ∀ obs e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗ ownP σ₂ ={∅,E}=∗
        WP e₂ @ s; E {{ Φ }} ∗ [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  unfold ownP
  iintro H
  cases hv : toVal e₁
  · iapply wp_lift_step hv
    iintro %σ₁ %ns %obs %obs' %nt Hσ
    imod H with ⟨%σ₁', %Hsafe, >Hσf, Hcont⟩
    isimp only [stateInterp_eq] at Hσ
    icombine Hσ Hσf gives %Hvalid
    obtain rfl := DiscreteO.eqv_inj (agree Hvalid)
    imodintro
    isplit
    · ipureintro; cases s <;> grind
    iintro !> %e₂ %σ₂ %eₜ %Hstep Hcred
    imod iOwn_update_op (update (a' := ⟨σ₂⟩)) $$ [$Hσ $Hσf] with ⟨Hσ, Hσf⟩
    iframe Hσ
    iapply Hcont $$ %obs %e₂ %σ₂ %eₜ %Hstep Hσf
  · iapply fupd_wp
    imod H with ⟨%σ₁, %Hsafe, -⟩
    cases s <;> grind

@[rocq_alias ownP_lift_stuck]
theorem ownP_lift_stuck :
    (|={E,∅}=> ∃ σ, ⌜PrimStep.Stuck (e, σ)⌝ ∗ ▷ ownP σ) ⊢ WP e @ E ?{{ Φ }} := by
  iintro H
  cases hv : toVal e
  · iapply wp_lift_stuck hv
    iintro %σ %ns %obs' %nt Hσ
    imod H with ⟨%σ', %Hstuck, >Hσf⟩
    icases ownP_eq $$ Hσ Hσf with %rfl
    imodintro
    itrivial
  · iapply fupd_wp
    imod H with ⟨%σ, %⟨Hnv, _⟩, -⟩
    grind

@[rocq_alias ownP_lift_pure_step]
theorem ownP_lift_pure_step [Inhabited State] (Hsafe : ∀ σ₁, ReducibleOrNotVal s (e₁, σ₁))
    (Hpure : ∀ σ₁ obs e₂ σ₂ eₜ, (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) → obs = [] ∧ σ₂ = σ₁) :
    (▷ ∀ obs e₂ eₜ σ, ⌜(e₁, σ) -<obs>-> (e₂, σ, eₜ)⌝ →
      WP e₂ @ s; E {{ Φ }} ∗ [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_step (by have := Hsafe default; cases s <;> grind)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplit
  · ipureintro; cases s <;> grind
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨rfl, rfl⟩ := Hpure _ _ _ _ _ Hstep
  imod Hclose
  imodintro
  iframe Hσ
  iapply H $$ %_ %_ %_ %_ [//]

/-! ### Derived lifting lemmas -/

@[rocq_alias ownP_lift_atomic_step]
theorem ownP_lift_atomic_step (Hsafe : ReducibleOrNotVal s (e₁, σ₁)) :
    (▷ ownP σ₁ ∗
      ▷ ∀ obs e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗ ownP σ₂ -∗
        (toVal e₂).elim iprop(False) Φ ∗ [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro ⟨Hσ, H⟩
  iapply ownP_lift_step
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  iexists σ₁
  iframe Hσ %Hsafe
  iintro !> %obs %e₂ %σ₂ %eₜ %Hstep Hσ₂
  icases H $$ %obs %e₂ %σ₂ %eₜ %Hstep Hσ₂ with ⟨HΦ, $⟩
  cases hv : toVal e₂ <;> simp only [Option.elim_none, Option.elim_some]
  · iexfalso
    iexact HΦ
  · imod Hclose
    imodintro
    iapply wp_value ⟨coe_of_toVal_eq_some hv⟩
    iexact HΦ

@[rocq_alias ownP_lift_atomic_det_step]
theorem ownP_lift_atomic_det_step {v₂ : Val} {eₜ : List Expr}
    (Hsafe : ReducibleOrNotVal s (e₁, σ₁))
    (Hdet : ∀ obs' e₂' σ₂' eₜ', (e₁, σ₁) -<obs'>-> (e₂', σ₂', eₜ') →
      σ₂' = σ₂ ∧ toVal e₂' = some v₂ ∧ eₜ' = eₜ) :
    ▷ ownP σ₁ ∗ ▷ (ownP σ₂ -∗ Φ v₂ ∗ [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro ⟨Hσ₁, Hσ₂⟩
  iapply ownP_lift_atomic_step Hsafe
  iframe Hσ₁
  iintro !> %obs' %e₂' %σ₂' %eₜ' %Hstep Hσ₂'
  obtain ⟨rfl, hv, rfl⟩ := Hdet _ _ _ _ Hstep
  simp only [hv, Option.elim_some]
  iapply Hσ₂ $$ Hσ₂'

@[rocq_alias ownP_lift_atomic_det_step_no_fork]
theorem ownP_lift_atomic_det_step_no_fork {v₂ : Val} (Hsafe : ReducibleOrNotVal s (e₁, σ₁))
    (Hdet : ∀ obs' e₂' σ₂' eₜ', (e₁, σ₁) -<obs'>-> (e₂', σ₂', eₜ') →
      σ₂' = σ₂ ∧ toVal e₂' = some v₂ ∧ eₜ' = []) :
    {{ ▷ ownP (GF := GF) σ₁ }} e₁ @ s; E {{ RET v₂; ownP σ₂ }} := by
  iintro %Φ Hσ₁ Hσ₂
  iapply ownP_lift_atomic_det_step (eₜ := []) Hsafe Hdet
  iframe Hσ₁
  iintro !> Hσ
  simp only [Algebra.BigOpL.bigOpL_nil]
  icases Hσ₂ $$ Hσ with $

@[rocq_alias ownP_lift_pure_det_step_no_fork]
theorem ownP_lift_pure_det_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, ReducibleOrNotVal s (e₁, σ₁))
    (Hpuredet : ∀ σ₁ obs e₂' σ₂ eₜ', (e₁, σ₁) -<obs>-> (e₂', σ₂, eₜ') →
      obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = []) :
    ▷ WP e₂ @ s; E {{ Φ }} ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_lift_pure_det_step_no_fork E (by cases s <;> exact Hsafe) Hpuredet
  iapply step_fupd_intro subset_refl
  iintro !> - {$Hwp}

end Lifting

end Language

/-! ## Lifting for evaluation-context languages -/

section EctxLifting

open EctxLanguage EctxLanguage.Notation

variable {Ectx : Type _} [EctxLanguage Expr Ectx State Obs Val]
variable [OwnPGS State GF]
variable {s : Stuckness} {E : CoPset} {e e₁ e₂ : Expr} {σ σ₁ σ₂ : State} {Φ : Val → IProp GF}

theorem reducibleOrNotVal_of_baseStep_reducible (Hbred : BaseStep.Reducible (e, σ)) :
    ReducibleOrNotVal s (e, σ) :=
  let h := primStep_reducible_of_baseStep_reducible Hbred
  match s with
  | .NotStuck => h
  | .MaybeStuck => toVal_none_of_reducible h

@[rocq_alias ownP_lift_base_step]
theorem ownP_lift_base_step :
    (|={E,∅}=> ∃ σ₁, ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗ ▷ ownP σ₁ ∗
      ▷ ∀ obs e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ ownP σ₂ ={∅,E}=∗
        WP e₂ @ s; E {{ Φ }} ∗ [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply ownP_lift_step
  imod H with ⟨%σ₁, %Hbred, >Hσ₁, Hwp⟩
  imodintro
  iexists σ₁
  isplit
  · ipureintro; exact reducibleOrNotVal_of_baseStep_reducible Hbred
  iframe Hσ₁
  iintro !> %obs %e₂ %σ₂ %eₜ %Hstep Hσ₂
  iapply Hwp $$ %_ %_ %_ %_ %(baseStep_of_primStep_of_baseStep_reducible Hbred Hstep) Hσ₂

@[rocq_alias ownP_lift_base_stuck]
theorem ownP_lift_base_stuck (Hsav : SubredexesAreValues e) :
    (|={E,∅}=> ∃ σ, ⌜BaseStep.Stuck (e, σ)⌝ ∗ ▷ ownP σ) ⊢ WP e @ E ?{{ Φ }} := by
  iintro H
  iapply ownP_lift_stuck
  imod H with ⟨%σ, %Hstuck, Hσ⟩
  imodintro
  iexists σ
  iframe Hσ
  ipureintro; exact primStep_stuck_of_baseStep_stuck Hstuck Hsav

@[rocq_alias ownP_lift_pure_base_step]
theorem ownP_lift_pure_base_step [Inhabited State] (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpure : ∀ σ₁ obs e₂ σ₂ eₜ, (e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) → obs = [] ∧ σ₂ = σ₁) :
    (▷ ∀ obs e₂ eₜ σ, ⌜(e₁, σ) -<obs>->ᵇ (e₂, σ, eₜ)⌝ →
      WP e₂ @ s; E {{ Φ }} ∗ [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply ownP_lift_pure_step (fun σ => reducibleOrNotVal_of_baseStep_reducible (Hbred σ))
    fun σ _ _ _ _ h => Hpure _ _ _ _ _ (baseStep_of_primStep_of_baseStep_reducible (Hbred σ) h)
  iintro !> %obs %e₂ %eₜ %σ %Hstep
  iapply H $$ %_ %_ %_ %_
  ipureintro; exact baseStep_of_primStep_of_baseStep_reducible (Hbred σ) Hstep

@[rocq_alias ownP_lift_atomic_base_step]
theorem ownP_lift_atomic_base_step (Hbred : BaseStep.Reducible (e₁, σ₁)) :
    (▷ ownP σ₁ ∗
      ▷ ∀ obs e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ ownP σ₂ -∗
        (toVal e₂).elim iprop(False) Φ ∗ [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro ⟨Hσ, H⟩
  iapply ownP_lift_atomic_step (reducibleOrNotVal_of_baseStep_reducible Hbred)
  iframe Hσ
  iintro !> %obs %e₂ %σ₂ %eₜ %Hstep Hσ₂
  iapply H $$ %_ %_ %_ %_ %(baseStep_of_primStep_of_baseStep_reducible Hbred Hstep) Hσ₂

@[rocq_alias ownP_lift_atomic_det_base_step]
theorem ownP_lift_atomic_det_base_step {v₂ : Val} {eₜ : List Expr}
    (Hbred : BaseStep.Reducible (e₁, σ₁))
    (Hdet : ∀ obs' e₂' σ₂' eₜ', (e₁, σ₁) -<obs'>->ᵇ (e₂', σ₂', eₜ') →
      σ₂' = σ₂ ∧ toVal e₂' = some v₂ ∧ eₜ' = eₜ) :
    ▷ ownP σ₁ ∗ ▷ (ownP σ₂ -∗ Φ v₂ ∗ [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} :=
  ownP_lift_atomic_det_step (reducibleOrNotVal_of_baseStep_reducible Hbred)
    fun _ _ _ _ h => Hdet _ _ _ _ (baseStep_of_primStep_of_baseStep_reducible Hbred h)

@[rocq_alias ownP_lift_atomic_det_base_step_no_fork]
theorem ownP_lift_atomic_det_base_step_no_fork {v₂ : Val} {obs : List Obs}
    (Hbred : BaseStep.Reducible (e₁, σ₁))
    (Hdet : ∀ obs' e₂' σ₂' eₜ', (e₁, σ₁) -<obs'>->ᵇ (e₂', σ₂', eₜ') →
      obs' = obs ∧ σ₂' = σ₂ ∧ toVal e₂' = some v₂ ∧ eₜ' = []) :
    {{ ▷ ownP (GF := GF) σ₁ }} e₁ @ s; E {{ RET v₂; ownP σ₂ }} :=
  ownP_lift_atomic_det_step_no_fork (reducibleOrNotVal_of_baseStep_reducible Hbred)
    fun _ _ _ _ h => (Hdet _ _ _ _ (baseStep_of_primStep_of_baseStep_reducible Hbred h)).2

@[rocq_alias ownP_lift_pure_det_base_step_no_fork]
theorem ownP_lift_pure_det_base_step_no_fork [Inhabited State]
    (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpuredet : ∀ σ₁ obs e₂' σ₂ eₜ', (e₁, σ₁) -<obs>->ᵇ (e₂', σ₂, eₜ') →
      obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = []) :
    ▷ WP e₂ @ s; E {{ Φ }} ⊢ WP e₁ @ s; E {{ Φ }} :=
  ownP_lift_pure_det_step_no_fork (fun σ => reducibleOrNotVal_of_baseStep_reducible (Hbred σ))
    fun σ _ _ _ _ h => Hpuredet _ _ _ _ _ (baseStep_of_primStep_of_baseStep_reducible (Hbred σ) h)

end EctxLifting

end
end Iris.ProgramLogic
