module

public import Iris.ProofMode
public import Iris.ProgramLogic.WeakestPre

public section

namespace Iris.ProgramLogic

open Language.Notation BI

variable {hlc : outParam Bool}
variable {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

variable {s : Stuckness} {E E₁ E₂ : CoPset} {v : Val} {e e₁ e₂ : Expr}
variable {σ : State} {P Q : IProp GF} {Φ : Val → IProp GF}

@[rocq_alias wp_lift_step_fupdN]
theorem wp_lift_step_fupdN (h : toVal e₁ = none) :
  (∀ σ₁ ns (obs obs' : List Obs) nt,
    stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
    ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
    ∀ e₂ σ₂ eₜ,   ⌜(e₁, σ₁) -<obs>-> (e₂,σ₂, eₜ)⌝ -∗
      £ (ι.numLatersPerStep ns + 1) ={∅}▷=∗^[ι.numLatersPerStep ns + 1] |={∅,E}=>
      -- NOTE: Changed the order of `nt` and `eₜ.length` since in Lean
      -- we have `n + 0 = n` and not `0 + n = n`
      stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
      WP e₂ @ s; E {{ Φ }} ∗
      [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
  ⊢ WP e₁ @ s; E {{ Φ }} := by
  simp only [IProp.ext (wp_unfold (e := e₁)), wp.pre, h, BIBase.Entails.rfl]

@[rocq_alias wp_lift_step_fupd]
theorem wp_lift_step_fupd (h : toVal e₁ = none) :
  (∀ σ₁ ns (obs obs' : List Obs) nt,
    stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
    ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
    ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂,σ₂, eₜ)⌝ -∗
      £ 1 ={∅}=∗ ▷ |={∅,E}=>
      -- NOTE: Changed the order of `nt` and `eₜ.length` since in Lean
      -- we have `n + 0 = n` and not `0 + n = n`
      stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length ) ∗
      WP e₂ @ s; E {{ Φ }} ∗
      [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
  ⊢ WP e₁ @ s; E {{ Φ }} := by
  refine .trans ?_ <| wp_lift_step_fupdN h
  iintro Hwp %σ₁ %ns %obs %obs' %nt Hσ
  imod Hwp $$ Hσ with ⟨$, Hwp⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcred
  ihave Hcred := lc_weaken 1 (Nat.le_add_left 1 (ι.numLatersPerStep ns)) $$ Hcred
  refine .trans ?_ <| step_fupd_mono <|
    (laterN_intro _).trans <| step_fupdN_intro Std.LawfulSet.empty_subset
  iintro ⟨Hwp, Hcred⟩
  imod Hwp $$ %_ %_ %_ %Hstep Hcred with Hwp
  iapply step_fupd_intro Std.LawfulSet.empty_subset
  iassumption

theorem wp_lift_stuck (h : toVal e = none) :
    (∀ σ ns obs nt,
      stateInterp σ ns obs nt ={E,∅}=∗ ⌜PrimStep.Stuck (e,σ)⌝)
    ⊢ WP e @ E ? {{ Φ }} := by
  iintro H
  simp only [IProp.ext wp_unfold]
  simp only [wp.pre, h]
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ Hσ with %Hirr
  replace ⟨_, Hirr⟩ := Hirr
  imodintro
  isplit
  · ipure_intro; simp [Stuckness.MaybeReducible]
  iintro %e₂ %σ₂ %eₜ %Hstep
  nomatch Hirr obs e₂ σ₂ eₜ Hstep

/-! ## Derived lifting lemmas -/


@[rocq_alias wp_lift_step]
theorem wp_lift_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={∅,E}=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        WP e₂ @ s; E {{ Φ }} ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ %_ %_ %_ %_ %_ Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcred !> !>
  iapply H $$ %_ %_ %_ %Hstep Hcred

@[rocq_alias wp_lift_pure_step_no_fork]
theorem wp_lift_pure_step_no_fork [Inhabited State] (E₂ : CoPset) :
    -- (∀ σ₁, if s matches .NotStuck then PrimStep.Reducible (e₁,σ₁) else toVal e₁ = none) →
    (∀ σ₁, match s with | .NotStuck => PrimStep.Reducible (e₁,σ₁) | _ => toVal e₁ = none) →
    (∀ obs σ₁ e₂ σ₂ eₜ, (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) → obs = [] ∧ σ₂ = σ₁ ∧ eₜ = []) →
    (|={E₁}[E₂]▷=> ∀ obs e₂ eₜ σ, ⌜(e₁, σ) -<obs>-> (e₂, σ, eₜ)⌝ -∗ £ 1 -∗ WP e₂ @ s; E₁ {{ Φ }})
    ⊢ WP e₁ @ s; E₁ {{ Φ }} := by
  iintro %Hsafe %Hpure H
  iapply wp_lift_step
  { grind only [Language.toVal_none_of_reducible, Hsafe default] }
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  { ipure_intro; cases s <;> grind only} -- TODO: Why is `grind [cases S]` not enough?
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨rfl, rfl, rfl⟩ := Hpure _ _ _ _ _ Hstep
  dsimp only [List.nil_append, List.length_nil]
  imod ι.stateInterp_mono $$ Hσ with $
  imod Hclose
  imod H
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  ispecialize H $$ %_ %_ %_ %_ %Hstep Hcred
  iframe

@[rocq_alias wp_lift_pure_stuck]
theorem wp_lift_pure_stuck [Inhabited State] :
    (∀ σ, PrimStep.Stuck (e,σ)) →
    True ⊢ WP e @ E ?{{ Φ }} := by
  iintro %Hstuck -
  have ⟨toVal_e, _⟩ := Hstuck default
  iapply wp_lift_stuck toVal_e
  iintro %σ %ns %obs' %nt -
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  ipure_intro
  apply Hstuck

theorem wp_lift_atomic_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E1}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E1}[E2]▷=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (toVal e₂).rec iprop(False) Φ ∗
        -- NOTE: I tried something like this
        -- (∃ v, ⌜(toVal e₂) = some v⌝ ∧  Φ v) ∗
        -- which seems to work better for the proof. However, I
        -- don't fully understand why `Option.rec` was used
        -- instead, so I haven't made the change.
        -- Why is `Option.rec` (or `from_option` in Iris) used
        -- in the first place.
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E1 {{ Φ }} := by
  iintro H
  iapply wp_lift_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ Hσ₁ with ⟨$, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose %e₂ %σ₂ %eₜ %Hstep Hcred
  imod Hclose
  imod H $$ %_ %_ %_ %Hstep Hcred with H
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose !>
  imod Hclose
  imod H with ⟨$, HQ, $⟩
  -- imod H with ⟨$, ⟨%v, %h, HQ⟩, $⟩
  -- iapply wp_value ⟨ToVal.coe_of_toVal_eq_some h⟩ $$ HQ
  match h : toVal e₂ with
  | some v =>
    iintro !>
    iapply wp_value ⟨ToVal.coe_of_toVal_eq_some h⟩ $$ HQ
  | none =>
    iexfalso; iassumption


theorem wp_lift_atomic_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E}=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length ) ∗
        (toVal e₂).rec iprop(False) Φ  ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ [$] with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcred !> !>
  iapply H $$ %_ %_ %_ %Hstep Hcred

theorem wp_lift_pure_det_step_no_fork [Inhabited State] (E₂ : CoPset) :
    -- TODO: Why not have this `∀` only in the left match branch?
    (∀ σ₁, match s with | .NotStuck => PrimStep.Reducible (e₁,σ₁) | _ => toVal e₁ = none) →
    (∀ σ₁ obs e₂' σ₂ eₜ', (e₁, σ₁) -<obs>-> (e₂', σ₂, eₜ') →
      obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = []) →
    (|={E}[E₂]▷=> £ 1 -∗ WP e₂ @ s; E {{ Φ }}) ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro %Hsafe %Hpuredet H
  iapply wp_lift_pure_step_no_fork E₂ Hsafe (by grind only)
  iapply step_fupd_wand $$ H
  iintro H
  iintro %obs %e' %eₜ' %σ %aux
  obtain ⟨rfl, _, rfl, rfl⟩:= Hpuredet _ _ _ _ _ aux
  iassumption

theorem wp_pure_step_fupd [Inhabited State] (E₂ : CoPset):
    Language.PureExec φ n e₁ e₂ → φ → (|={E}[E₂]▷=>^[n] £ n -∗ WP e₂ @ s; E {{ Φ }}) ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro %Hexec %Hφ Hwp
  replace Hexec := Hexec.pureExec Hφ
  induction Hexec using Relation.Iterate.head_induction_on with
  | rfl =>
    simp only [Nat.repeat]
    rw (occs := [2]) [IProp.ext fupd_wp_iff]
    icases lc_zero with >Hz
    iapply Hwp $$ Hz
  | @head n e₁ e₃ _ _ IH =>
    obtain ⟨Hsafe, Hdet⟩ := ‹e₁ -ᵖ-> e₃›
    iapply wp_lift_pure_det_step_no_fork E₂ (e₂ := e₃) (by
        intro σ
        have : PrimStep.Reducible (e₁, σ) := by grind only [Language.reducible_of_reducibleNoObs]
        grind [cases Stuckness]
      ) (by grind)
    simp only [Nat.repeat]
    iapply step_fupd_wand $$ Hwp
    iintro Hwp Hone
    iapply IH
    iapply step_fupdN_wand $$ Hwp
    iintro Hwp Hc
    iapply Hwp $$ [Hone Hc]
    iapply lc_split
    iframe

theorem wp_pure_step_later [Inhabited State] :
    Language.PureExec φ n e₁ e₂ → φ → ▷^[n] (£ n -∗ WP e₂ @ s; E {{ Φ }}) ⊢ WP e₁ @ s; E {{ Φ }} := by
  intro Hexec Hφ
  refine .trans ?_  (wp_pure_step_fupd E Hexec Hφ)
  suffices Hwp : ∀ (P : IProp GF), ▷^[n] P ⊢ |={E}▷=>^[n] P by iapply Hwp
  intro P
  clear Hexec -- So it is not captured by the `induction`
  induction n with
  | zero => exact .rfl
  | succ n IH =>
    simp only [Nat.repeat]
    rw [IProp.ext <| later_laterN n]
    refine (later_mono IH).trans  ?_
    apply step_fupd_intro (Std.LawfulSet.subset_refl)
