/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.Instances.Lib.FUpd
public import Iris.BI
public import Iris.BI.WeakestPre
public import Iris.BI.DerivedLaws
public import Iris.ProofMode
public import Iris.ProgramLogic.Language
public import Iris.Std.CoPset

namespace Iris

open ProgramLogic Language.Notation Std Iris.BI

@[expose] public section

/-!
TODO: AddModal, ElimAcc instances
-/

/-- Carrier typeclass for the `stateInterp` operation.

This operation cannot be placed directly inside of `IrisGS_gen`
because Lean then wouldn't be able to derive from its arguments
the values of `Expr` and `Val`, and so they're asked explicitly.
This was not a problem in Iris Rocq becuse of canonical structures.
In Iris Lean, we instead fix our choice of `State` from the choice
of `Expr`, so `Expr` cannot be inferred from `State` instead.
-/
class StateInterp (State : Type _) (Obs : outParam $ Type _) (GF : BundledGFunctors)
  where
    /-- Interpretation of a state in a language model. Takes a state,
    number of steps, list of observations prior to the state, and number of
    threads previously spawned. -/
    stateInterp : State → Nat → List Obs → Nat → IProp GF

export StateInterp (stateInterp)

@[rocq_alias irisGS_gen]
class IrisGS_gen (hlc : outParam HasLC) (Expr : Type _) {Val : Type _} {State : Type _}
    {Obs : Type _} [Λ : Language Expr State Obs Val] (GF : BundledGFunctors) extends
    StateInterp State Obs GF, InvGS_gen hlc GF where
  /-- Number of later credits obtained from taking one step in the
  operational semantics of our language. -/
  numLatersPerStep : Nat → Nat
  -- TODO: Even when referenced with the typeclass instance, the
  -- display of `numLatersPerStep` is still kinda awful.
  /-- Postcondition of forked threads -/
  forkPost : Val → IProp GF
  /-- The number of steps in the state interpretation should only be
  considered a lower bound. -/
  stateInterp_mono σ ns obs nt :
    iprop(stateInterp σ ns obs nt ⊢ |={∅}=> stateInterp σ (ns + 1) obs nt)

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

/-- Reducibility condition depending on stuckness. -/
abbrev Stuckness.MaybeReducible : Stuckness → Expr × State → Prop
| .NotStuck, (e₁, σ₁) => PrimStep.Reducible (e₁, σ₁)
| _, _ => True

@[rocq_alias wp_pre]
def wp.pre (s : Stuckness) (wp : CoPset -> Expr -> (Val -> IProp GF) -> IProp GF) (E : CoPset)
    (e₁ : Expr) (Φ : Val -> IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(∀ (σ₁ : State) (ns : Nat) (obs obs' : List Obs) (nt : Nat),
    stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
    ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
    ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗
      £ (ι.numLatersPerStep ns + 1) ={∅}▷=∗^[ι.numLatersPerStep ns + 1] |={∅,E}=>
      stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
      wp E e₂ Φ ∗ [∗list] e' ∈ eₜ, wp ⊤ e' ι.forkPost)

@[rocq_alias wp_pre_contractive]
instance wp.pre.contractive s : OFE.Contractive (wp.pre s (ι := ι)) where
  distLater_dist := by
    intros n wp wp' Hwp E e₁ Φ
    unfold pre
    cases toVal e₁
    case some _ =>
      exact .rfl
    case none =>
      refine BI.forall_ne (fun σ₁ => ?_)
      refine BI.forall_ne (fun ns => ?_)
      refine BI.forall_ne (fun obs => ?_)
      refine BI.forall_ne (fun obs' => ?_)
      refine BI.forall_ne (fun nt => ?_)
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.forall_ne (fun e₂  => ?_)
      refine BI.forall_ne (fun σ₂ => ?_)
      refine BI.forall_ne (fun eₜ => ?_)
      refine BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine OFE.Contractive.distLater_dist fun m m_n => ?_
      refine BIFUpdate.ne.ne ?_
      refine step_fupdN_ne.ne ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.sep_ne.ne ?_ ?_
      · exact Hwp m m_n _ _ _
      · exact BI.BigSepL.bigSepL_dist <| fun _ => Hwp m m_n _ _ _

@[rocq_alias wp_def]
instance wp.def : Wp (IProp GF) (Expr) (Val) Stuckness where
  wp s := fixpoint (wp.pre s)

#rocq_ignore wp_aux "We do not use Iris' custom seal/unseal visibility control"
#rocq_ignore wp' "We do not use Iris' custom seal/unseal visibility control"
#rocq_ignore wp_unseal "We do not use Iris' custom seal/unseal visibility control"

section Wp

@[rocq_alias wp_unfold]
theorem wp_unfold {s E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊣⊢ wp.pre s (Wp.wp (PROP := IProp GF) s) E e Φ :=
  BI.equiv_iff.1 <| fun n => fixpoint_unfold (f := (wp.pre s).toContractiveHom) n E e Φ

@[rocq_alias wp_ne]
instance wp_ne {s : Stuckness} {E} {e : Expr} :
    OFE.NonExpansive (Wp.wp (PROP := IProp GF) s E e) where
  ne {n Φ₁ Φ₂} HΦ := by
    induction n using Nat.strongRecOn generalizing e E Φ₁ Φ₂ with | ind n IH =>
    simp only [wp_unfold.to_eq]
    dsimp only [wp.pre]
    cases toVal e
    case some v =>
      exact BIFUpdate.ne.ne <| HΦ v
    case none =>
      refine BI.forall_ne fun σ₁ => ?_
      refine BI.forall_ne fun ns => ?_
      refine BI.forall_ne fun obs => ?_
      refine BI.forall_ne fun obs' => ?_
      refine BI.forall_ne fun nt => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.forall_ne fun e₂  => ?_
      refine BI.forall_ne fun σ₂ => ?_
      refine BI.forall_ne fun eₜ => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl ?_
      refine step_fupdN_contractive.distLater_dist fun m n_m => ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.sep_ne.ne ?_ .rfl
      exact IH m n_m <| OFE.dist_lt HΦ n_m

#rocq_ignore wp_proper "Derivable using NonExpansive.eqv"

@[rocq_alias wp_contractive]
theorem wp_contractive (s : Stuckness) E (e : Expr) (h : toVal e = none) :
    OFE.Contractive (Wp.wp (PROP := IProp GF) s E e) where
  distLater_dist {n Φ₁ Φ₂} HΦ := by
    simp only [wp_unfold.to_eq]
    simp only [wp.pre, h]
    refine BI.forall_ne fun σ₁ => ?_
    refine BI.forall_ne fun ns => ?_
    refine BI.forall_ne fun obs => ?_
    refine BI.forall_ne fun obs' => ?_
    refine BI.forall_ne fun nt => ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.forall_ne fun e₂  => ?_
    refine BI.forall_ne fun σ₂ => ?_
    refine BI.forall_ne fun eₜ => ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl ?_
    refine step_fupdN_contractive.distLater_dist fun m n_m => ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.sep_ne.ne ?_ .rfl
    refine wp_ne.ne ?_
    exact HΦ m n_m

@[rocq_alias wp_value_fupd']
theorem wp_value_fupd' {s : Stuckness} {E} {Φ : Val → IProp GF} {v : Val} :
    WP (v : Expr) @ s ; E {{ Φ }} ⊣⊢ |={E}=> Φ v := by
  simp [wp_unfold.to_eq, toVal_coe, BI.BIBase.BiEntails.rfl, wp.pre]

@[rocq_alias wp_strong_mono]
theorem wp_strong_mono {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr} {Φ Ψ : Val → IProp GF}
    (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ WP e @ s₁ ; E₁ {{ Φ }} -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ {{ Ψ }} := by
  iloeb as IH generalizing %e %Φ %Ψ %E₁ %E₂ %hE
  rw [wp_unfold.to_eq, wp_unfold.to_eq]
  iintro H HΦ
  dsimp only [wp.pre]
  match toVal e with
  | none =>
    dsimp only
    iintro %σ₁ %ns %obs %obs' %nt Hσ
    imod fupd_mask_subseteq hE with Hclose
    icases H $$ Hσ with >⟨%h, H⟩
    imodintro
    isplit
    · simp only [LE.le] at hs
      ipureintro
      grind [cases Stuckness]
    · iintro %e₂ %σ₂ %eₜ #hstep hc
      dsimp only [Nat.repeat]
      imod H $$ hstep hc with H
      iintro !> !>; imod H; iintro !>
      iapply step_fupdN_wand $$ H
      iintro >⟨aux, H, Hefs⟩
      imod Hclose
      imodintro
      iframe aux
      isplitr [Hefs]
      · iapply IH $$ %e₂ %Φ %Ψ %E₁ %E₂ %hE H HΦ
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %e' %_ H
        iapply IH $$ %e' %_ %_ %⊤ %_ %LawfulSet.subset_refl H
        iintro %v H
        imodintro
        iassumption
  | some v =>
    dsimp only
    imod fupd_mask_mono hE $$ H with h
    iapply HΦ $$ h

@[rocq_alias fupd_wp]
theorem fupd_wp {s : Stuckness}{E}{e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> WP e @ s ; E {{ Φ }}) ⊢ WP e @ s ; E {{ Φ }} := by
  simp only [wp_unfold.to_eq]
  iintro H
  match h: toVal e with
  | some v =>
    simp only [wp.pre, h]
    imod H
    iassumption
  | none =>
    simp only [wp.pre, h]
    iintro %σ₁ %ns %obs %obs' %nt
    imod H with H
    iassumption

theorem fupd_wp_iff {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊣⊢ (|={E}=> WP e @ s ; E {{ Φ }}) :=
  ⟨fupd_mask_intro_discard LawfulSet.subset_refl, fupd_wp⟩

-- FIXME: Implicits

@[rocq_alias wp_fupd]
theorem wp_fupd {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E {{v, |={E}=> Φ v }} ⊢ WP e @ s ; E {{ Φ }} := by
  iintro h
  iapply wp_strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ h
  iintro %v h
  iassumption

@[rocq_alias wp_atomic]
theorem wp_atomic {s : Stuckness} {E1 E2 : CoPset} {e : Expr} {Φ : Val → IProp GF}
  [ι : Language.Atomic ↑s e] :
    (|={E1,E2}=> WP e @ s ;  E2 {{v, |={E2,E1}=> Φ v }}) ⊢ (WP e @ s ; E1 {{ Φ }}) := by
  simp only [wp_unfold.to_eq]
  iintro H
  match He : toVal e with
  | some v =>
    simp only [wp.pre, He]
    iapply BIFUpdate.trans (E2 := E2)
    imod H
    iassumption
  | none =>
    simp only [wp.pre, He]
    iintro %σ₁ %ns %obs %obs' %nt Hσ
    imod H
    imod H $$ Hσ with ⟨$, H⟩
    imodintro
    iintro %e2 %σ2 %efs %Hstep Hcred
    ihave aux := H $$ %e2 %σ2 %efs %Hstep Hcred
    iapply step_fupdN_wand $$ aux
    iintro >(⟨Hσ,H,Hefs⟩)
    irevert %ι
    match s with
    | .NotStuck =>
      simp only [wp_unfold.to_eq]
      dsimp only [wp.pre]
      match h₂ : toVal e2 with
      | some v2 =>
        iintro %ι
        icases H with > > $
        iframe
      | none =>
        iintro %ι
        icases H $$ %σ2 %(ns +1) %([]) %_ %(nt + efs.length) [Hσ] with >⟨%h, _⟩
        · exact .rfl
        exact ((Language.not_reducible_iff_irreducible.mpr (ι.atomic Hstep)) h).elim
    | .MaybeStuck =>
      iintro %ι
      have ⟨v, h⟩ := Option.isSome_iff_exists.mp (ι.atomic Hstep)
      obtain ⟨rfl⟩ := (ToVal.coe_of_toVal_eq_some h)
      simp only [wp_value_fupd'.to_eq]
      imod H with > H
      iframe

@[rocq_alias wp_credit_access]
theorem wp_credit_access {s : Stuckness} {E : CoPset} {e : Expr} {Φ} {P: IProp GF} (h : toVal e = none)
    (Htri : ∀ m k, ι.numLatersPerStep m + ι.numLatersPerStep k ≤ ι.numLatersPerStep (m + k)) :
    (∀ (σ₁ : State) ns obs nt,
      stateInterp σ₁ ns obs nt ={E}=∗
      ∃ k m, stateInterp σ₁ m obs nt ∗ ⌜ns = m + k⌝ ∗ (
        ∀ nt (σ₂: State) obs, £ (ι.numLatersPerStep k) -∗ stateInterp σ₂ (m+1) obs nt ={E}=∗
          stateInterp σ₂ (ns+1) obs nt ∗ P)) ⊢
    WP e @ s ; E {{ v, P ={E}=∗ Φ v }} -∗
    WP e @ s ; E {{ Φ }} := by
  simp only [wp_unfold.to_eq]
  iintro Hupd Hwp
  simp only [wp.pre, h]
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod Hupd $$ Hσ₁ with ⟨%k, %m, Hσ₁, %h, Hpost⟩; subst h
  imod Hwp $$ Hσ₁ with ⟨$,Hwp⟩
  imodintro
  iintro %e₂ %σ₂ %efs %Hstep Hc
  simp only [lc_split.to_eq]
  icases Hc with ⟨Hc,Hone⟩
  ihave Hc := lc_weaken _ (Htri m k) $$ Hc
  icases lc_split $$ Hc with ⟨Hm, Hk⟩
  icombine Hm Hone as Hm
  dsimp only [Nat.repeat]
  ihave Hwp := Hwp $$ [//] [Hm]
  · simp [lc_split.to_eq]; itrivial
  iapply step_fupd_wand $$ Hwp; iintro Hwp
  iapply step_fupdN_le (n := ι.numLatersPerStep m) (by grind only) LawfulSet.subset_refl
  iapply step_fupdN_wand $$ Hwp; iintro >⟨SI, Hwp, $⟩
  icases Hpost $$ Hk SI with >⟨$, HP⟩
  imodintro
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) (LawfulSet.subset_refl) $$ Hwp
  iintro %v HΦ
  iapply HΦ $$ HP

@[rocq_alias wp_step_fupdN_strong]
theorem wp_step_fupdN_strong {s : Stuckness} {E1 E2 : CoPset} {e : Expr} {P : IProp GF} {Φ} {n}
    (toVal_e : toVal e = none)  (E2_E1 : E2 ⊆ E1) :
    (∀ (σ : State) ns obs nt, stateInterp σ ns obs nt ={E1, ∅}=∗ ⌜n ≤ ι.numLatersPerStep ns + 1⌝)
    ∧ ((|={E1,E2}=> |={∅}▷=>^[n] |={E2,E1}=> P)
    ∗ WP e @ s ; E2 {{ v, P ={E1}=∗ Φ v}}) ⊢
    WP e @ s ; E1 {{ Φ }} := by
  match n with
  | 0 =>
    iintro ⟨-, ⟨Hp, Hwp⟩⟩
    iapply wp_strong_mono (Std.IsPreorder.le_refl s) E2_E1 $$ Hwp
    iintro %v H
    dsimp only [Nat.repeat]
    imod Hp
    imod Hp
    iapply H $$ Hp
  | n+1 =>
    simp only [wp_unfold.to_eq]
    simp only [wp.pre, toVal_e]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ₁
    by_cases Hn : n ≤ ι.numLatersPerStep ns
    · icases H with ⟨-, ⟨Hp, Hwp⟩⟩
      imod Hp
      dsimp only [Nat.repeat]
      imod Hwp $$ Hσ₁ with ⟨$, H⟩
      iintro !> %e₂ %σ₂ %efs %Hstep Hcred
      icases H $$ %_ %_ %_ %Hstep Hcred with H
      imod H; imod Hp
      iintro !> !>
      imod H; imod Hp
      imodintro
      generalize ι.numLatersPerStep ns = n0 at *
      induction n generalizing n0 with
      | zero =>
        iapply step_fupdN_wand $$ H
        iintro >⟨$, Hwp, $⟩
        dsimp only [Nat.repeat]
        imod Hp
        imodintro
        iapply wp_strong_mono (Std.IsPreorder.le_refl s) E2_E1 $$ Hwp
        iintro %v HΦ
        iapply HΦ $$ Hp
      | succ n IH =>
        obtain ⟨n0, rfl⟩ : ∃ n0', n0 = n0' + 1 := by cases n0 <;> grind
        dsimp only [Nat.repeat]
        imod Hp; imod H; imodintro; imodintro; imod Hp; imod H; imodintro
        -- TODO: remove this once we have iinduction
        unfold ProofMode.Entails' at IH
        iapply IH n0 (Nat.le_of_succ_le_succ Hn) $$ [$]
    · icases H with ⟨interp, -⟩
      imod interp $$ Hσ₁ with %h
      grind only


theorem wp_bind_iff (K : Expr → Expr) [κ : Language.Context K] {s : Stuckness} {E : CoPset} {e : Expr}
    {Φ : Val → IProp GF} :
    -- TODO: Have `WP` use the correct `Val` type from the `Wp` instance (it should anyways, it's an outParam, no?)
    WP e @ s ; E {{v, WP (K (↑v : Val)) @ s ; E {{ Φ }} }} ⊣⊢ WP (K e) @ s ; E {{ Φ }} := by
  iloeb as IH generalizing %E %e %Φ
  rewrite (occs := [1]) [wp_unfold.to_eq]
  simp only [wp.pre]
  match h : toVal e with
  | some v =>
    dsimp only
    rw [ToVal.coe_of_toVal_eq_some h]
    isplit
    · iintro H; iapply fupd_wp $$ H
    · iintro $
  | none =>
    rw [wp_unfold.to_eq]
    dsimp only
    simp only [wp.pre, κ.toVal_eq_none_fill h, Nat.repeat]
    isplit <;>
    (iintro H %σ₁ %step %obs %obs' %n Hσ; imod H $$ [$] with ⟨%_, H⟩; imodintro; isplit)
    · ipureintro; grind only [cases Stuckness, Language.Context.reducible_fill]
    · iintro %e₂ %σ₂ %efs %HKstep Hcred
      obtain ⟨e₂', rfl, Hstep⟩ := κ.primStep_fill_inv h HKstep
      icases H $$ %e₂' %σ₂ %efs %Hstep Hcred with >H; imodintro; imodintro
      imod H; imodintro; iapply step_fupdN_wand $$ H; iintro H
      imod H with ⟨$, H, $⟩; imodintro; iapply IH $$ H
    · ipureintro; grind only [cases Stuckness, Language.Context.reducible_fill_inv]
    · iintro %e₂ %σ₂ %efs %Hstep Hcred
      icases H $$ %(K e₂) %σ₂ %efs %(κ.primStep_fill Hstep) Hcred with >H; imodintro; imodintro
      imod H; imodintro; iapply step_fupdN_wand $$ H; iintro H
      imod H with ⟨$, H, $⟩; imodintro; iapply IH $$ H

@[rocq_alias wp_bind]
theorem wp_bind (K : Expr → Expr) [κ : Language.Context K] {s : Stuckness} {E : CoPset} {e : Expr}
    {Φ : Val → IProp GF} :
    WP e @ s ; E {{v, WP (K (↑v : Val)) @ s ; E {{ Φ }} }} ⊢ WP (K e) @ s ; E {{ Φ }} := (wp_bind_iff K).1

@[rocq_alias wp_bind_inv]
theorem wp_bind_inv (K : Expr → Expr) [κ : Language.Context K] {s : Stuckness} {E : CoPset} {e : Expr}
    {Φ : Val → IProp GF} :
   WP (K e) @ s ; E {{ Φ }} ⊢ WP e @ s ; E {{v, WP (K (↑v : Val)) @ s ; E {{ Φ }} }}  := (wp_bind_iff K).2

/-! ## Derived rules -/

@[rocq_alias wp_mono]
theorem wp_mono {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    (∀ v, Φ v ⊢ Ψ v) → WP e @ s ; E {{ Φ }} ⊢ WP e @ s ; E {{ Ψ }} := by
  iintro %HΦ H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) (LawfulSet.subset_refl) $$ H
  iintro %v HΨ !>
  iapply HΦ $$ HΨ

@[rocq_alias wp_stuck_mono]
theorem wp_stuck_mono {s₁ s₂ : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    s₁ ≤ s₂ → WP e @ s₁; E {{ Φ }} ⊢ WP e @ s₂ ; E {{ Φ }} := by
  iintro %s₁s₂ Hwp
  iapply wp_strong_mono s₁s₂ (LawfulSet.subset_refl) $$ Hwp
  iintro %v HΦ
  iframe HΦ

@[rocq_alias wp_stuck_weaken]
theorem wp_stuck_weaken {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }} :=
  wp_stuck_mono (Stuckness.le_MaybeStuck)

@[rocq_alias wp_mask_mono]
theorem wp_mask_mono {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF}
    (E₁_E₂ : E₁ ⊆ E₂) : WP e @ s; E₁ {{ Φ }} ⊢ WP e @ s; E₂ {{ Φ }} := by
  iintro Hwp
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) E₁_E₂ $$ Hwp
  iintro %v HΦ
  iframe HΦ

#rocq_ignore wp_mono' "No `Proper` typeclass in Lean"
#rocq_ignore wp_flip_mono' "No `Proper` typeclass in Lean"

@[rocq_alias wp_value_fupd]
theorem wp_value_fupd {s : Stuckness} {E : CoPset} {e : Expr} {v : Val} {Φ : Val → IProp GF} :
    Language.IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v
  | ⟨h⟩ => h ▸ wp_value_fupd'

@[rocq_alias wp_value']
theorem wp_value' {s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    Φ v ⊢ WP (v : Expr) @ s; E {{ Φ }} :=
  fupd_intro.trans wp_value_fupd'.2

@[rocq_alias wp_value]
theorem wp_value {s : Stuckness} {E : CoPset} {e : Expr} {v : Val} {Φ : Val → IProp GF} :
    Language.IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}
  | ⟨h⟩ => h ▸ wp_value'

@[simp]
theorem wp_value_iff {s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    WP (v : Expr) @ s; E {{ Φ }} = iprop(|={E}=> Φ v) := by
  simp [wp_unfold.to_eq, wp.pre]

@[rocq_alias wp_frame_l]
theorem wp_frame_l {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }} := by
  iintro ⟨_, H⟩
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) (LawfulSet.subset_refl) $$ H
  iframe
  iintro %x
  iapply fupd_intro

@[rocq_alias wp_frame_r]
theorem wp_frame_r {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, R ∗ Φ v }} :=
  BI.sep_comm.1.trans wp_frame_l

@[rocq_alias wp_step_fupdN]
theorem wp_step_fupdN {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {P : IProp GF} {Φ : Val → IProp GF} {n : Nat}
    (toVal_e : toVal e = none) (E₂E₁ : E₂ ⊆ E₁) :
    (∀ (σ : State) ns obs nt, stateInterp σ ns obs nt ={E₁,∅}=∗ ⌜n ≤ (ι.numLatersPerStep ns)+1⌝) ∧
    (((|={E₁\E₂,∅}=> |={∅}▷=>^[n] |={∅,E₁\E₂}=> P) ∗
    WP e @ s; E₂ {{ v, P ={E₁}=∗ Φ v }})) -∗
    WP e @ s; E₁ {{ Φ }} := by
  iintro H
  iapply wp_step_fupdN_strong (s := s) (P := P) (n := n) toVal_e E₂E₁ $$ [H]
  iapply BI.and_mono_right $$ H
  iintro ⟨HP, $⟩
  imod fupd_mask_subseteq_emptyset_difference (show E₁\ E₂ ⊆ E₁ from LawfulSet.diff_subset_left) with G
  imod HP
  imod G with -
  rw [show E₁ \ (E₁ \ E₂) = E₂ from LawfulSet.diff_self_diff_of_subset E₂E₁]
  imodintro
  iapply step_fupdN_wand $$ HP; iintro H
  iapply fupd_mask_frame LawfulSet.empty_subset
  imod H
  imodintro
  simp [LawfulSet.diff_empty, ←LawfulSet.diff_subset_decomp E₂E₁]
  itrivial

@[rocq_alias wp_step_fupd]
theorem wp_step_fupd {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {P : IProp GF} {Φ : Val → IProp GF}
    (toVal_e : toVal e = none) (E₂E₁ : E₂ ⊆ E₁) :
    (|={E₁}[E₂]▷=> P) -∗ WP e @ s; E₂ {{ v, P ={E₁}=∗ Φ v }} -∗ WP e @ s; E₁ {{ Φ }} := by
  iintro HR H
  iapply wp_step_fupdN_strong (n := 1) (P := P) toVal_e E₂E₁ $$ [-]
  iframe H
  isplit
  · iintro %σ %ns %obj %nt interp
    iapply fupd_mask_intro_discard LawfulSet.empty_subset $$ [HR]
    itrivial
  · imod HR
    dsimp only [Nat.repeat]
    iframe

@[rocq_alias wp_frame_step_l]
theorem wp_frame_step_l {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF}
    (toVal_e : toVal e = none) (E₂E₁ : E₂ ⊆ E₁) :
    (|={E₁}[E₂]▷=> R) ∗ WP e @ s; E₂ {{ Φ }} ⊢ WP e @ s; E₁ {{ v, R ∗ Φ v }} := by
  iintro ⟨Hu, Hwp⟩
  iapply wp_step_fupd toVal_e E₂E₁ $$ Hu
  iapply wp_mono $$ Hwp
  iintro %x $ $

@[rocq_alias wp_frame_step_r]
theorem wp_frame_step_r {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF}
    (h1 : toVal e = none) (h2 : E₂ ⊆ E₁) :
    WP e @ s; E₂ {{ Φ }} ∗ (|={E₁}[E₂]▷=> R) ⊢ WP e @ s; E₁ {{ v, Φ v ∗ R }} :=
  (BI.sep_comm.1.trans <| wp_frame_step_l h1 h2 |>.trans <| wp_mono (fun _ => BI.sep_comm.1))

@[rocq_alias wp_frame_step_l']
theorem wp_frame_step_l' {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}{Φ : Val → IProp GF} {R : IProp GF}
    (toVal_e : toVal e = none) (E₂E₁ : E₂ ⊆ E₁) :
    (▷ R) ∗ WP e @ s; E₂ {{ Φ }} ⊢ WP e @ s; E₁ {{ v, R ∗ Φ v }} := by
  iintro ⟨Hu, Hwp⟩
  iapply wp_frame_step_l toVal_e E₂E₁
  iframe
  iapply fupd_mask_intro E₂E₁
  iintro H
  imodintro
  imod H
  imodintro
  iapply BI.true_intro $$ H

@[rocq_alias wp_frame_step_r']
theorem wp_frame_step_r' {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF}
  (h1 : toVal e = none) (h2 : E₂ ⊆ E₁) : WP e @ s; E₂ {{ Φ }} ∗ (▷ R) ⊢ WP e @ s; E₁ {{ v, Φ v ∗ R }} :=
  (BI.sep_comm.1.trans <| wp_frame_step_l' h1 h2 |>.trans <| wp_mono (fun _ => BI.sep_comm.1))

@[rocq_alias wp_wand]
theorem wp_wand {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} := by
  iintro Hwp H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ Hwp
  iintro %v HΦ
  icases H $$ HΦ with H
  imodintro; iframe

@[rocq_alias wp_wand_l]
theorem wp_wand_l {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s ; E {{ Φ }} ⊢ WP e @ s ; E {{ Ψ }} :=
  BI.wand_elim_swap wp_wand

@[rocq_alias wp_wand_r]
theorem wp_wand_r {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s ; E {{ Ψ }} :=
  BI.wand_elim wp_wand

@[rocq_alias wp_frame_wand]
theorem wp_frame_wand {s : Stuckness} {E : CoPset} {e : Expr} {Φ :Val → IProp GF} {R : IProp GF} :
    R ⊢ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }} := by
  iintro R Hwp
  iapply wp_wand $$ Hwp
  iintro %v H
  iapply H $$ R

end Wp

section ProofModeClasses

open ProofMode

variable {hlc : outParam HasLC}
variable {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

variable {s : Stuckness} {E : CoPset} {e : Expr} {v : Val} {Φ Ψ : Val → IProp GF} {P Q R : IProp GF}

@[rocq_alias frame_wp]
instance frameWp {p : Bool} [H : ∀ v, Frame p R (Φ v) (Ψ v)] :
    -- TODO: move FrameInstantiateExistDisabled over the `FrameInstantiateExistDisabled` constant
    -- Blocked by #390
    -- see: https://github.com/leanprover-community/iris-lean/pull/393
    Frame p R (WP e @ s ; E {{ Φ }}) (WP e @ s ; E {{ Ψ }}) where
  frame := by
    refine wp_frame_l.trans ?_
    apply wp_mono
    exact fun v => frame

@[rocq_alias is_except_0_wp]
instance isExcept0Wp : IsExcept0 (WP e @ s ; E {{ Φ }}) where
  is_except0 :=
    calc iprop(◇ _)
      _ ⊢ ◇ |={E}=> _ := BI.except0_mono fupd_intro
      _ ⊢ |={E}=> _ := BIFUpdate.except0
      _ ⊢ WP e @ s ; E {{ Φ }} := fupd_wp

-- this should have higher priority than elimModalFupdWpAtomic
@[rocq_alias elim_modal_fupd_wp]
instance (priority := default + 10) elimModalFupdWp p :
    ElimModal True p io false iprop(|={E}=> P) P (WP e @ s ; E {{ Φ }}) (WP e @ s ; E {{ Φ }}) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply fupd_wp
    imod H; imodintro
    iapply G $$ H

@[rocq_alias elim_modal_bupd_wp]
instance elimModalBupdWp p :
    ElimModal True p io false iprop(|==> P) P (WP e @ s ; E {{ Φ }}) (WP e @ s ; E {{ Φ }}) where
  elim_modal := by
    rintro ⟨⟩
    refine BI.sep_mono (BI.intuitionisticallyIf_mono (BIUpdateFUpdate.fupd_of_bupd (E := E))) .rfl |>.trans ?_
    exact elimModalFupdWp _ |>.elim_modal ⟨⟩ (io := io)

/-- Error message instance for non-mask-changing view shifts.  Also uses a slightly
different error: we cannot apply `fupd_mask_subseteq` if `e` is not atomic, so
we tell the user to first add a leading `fupd` and then change the mask of that. -/
@[rocq_alias elim_modal_fupd_wp_wrong_mask]
instance elimModalFupdWp_wrongMask :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
    Use `iapply fupd_wp; imod (fupd_mask_subseteq E₂)` to adjust the mask of your goal to `E₂`")
    p io false iprop(|={E₂}=> P) iprop(False) (WP e @ s ; E₁ {{ Φ }}) iprop(False) where
  elim_modal := nofun

@[rocq_alias elim_modal_fupd_wp_atomic]
instance elimModalFupdWpAtomic :
    ElimModal (Language.Atomic ↑s e) p io false iprop(|={E₁,E₂}=> P) P (WP e @ s ; E₁ {{ Φ }}) (WP e @ s ; E₂ {{ v, |={E₂,E₁}=> Φ v}}) where
  elim_modal := by
    rintro atomic; iintro ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply wp_atomic
    imod H; imodintro
    iapply G $$ H

@[rocq_alias elim_modal_fupd_wp_atomic_wrong_mask]
instance elimModalFupdWpAtomic_wrongMask :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
    Use `iapply fupd_wp; imod (fupd_mask_subseteq E₂)` to adjust the mask of your goal to `E₂`")
    p io false iprop(|={E₁,E₂}=> P) iprop(False) (WP e @ s ; E₁ {{ Φ }}) iprop(False) where
  elim_modal := nofun

@[rocq_alias elim_acc_wp_atomic]
instance (priority := low) elimAcc_wp_atomic {X} (E₁ E₂ : CoPset) α β (γ : X → Option (IProp GF)) :
    ElimAcc (Language.Atomic ↑s e) (fupd E₁ E₂) (fupd E₂ E₁) α β γ
      (WP e @ s ; E₁ {{ Φ }})
      (fun x => WP e @ s ; E₂ {{ v, |={E₂}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %atomic Hinner >⟨%x, Hα, Hclose⟩
    iapply wp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

@[rocq_alias elim_acc_wp_nonatomic]
instance elimAcc_wp_nonatomic {X} E (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E E) (fupd E E) α β γ (WP e @ s ; E {{ Φ }})
    (fun x => WP e @ s ; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    iapply wp_fupd
    iapply wp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

end ProofModeClasses
