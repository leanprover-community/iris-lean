/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li, Sergei Stepanenko, Zongyuan Liu
-/
module

public import Iris.Algebra
public import Iris.BI
public import Iris.ProofMode
public import Iris.ProgramLogic.WeakestPre
public import Iris.Std.FromMathlib

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.BI Iris.Algebra Std FromMathlib LawfulSet
open Iris.ProgramLogic.PrimStep
open Language.Notation

@[expose] public section

variable {hlc : HasLC} {Expr State Obs Val : Type _}
variable [Language Expr State Obs Val]
variable {GF : BundledGFunctors} [iG : IrisGS_gen hlc Expr GF]

abbrev wptp (s : Stuckness) (es : List Expr) (Φs : List (Val → IProp GF)) : IProp GF :=
  iprop([∗list] e;Φ ∈ es;Φs, WP e @ s ; ⊤ {{ Φ }})

@[rocq_alias steps_sum]
def steps_sum (numLaters : Nat → Nat) : Nat → Nat → Nat
  | _,     0      => 0
  | start, n + 1  => numLaters start + 1 + steps_sum numLaters (start + 1) n

@[rocq_alias wp_step]
theorem wp_step (s : Stuckness) (e1 : Expr) (σ1 : State)
    (ns : Nat) (κ κs : List Obs) (e2 : Expr) (σ2 : State) (efs : List Expr) (nt : Nat)
    (Φ : Val → IProp GF)
    (Hstep : (e1, σ1) -<κ>-> (e2, σ2, efs)) :
    ⊢ stateInterp σ1 ns (κ ++ κs) nt -∗
      £ (iG.numLatersPerStep ns + 1) -∗
      WP e1 @ s ; ⊤ {{ Φ }}
        ={⊤,∅}=∗
        |={∅}▷=>^[iG.numLatersPerStep ns + 1] |={∅,⊤}=>
        stateInterp σ2 (ns + 1) κs (nt + efs.length) ∗
        WP e2 @ s ; ⊤ {{ Φ }} ∗
        wptp s efs (List.replicate efs.length iG.forkPost) := by
  rw [wp_unfold.to_eq]
  simp only [wp.pre, Language.val_stuck Hstep]
  iintro Hσ Hcred Hwp
  imod Hwp $$ %σ1 %ns %κ %κs %nt Hσ with ⟨%_, Hcont⟩
  imodintro
  ihave Hcont := Hcont $$ %e2 %σ2 %efs %Hstep Hcred
  iapply step_fupdN_wand $$ Hcont
  iintro >⟨HSI, Hwp2, Hefs⟩
  imodintro
  iframe HSI Hwp2
  iapply BigSepL2.bigSepL2_replicate_right.mpr
  iexact Hefs

@[rocq_alias wptp_step]
theorem wptp_step (s : Stuckness) (es1 es2 : List Expr)
    (κ κs : List Obs) (σ1 σ2 : State) (ns : Nat) (Φs : List (Val → IProp GF)) (nt : Nat)
    (Hstep : (es1, σ1) -<κ>->ₜₚ (es2, σ2)) :
    ⊢ stateInterp σ1 ns (κ ++ κs) nt -∗
      £ (iG.numLatersPerStep ns + 1) -∗
      wptp s es1 Φs -∗
      ∃ nt', |={⊤,∅}=> |={∅}▷=>^[iG.numLatersPerStep ns + 1] |={∅,⊤}=>
        stateInterp σ2 (ns + 1) κs (nt + nt') ∗
        wptp s es2 (Φs ++ List.replicate nt' iG.forkPost) := by
  cases Hstep with | @atomic e1' _ _ e2' _ efs H_prim t₁ t₂ =>
  iintro Hσ Hcred Hwptp
  iexists efs.length
  icases BigSepL2.bigSepL2_app_inv_left $$ Hwptp with ⟨%Φs1, %Φs2, %hΦs, Hwptp1, Hwptp2⟩
  icases BigSepL2.bigSepL2_cons_inv_left $$ Hwptp2 with ⟨%Φ_head, %Φs2', %hΦs2, Hwp_e1, Hwptp3⟩
  subst hΦs hΦs2
  imod wp_step (Hstep := H_prim) $$ Hσ Hcred Hwp_e1 with Hstep
  imodintro
  iapply step_fupdN_wand $$ Hstep
  iintro >⟨HSI, Hwp_e2, Hwptp_efs⟩
  imodintro
  iframe HSI
  icases BigSepL2.bigSepL2_length $$ Hwptp1 with %Hlen1
  icases BigSepL2.bigSepL2_length $$ Hwptp3 with %Hlen3
  simp only [List.append_assoc, List.cons_append]
  iapply BigSepL2.bigSepL2_append (.inl Hlen1); iframe Hwptp1
  iapply BigSepL2.bigSepL2_cons; iframe Hwp_e2
  iapply BigSepL2.bigSepL2_append (.inl Hlen3); iframe Hwptp3 Hwptp_efs

@[rocq_alias wp_not_stuck]
theorem wp_not_stuck (κs : List Obs) (nt : Nat) (e : Expr) (σ : State)
    (ns : Nat) (Φ : Val → IProp GF) :
    ⊢ stateInterp σ ns κs nt -∗
      WP e @ Stuckness.NotStuck ; ⊤ {{ Φ }} ={⊤,∅}=∗ ⌜NotStuck (e, σ)⌝ := by
  rw [wp_unfold.to_eq]
  unfold wp.pre
  match h : toVal e with
  | some v =>
    dsimp only
    iintro _ _
    iapply fupd_mask_intro_discard empty_subset
    ipure_intro
    exact .inl (by rw [h]; rfl)
  | none =>
    dsimp only
    iintro Hst Hcont
    ispecialize Hcont $$ %σ %ns %([]) %κs %nt
    rw [List.nil_append]
    imod Hcont $$ Hst with ⟨%H, _⟩
    imodintro
    ipure_intro
    exact .inr H

@[rocq_alias wptp_preservation]
theorem wptp_preservation (s : Stuckness) (n : Nat) (es1 es2 : List Expr)
    (κs κs' : List Obs) (σ1 σ2 : State) (ns : Nat)
    (Φs : List (Val → IProp GF)) (nt : Nat)
    (Hsteps : (es1, σ1) -<κs>->ₜₚ^[n] (es2, σ2)) :
    ⊢ stateInterp σ1 ns (κs ++ κs') nt -∗
      £ (steps_sum iG.numLatersPerStep ns n) -∗
      wptp s es1 Φs ={⊤,∅}=∗
      |={∅}▷=>^[steps_sum iG.numLatersPerStep ns n] |={∅,⊤}=> ∃ nt',
        stateInterp σ2 (n + ns) κs' (nt + nt') ∗
        wptp s es2 (Φs ++ List.replicate nt' iG.forkPost) := by
  generalize hρ1 : (es1, σ1) = ρ1 at Hsteps
  generalize hρ2 : (es2, σ2) = ρ2 at Hsteps
  induction Hsteps generalizing nt κs' Φs ns es1 σ1 es2 σ2 with
  | refl ρ =>
    cases hρ1; cases hρ2
    simp only [Nat.zero_add, List.nil_append, steps_sum, Nat.repeat]
    iintro Hσ _ Hwptp
    iapply fupd_mask_intro empty_subset
    iintro Hcl; imod Hcl; imodintro
    iexists 0
    simp only [List.replicate, List.append_nil]
    iframe Hσ
    iexact Hwptp
  | @cons n_inner ρ1' ρ_mid ρ2' obs obs' hstep hrest ih =>
    cases hρ1; cases hρ2
    cases ρ_mid with | mk e_mid σ_mid =>
    rw [List.append_assoc obs obs' κs']
    dsimp only [steps_sum]
    rw [Nat.repeat_add]
    iintro Hσ ⟨Hcred1, Hcred2⟩ Hwptp
    icases wptp_step s es1 e_mid obs (obs' ++ κs') σ1 σ_mid ns Φs nt hstep
            $$ Hσ Hcred1 Hwptp with ⟨%nt'_step, >Hwptp_step⟩
    imodintro
    iapply step_fupdN_S_fupd.2
    iapply step_fupdN_wand $$ Hwptp_step
    iintro >⟨HSI, Hwptp_mid⟩
    imod ih _ _ _ _ _ _ _ _ rfl rfl $$ HSI Hcred2 Hwptp_mid with Hih
    imodintro
    iapply step_fupdN_wand $$ Hih
    iintro >⟨%nt_inner', HSI', Hwptp'⟩
    iexists (nt'_step + nt_inner')
    rw [Nat.add_assoc, Nat.add_comm _ 1, ←Nat.add_assoc]
    rw [←List.replicate_append_replicate, List.append_assoc]
    iframe HSI' Hwptp'

@[rocq_alias wptp_postconditions]
theorem wptp_postconditions (Φs : List (Val → IProp GF)) (s : Stuckness) (es : List Expr):
    wptp s es Φs ={⊤}=∗ [∗list] e;Φ ∈ es;Φs, (toVal e).elim iprop(True) Φ := by
  iintro Ht
  iapply BigSepL2.bigSepL2_fupd
  iapply BigSepL2.bigSepL2_impl $$ Ht
  iintro !> %k %x1 %x2 %Hin %Hlen Hwp
  cases hv : toVal x1
  · imodintro; apply true_intro
  · simp only [Option.elim_some]
    iapply wp_value_fupd $$ Hwp
    constructor; grind

omit iG in
@[rocq_alias wp_strong_adequacy_gen]
theorem wp_strong_adequacy_gen [InvGpreS GF] (s : Stuckness) (es : List Expr) (σ1 : State)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (σ2 : State) (φ : Prop)
    (numLaters : Nat → Nat) (Hwp : ∀ [InvGS_gen hlc GF],
      ⊢ |={⊤}=>
        ∃ (stateI : State → Nat → List Obs → Nat → IProp GF)
          (Φs : List (Val → IProp GF)) (forkPost : Val → IProp GF)
          (mono : ∀ σ ns obs nt, stateI σ ns obs nt ⊢ |={∅}=> stateI σ (ns + 1) obs nt),
        let _ : IrisGS_gen hlc Expr GF := .mk (toStateInterp := ⟨stateI⟩) numLaters forkPost mono
        iprop(stateI σ1 0 κs 0 ∗
          ([∗list] e;Φ ∈ es;Φs, WP e @ s ; ⊤ {{ Φ }}) ∗
          (∀ (es' t2' : List Expr),
            ⌜t2 = es' ++ t2'⌝ -∗ ⌜es'.length = es.length⌝ -∗
            ⌜∀ e2, s = .NotStuck → e2 ∈ t2 → NotStuck (e2, σ2)⌝ -∗
            stateI σ2 n [] t2'.length -∗
            ([∗list] e;Φ ∈ es';Φs, (toVal e).elim iprop(True) Φ) -∗
            ([∗list] v ∈ List.filterMap toVal t2', forkPost v) -∗
            |={⊤,∅}=> ⌜φ⌝)))
    (Hsteps : (es, σ1) -<κs>->ₜₚ^[n] (t2, σ2)) :
    φ := by
  apply pure_soundness (PROP := IProp GF)
  apply laterN_soundness (n := steps_sum numLaters 0 n + 1)
  rw [(laterN_later _).to_eq]
  refine Entails.trans ?_ (laterN_mono _ except0_into_later)
  apply fupd_finally_soundness hlc (steps_sum numLaters 0 n) ⊤
  iintro %Hinv Hf
  imod Hwp with ⟨%stateI, %Φs, %forkPost, %mono, HSI_init, Hwptp_bsl, Hφ⟩
  ihave %hlen_es_Φs := BigSepL2.bigSepL2_length $$ Hwptp_bsl
  letI iG : IrisGS_gen hlc Expr GF := .mk (toStateInterp := ⟨stateI⟩) numLaters forkPost mono
  imod wptp_preservation (κs' := []) (Hsteps := Hsteps) $$ [HSI_init] Hf Hwptp_bsl with H
  · simp only [List.append_nil]; iframe
  rw [Nat.add_zero]
  iapply step_fupdN_fupd_finally
  iapply step_fupdN_wand $$ H
  iintro >⟨%nt', Hσ, Ht⟩
  iapply fupd_finally_keep _ iprop(⌜∀ e2, s = .NotStuck → e2 ∈ t2 → NotStuck (e2, σ2)⌝)
  isplit
  · iintro %e %Heq %Hin
    subst s
    obtain ⟨i, He⟩ := List.getElem?_of_mem Hin
    icases BigSepL2.bigSepL2_lookup_left $$ Ht with ⟨%Φ', _, He⟩; exact He
    imod wp_not_stuck $$ Hσ He with %_
    ipure_intro;trivial
  iintro %_
  imod wptp_postconditions $$ Ht with Ht
  icases BigSepL2.bigSepL2_app_inv_right $$ Ht with ⟨%es', %t2', %Heq, Hes', Ht2'⟩; subst Heq
  icases BigSepL2.bigSepL2_length $$ Hes' with %_
  icases BigSepL2.bigSepL2_length $$ Ht2' with %Hlen2
  rw [List.length_replicate] at Hlen2; subst Hlen2
  simp only [Nat.zero_add]
  icases BigSepL2.bigSepL2_replicate_right $$ Ht2' with Ht2'
  icases (equiv_iff.mp <| BigSepL.bigSepL_filterMap toVal).mpr $$ [Ht2'] with Ht2'
  · iapply BigSepL.bigSepL_mono $$ Ht2'
    intros; rcases (toVal _)
    simp only [Option.elim_none]
    ipure_intro; trivial
    simp only [Option.elim_some]
    exact .rfl
  imod Hφ $$ [] [] [] Hσ Hes' Ht2' with %_ <;> ipure_intro <;> grind

@[rocq_alias wp_strong_adequacy]
abbrev wp_strong_adequacy := @wp_strong_adequacy_gen .hasLC

@[rocq_alias adequate]
structure adequate (s : Stuckness) (e1 : Expr) (σ1 : State)
    (φ : Val → State → Prop) : Prop where
  adequate_result :
    ∀ (t2 : List Expr) (σ2 : State) (v2 : Val),
        ([e1], σ1) -·->ₜₚ* (ToVal.ofVal v2 :: t2, σ2) → φ v2 σ2
  adequate_not_stuck :
    ∀ (t2 : List Expr) (σ2 : State) (e2 : Expr),
      s = .NotStuck → ([e1], σ1) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → NotStuck (e2, σ2)

@[rocq_alias adequate_alt]
theorem adequate_alt (s : Stuckness) (e1 : Expr) (σ1 : State)
    (φ : Val → State → Prop) :
    adequate s e1 σ1 φ ↔
      ∀ (t2 : List Expr) (σ2 : State),
        ([e1], σ1) -·->ₜₚ* (t2, σ2) →
        (∀ (v2 : Val) (t2' : List Expr), t2 = ToVal.ofVal v2 :: t2' → φ v2 σ2) ∧
        (∀ (e2 : Expr), s = .NotStuck → e2 ∈ t2 → NotStuck (e2, σ2)) := by
  refine ⟨fun ⟨hres, hns⟩ t2 σ2 hreach => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · rintro v2 t2' ⟨⟩
    exact hres _ _ _ hreach
  · exact fun e2 hs hel => hns _ _ _ hs hreach hel
  · exact fun t2 σ2 v2 hreach => ((h _ _ hreach).1) v2 t2 rfl
  · exact fun t2 σ2 e2 hs hreach hel => ((h _ _ hreach).2) e2 hs hel

@[rocq_alias adequate_tp_safe]
theorem adequate_tp_safe (e1 : Expr) (t2 : List Expr) (σ1 σ2 : State)
    (φ : Val → State → Prop) (had : adequate .NotStuck e1 σ1 φ)
    (hsteps : ([e1], σ1) -·->ₜₚ* (t2, σ2)) :
    (∀ e ∈ t2, ∃ v, ToVal.toVal e = some v) ∨
      ∃ (t3 : List Expr) (σ3 : State), (t2, σ2) -·->ₜₚ (t3, σ3) := by
  by_cases hall : ∀ e ∈ t2, ∃ v, ToVal.toVal e = some v
  · exact .inl hall
  · simp [Classical.not_forall] at hall
    obtain ⟨e2, ⟨hel, hne⟩⟩ := hall
    have hns : NotStuck (e2, σ2) := had.adequate_not_stuck t2 σ2 e2 rfl hsteps hel
    rcases hns with hv | ⟨obs, e3, σ3, efs, hstep⟩
    · exfalso; rcases hv2 : ToVal.toVal e2 with _ | v <;> grind
    obtain ⟨t2', t2'', rfl⟩ := List.append_of_mem hel
    exact .inr ⟨t2' ++ e3 :: t2'' ++ efs, σ3, obs, Language.Step.of_primStep hstep⟩

omit iG in
@[rocq_alias wp_adequacy_gen]
theorem wp_adequacy_gen [InvGpreS GF] (s : Stuckness) (e : Expr) (σ : State) (φ : Val → Prop)
    (Hwp : ∀ [InvGS_gen hlc GF] (κs : List Obs),
        ⊢ iprop(|={⊤}=>
          ∃ (stateI : State → List Obs → IProp GF)
            (forkPost : Val → IProp GF),
          letI _ : IrisGS_gen hlc Expr GF :=
            .mk (toStateInterp := ⟨fun σ _ κs _ => stateI σ κs⟩) (fun _ => 0) forkPost
              (fun _ _ _ _ => fupd_intro)
          iprop(stateI σ κs ∗ WP e @ s ; ⊤ {{ v, ⌜φ v⌝ }}))) :
    adequate s e σ (fun v _ => φ v) := by
  refine (adequate_alt s e σ (fun v _ => φ v)).mpr ?_
  intro t2 σ2 hreach
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF) (hlc := hlc) s (Hsteps := hsteps) (numLaters := fun _ => 0)
  iintro %Hinv
  imod Hwp κs with ⟨%Hst, %Hfork, ⟨Hst, Hwp⟩⟩
  iexists (λ σ _ κs _ => Hst σ κs), [(λ v => iprop(⌜φ v⌝))], Hfork, (fun _ _ _ _ => fupd_intro)
  dsimp only
  imodintro
  iframe
  isplitl [Hwp]
  · iapply BigSepL2.bigSepL2_singleton; iframe
  iintro %_ %_ %Heq %_ %HNS Hst Hwptp _
  iapply fupd_mask_intro_discard empty_subset
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hwptp with ⟨%e', %_, %Heq', Hpost, H⟩
  subst Heq' Heq
  dsimp only [List.cons_append, List.length_cons, Nat.pred_eq_sub_one, Nat.add_one_sub_one]
  icases BigSepL2.bigSepL2_nil_inv_right $$ H with %Heq
  subst Heq
  cases h : toVal e'
  · ipure_intro; grind
  · dsimp only [Option.elim_some]; icases Hpost with %Hpost
    ipure_intro; grind

@[rocq_alias wp_adequacy]
abbrev wp_adequacy := @wp_adequacy_gen .hasLC

omit iG in
@[rocq_alias wp_invariance_gen]
theorem wp_invariance_gen [InvGpreS GF] (s : Stuckness) (e1 : Expr) (σ1 σ2 : State) (t2 : List Expr)
    (φ : Prop)
    (Hwp : ∀ [InvGS_gen hlc GF] (κs : List Obs),
        ⊢ iprop(|={⊤}=>
          ∃ (stateI : State → List Obs → Nat → IProp GF)
            (forkPost : Val → IProp GF),
          letI _ : IrisGS_gen hlc Expr GF := .mk (toStateInterp := ⟨fun σ _ => stateI σ⟩)
            (fun _ => 0) forkPost (fun _ _ _ _ => fupd_intro)
          iprop(stateI σ1 κs 0 ∗ WP e1 @ s ; ⊤ {{ _v, iprop(True) }} ∗
                (stateI σ2 [] (.pred (List.length t2)) -∗ ∃ (E : CoPset), |={⊤,E}=> ⌜φ⌝))))
    (Hsteps : ([e1], σ1) -·->ₜₚ* (t2, σ2)) :
    φ := by
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp Hsteps
  apply wp_strong_adequacy_gen (GF := GF) (hlc := hlc) s (Hsteps := hsteps) (numLaters := fun _ => 0)
  iintro %Hinv
  imod Hwp κs with ⟨%Hst, %Hfork, ⟨Hst, Hwp, Hcont⟩⟩
  iexists ((λ σ _ => Hst σ)), [(λ _ => iprop(True))], Hfork, (fun _ _ _ _ => fupd_intro)
  dsimp only
  imodintro
  iframe Hst
  isplitl [Hwp]
  · iapply BigSepL2.bigSepL2_singleton; iframe
  iintro %_ %_ %Heq %_ %_ Hst Hwptp _
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hwptp with ⟨%_, %_, %Heq', _, H⟩
  subst Heq' Heq
  dsimp only [List.cons_append, List.length_cons, Nat.pred_eq_sub_one, Nat.add_one_sub_one]
  icases BigSepL2.bigSepL2_nil_inv_right $$ H with %Heq
  subst Heq
  icases Hcont $$ [Hst] with ⟨%_, >Hcont⟩
  · simp only [List.nil_append, refl]
  iapply fupd_mask_intro_discard empty_subset
  iframe Hcont

@[rocq_alias wp_invariance]
abbrev wp_invariance := @wp_invariance_gen .hasLC

end
end Iris.ProgramLogic
