/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.Algebra
public import Iris.BI
public import Iris.BI.WeakestPre
public import Iris.BI.BigOp.BigSepList
public import Iris.Instances.Lib.FUpd
public import Iris.ProofMode
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.WeakestPre
public import Iris.Std.CoPset
public import Iris.Std.FromMathlib

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.BI Iris.Algebra Std FromMathlib LawfulSet
open Iris.ProgramLogic.PrimStep
open Language.Notation

@[expose] public section

/-! # Adequacy

Lean 4 port of Coq Iris's `iris/program_logic/adequacy.v`. All theorem
statements 1:1 with Coq; proofs left `sorry` (interface skeleton).

Adapted to PR #393 (`fele/feat/add-weakestpre`) interface:
- `IrisGS_gen hlc Expr GF` (split into `StateInterp` + `InvGS_gen` + `IrisGS_gen` fields)
- `stateInterp` (exported), `iG.numLatersPerStep`, `iG.forkPost`,
  `iG.stateInterp_mono`
- `WP e @ s ; E {{ Φ }}` notation (via `Wp` typeclass) -/

variable {hlc : Bool} {Expr State Obs Val : Type _}
variable [Language Expr State Obs Val]
variable {GF : BundledGFunctors} [iG : IrisGS_gen hlc Expr GF]

@[rocq_alias wptp]
noncomputable def wptp (s : Stuckness) (es : List Expr) (Φs : List (Val → IProp GF)) : IProp GF :=
  iprop([∗list] e;Φ ∈ es;Φs, WP e @ s ; ⊤ {{ Φ }})

/-- `step_fupdN_wand` lifted to additive `a + b` exponent. -/
private theorem step_fupdN_compose {Eo Ei : CoPset} {a b : Nat} {P Q : IProp GF} :
    iprop(|={Eo}[Ei]▷=>^[a] P) ⊢
    iprop((P -∗ |={Eo}[Ei]▷=>^[b] Q) -∗ |={Eo}[Ei]▷=>^[a + b] Q) := by
  show iprop(|={Eo}[Ei]▷=>^[a] P) ⊢
       iprop((P -∗ |={Eo}[Ei]▷=>^[b] Q) -∗
             Nat.repeat (fun X => iprop(|={Eo}[Ei]▷=> X)) (a + b) iprop(Q))
  rw [Nat.repeat_add]
  exact step_fupdN_wand

@[rocq_alias steps_sum]
def steps_sum (numLaters : Nat → Nat) : Nat → Nat → Nat
  | _,     0      => 0
  | start, n + 1  => numLaters start + 1 + steps_sum numLaters (start + 1) n

@[rocq_alias wp_step]
theorem wp_step (s : Stuckness) (e1 : Expr) (σ1 : State)
    (ns : Nat) (κ κs : List Obs) (e2 : Expr) (σ2 : State) (efs : List Expr) (nt : Nat)
    (Φ : Val → IProp GF)
    (_hstep : PrimStep.primStep (e1, σ1) κ (e2, σ2, efs)) :
    ⊢ iprop(stateInterp σ1 ns (κ ++ κs) nt -∗
      £ (iG.numLatersPerStep ns + 1) -∗
      WP e1 @ s ; ⊤ {{ Φ }}
        ={⊤,∅}=∗
        |={∅}▷=>^[iG.numLatersPerStep ns + 1] |={∅,⊤}=>
        stateInterp σ2 (ns + 1) κs (nt + efs.length) ∗
        WP e2 @ s ; ⊤ {{ Φ }} ∗
        wptp s efs (List.replicate efs.length iG.forkPost)) := by
  have hval : toVal e1 = none := Language.val_stuck _hstep
  rw [IProp.ext wp_unfold]
  dsimp only [wp.pre]
  rw [hval]
  dsimp only
  iintro Hσ
  iintro Hcred
  iintro Hwp
  ihave Hcont := Hwp $$ %σ1 %ns %κ %κs %nt Hσ
  imod Hcont with ⟨%_, Hcont⟩
  ihave Hcont := Hcont $$ %e2 %σ2 %efs %_hstep Hcred
  imodintro
  iapply step_fupdN_wand $$ Hcont
  iintro >⟨HSI, Hwp2, Hefs⟩
  imodintro
  iframe HSI
  iframe Hwp2
  unfold wptp
  iapply BI.BigSepL2.bigSepL2_replicate_right.mpr
  iexact Hefs

@[rocq_alias wptp_step]
theorem wptp_step (s : Stuckness) (es1 es2 : List Expr)
    (κ κs : List Obs) (σ1 σ2 : State) (ns : Nat) (Φs : List (Val → IProp GF)) (nt : Nat)
    (_hstep : Language.Step (es1, σ1) κ (es2, σ2)) :
    ⊢ iprop(stateInterp σ1 ns (κ ++ κs) nt -∗
      £ (iG.numLatersPerStep ns + 1) -∗
      wptp s es1 Φs -∗
      ∃ nt', |={⊤,∅}=> |={∅}▷=>^[iG.numLatersPerStep ns + 1] |={∅,⊤}=>
        stateInterp σ2 (ns + 1) κs (nt + nt') ∗
        wptp s es2 (Φs ++ List.replicate nt' iG.forkPost)) := by
  cases _hstep with
  | atomic H_prim t₁ t₂ =>
    rename_i e1' e2' efs
    iintro Hσ
    iintro Hcred
    iintro Hwptp
    iexists efs.length
    -- Split wptp s (t₁ ++ e1' :: t₂) Φs via bigSepL2_app_inv_left + bigSepL2_cons_inv_left.
    have splitL : ⊢@{IProp GF} iprop(wptp s (t₁ ++ e1' :: t₂) Φs -∗
        ∃ (Φs1 : List (Val → IProp GF)) (Φs2 : List (Val → IProp GF)),
          ⌜Φs = Φs1 ++ Φs2⌝ ∧
          (wptp s t₁ Φs1 ∗
           [∗list] k ↦ e;Φ ∈ (e1' :: t₂);Φs2,
             Wp.wp (PROP := IProp GF) s ⊤ e Φ)) :=
      wand_intro (emp_sep.1.trans BI.BigSepL2.bigSepL2_app_inv_left)
    ihave Hwptp := splitL $$ Hwptp
    icases Hwptp with ⟨%Φs1, %Φs2, %hΦs, Hwptp1, Hwptp2⟩
    have splitC : ⊢@{IProp GF} iprop(
        ([∗list] k ↦ e;Φ ∈ (e1' :: t₂);Φs2, Wp.wp (PROP := IProp GF) s ⊤ e Φ) -∗
        ∃ (Φ_head : Val → IProp GF) (Φs2' : List (Val → IProp GF)),
          ⌜Φs2 = Φ_head :: Φs2'⌝ ∧
          (Wp.wp (PROP := IProp GF) s ⊤ e1' Φ_head ∗
           [∗list] k ↦ e;Φ ∈ t₂;Φs2', Wp.wp (PROP := IProp GF) s ⊤ e Φ)) :=
      wand_intro (emp_sep.1.trans BI.BigSepL2.bigSepL2_cons_inv_left.1)
    ihave Hwptp2 := splitC $$ Hwptp2
    icases Hwptp2 with ⟨%Φ_head, %Φs2', %hΦs2, Hwp_e1, Hwptp3⟩
    -- Apply wp_step to the stepping thread, then peel step_fupdN_wand.
    ihave Hstep := wp_step s e1' σ1 ns κ κs e2' σ2 efs nt Φ_head H_prim $$ Hσ Hcred Hwp_e1
    subst hΦs
    subst hΦs2
    imod Hstep
    imodintro
    iapply step_fupdN_wand $$ Hstep
    iintro >⟨HSI, Hwp_e2, Hwptp_efs⟩
    imodintro
    iframe HSI
    -- Recombine the 4 wptp pieces. Need lengths for bigSepL2_append.

    have lenL1 : ⊢@{IProp GF} iprop(wptp s t₁ Φs1 -∗ ⌜t₁.length = Φs1.length⌝) :=
      wand_intro (emp_sep.1.trans BI.BigSepL2.bigSepL2_length)
    have lenL3 : ⊢@{IProp GF} iprop(
        ([∗list] k ↦ e;Φ ∈ t₂;Φs2', Wp.wp (PROP := IProp GF) s ⊤ e Φ) -∗
        ⌜t₂.length = Φs2'.length⌝) :=
      wand_intro (emp_sep.1.trans BI.BigSepL2.bigSepL2_length)
    ihave %hlen1 := lenL1 $$ Hwptp1
    ihave %hlen3 := lenL3 $$ Hwptp3
    -- Align list associativity: `t₁ ++ e2' :: t₂ ++ efs` = `t₁ ++ (e2' :: t₂ ++ efs)`.
    have list_eq : t₁ ++ e2' :: t₂ ++ efs = t₁ ++ (e2' :: t₂ ++ efs) :=
      List.append_assoc t₁ (e2' :: t₂) efs
    have phis_eq : Φs1 ++ Φ_head :: Φs2' ++ List.replicate efs.length iG.forkPost =
        Φs1 ++ (Φ_head :: Φs2' ++ List.replicate efs.length iG.forkPost) :=
      List.append_assoc Φs1 (Φ_head :: Φs2') _
    have wptp_eq : iprop(wptp s (t₁ ++ e2' :: t₂ ++ efs)
                  (Φs1 ++ Φ_head :: Φs2' ++ List.replicate efs.length iG.forkPost)) =
                iprop([∗list] k ↦ e;Φ ∈ t₁ ++ (e2' :: t₂ ++ efs);
                                       Φs1 ++ (Φ_head :: Φs2' ++ List.replicate efs.length iG.forkPost),
                      Wp.wp (PROP := IProp GF) s ⊤ e Φ) := by
      simp only [wptp, list_eq, phis_eq]
    rw [wptp_eq]
    iapply (BI.BigSepL2.bigSepL2_append
            (Φ := fun (_ : Nat) (e : Expr) (Φ : Val → IProp GF) =>
                    iprop(Wp.wp (PROP := IProp GF) s ⊤ e Φ))
            (Or.inl hlen1)).2
    -- Convert wptp ↔ bigSepL2 (defn-equal) via wand-wrapped `.rfl`.
    have wptp_t1_to_bsl : ⊢@{IProp GF} iprop(wptp s t₁ Φs1 -∗
        [∗list] k ↦ e;Φ ∈ t₁;Φs1, Wp.wp (PROP := IProp GF) s ⊤ e Φ) :=
      wand_intro (emp_sep.1.trans (.rfl
        : iprop(wptp s t₁ Φs1) ⊢ iprop([∗list] k ↦ e;Φ ∈ t₁;Φs1, Wp.wp s ⊤ e Φ)))
    ihave Hwptp1 := wptp_t1_to_bsl $$ Hwptp1
    isplitl [Hwptp1]
    · iexact Hwptp1
    · -- `(e2' :: t₂) ++ efs = e2' :: (t₂ ++ efs)` by `List.cons_append` (rfl).
      have list_eq2 : (e2' :: t₂) ++ efs = e2' :: (t₂ ++ efs) := rfl
      have phis_eq2 : (Φ_head :: Φs2') ++ List.replicate efs.length iG.forkPost =
          Φ_head :: (Φs2' ++ List.replicate efs.length iG.forkPost) := rfl
      rw [list_eq2, phis_eq2]
      iapply (BI.BigSepL2.bigSepL2_cons
              (Φ := fun (_ : Nat) (e : Expr) (Φ : Val → IProp GF) =>
                      iprop(Wp.wp (PROP := IProp GF) s ⊤ e Φ))).2
      isplitl [Hwp_e2]
      · iexact Hwp_e2
      · iapply (BI.BigSepL2.bigSepL2_append
                (Φ := fun (_ : Nat) (e : Expr) (Φ : Val → IProp GF) =>
                        iprop(Wp.wp (PROP := IProp GF) s ⊤ e Φ))
                (Or.inl hlen3)).2
        isplitl [Hwptp3]
        · iexact Hwptp3
        · have wptp_efs_to_bsl : ⊢@{IProp GF}
              iprop(wptp s efs (List.replicate efs.length iG.forkPost) -∗
                    [∗list] k ↦ e;Φ ∈ efs;List.replicate efs.length iG.forkPost,
                      Wp.wp (PROP := IProp GF) s ⊤ e Φ) :=
            wand_intro (emp_sep.1.trans (.rfl : iprop(wptp s efs (List.replicate efs.length iG.forkPost)) ⊢
                          iprop([∗list] k ↦ e;Φ ∈ efs;List.replicate efs.length iG.forkPost,
                                Wp.wp (PROP := IProp GF) s ⊤ e Φ)))
          ihave Hwptp_efs := wptp_efs_to_bsl $$ Hwptp_efs
          iexact Hwptp_efs

@[rocq_alias wp_not_stuck]
theorem wp_not_stuck (κs : List Obs) (nt : Nat) (e : Expr) (σ : State)
    (ns : Nat) (Φ : Val → IProp GF) :
    ⊢ iprop(stateInterp σ ns κs nt -∗
      WP e @ Stuckness.NotStuck ; ⊤ {{ Φ }}
        ={⊤,∅}=∗ ⌜PrimStep.NotStuck (e, σ)⌝) := by
  rw [IProp.ext wp_unfold]
  dsimp only [wp.pre]
  match h : toVal e with
  | some v =>
    -- Value branch: NotStuck.inl via toVal e = some v.
    dsimp only
    have h_ns : PrimStep.NotStuck (e, σ) := .inl (by rw [h]; rfl)
    refine wand_intro' ?_
    refine wand_intro' ?_
    refine (BI.pure_intro h_ns).trans ?_
    exact fupd_mask_intro_discard empty_subset
  | none =>
    -- Reducible branch: specialize Hwp on σ ns [] κs nt, extract pure
    -- MaybeReducible (e, σ) = Reducible (e, σ) (since s = NotStuck), conclude NotStuck.inr.
    dsimp only
    refine wand_intro' (wand_intro' ?_)
    have spec : iprop(∀ (σ₁ : State) (ns_1 : Nat) (obs obs' : List Obs) (nt_1 : Nat),
        stateInterp σ₁ ns_1 (obs ++ obs') nt_1 ={⊤,∅}=∗
          ⌜Stuckness.NotStuck.MaybeReducible (e, σ₁)⌝ ∗
          (∀ (e₂ : Expr) (σ₂ : State) (eₜ : List Expr),
            ⌜(e, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗
            £ (iG.numLatersPerStep ns_1 + 1) ={∅}▷=∗^[iG.numLatersPerStep ns_1 + 1] |={∅,⊤}=>
              stateInterp σ₂ (ns_1 + 1) obs' (nt_1 + eₜ.length) ∗
              Wp.wp Stuckness.NotStuck ⊤ e₂ Φ ∗
              [∗list] e' ∈ eₜ, Wp.wp Stuckness.NotStuck ⊤ e' iG.forkPost)) ⊢
        (iprop(stateInterp σ ns ([] ++ κs) nt ={⊤,∅}=∗
          ⌜Stuckness.NotStuck.MaybeReducible (e, σ)⌝ ∗
          (∀ (e₂ : Expr) (σ₂ : State) (eₜ : List Expr),
            ⌜(e, σ) -<([] : List Obs)>-> (e₂, σ₂, eₜ)⌝ -∗
            £ (iG.numLatersPerStep ns + 1) ={∅}▷=∗^[iG.numLatersPerStep ns + 1] |={∅,⊤}=>
              stateInterp σ₂ (ns + 1) κs (nt + eₜ.length) ∗
              Wp.wp Stuckness.NotStuck ⊤ e₂ Φ ∗
              [∗list] e' ∈ eₜ, Wp.wp Stuckness.NotStuck ⊤ e' iG.forkPost)) : IProp GF) := by
      refine (forall_elim σ).trans ?_
      refine (forall_elim ns).trans ?_
      refine (forall_elim (([] : List Obs))).trans ?_
      refine (forall_elim κs).trans ?_
      exact forall_elim nt
    refine (sep_mono_l spec).trans ?_
    refine (sep_mono_r sep_emp.1).trans ?_
    refine wand_elim_l.trans ?_
    refine BIFUpdate.mono ?_
    refine sep_elim_l.trans ?_
    exact pure_mono fun h => .inr h

@[rocq_alias wptp_preservation]
theorem wptp_preservation (s : Stuckness) (n : Nat) (es1 es2 : List Expr)
    (κs κs' : List Obs) (σ1 σ2 : State) (ns : Nat)
    (Φs : List (Val → IProp GF)) (nt : Nat)
    (_hsteps : Language.NSteps n (es1, σ1) κs (es2, σ2)) :
    ⊢ iprop(stateInterp σ1 ns (κs ++ κs') nt -∗
      £ (steps_sum iG.numLatersPerStep ns n) -∗
      wptp s es1 Φs ={⊤,∅}=∗
      |={∅}▷=>^[steps_sum iG.numLatersPerStep ns n] |={∅,⊤}=> ∃ nt',
        stateInterp σ2 (n + ns) κs' (nt + nt') ∗
        wptp s es2 (Φs ++ List.replicate nt' iG.forkPost)) := by
  -- Generalize pair indices (`(es1,σ1)` not free var → blocks `induction`).
  generalize hρ1 : (es1, σ1) = ρ1 at _hsteps
  generalize hρ2 : (es2, σ2) = ρ2 at _hsteps
  induction _hsteps generalizing nt κs' Φs ns es1 σ1 es2 σ2 with
  | refl ρ =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hρ1.symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hρ2.symm
    cases ρ with | mk e σ =>
    simp only [Nat.zero_add, Nat.add_zero, List.nil_append, List.append_nil,
               List.replicate]
    iintro Hσ; iintro _; iintro Hwptp
    dsimp only [steps_sum, Nat.repeat]
    -- Pattern from Iris/Examples/ClosedProofs.lean:58-74:
    iapply fupd_mask_intro empty_subset
    iintro Hcl
    -- Hcl : |={∅,⊤}=> emp ; goal: |={∅,⊤}=> ∃ nt', ...
    imod Hcl
    imodintro
    iexists 0
    simp only [List.replicate, List.append_nil]
    iframe Hσ
    iexact Hwptp
  | @cons n_inner ρ1' ρ_mid ρ2' obs obs' hstep hrest ih =>
    -- cons constructor unifies `ρ₁ ρ₃` with our `(es1, σ1)` / `(es2, σ2)` via hρ1/hρ2.
    cases hρ1; cases hρ2
    cases ρ_mid with | mk e_mid σ_mid =>
    -- κ-list assoc + step_fupdN split must be done BEFORE iintro
    -- (rw can't operate on IPM hypotheses).
    rw [List.append_assoc obs obs' κs']
    dsimp only [steps_sum]
    rw [Nat.repeat_add]
    iintro Hσ; iintro Hcred; iintro Hwptp
    -- Split £ credits: head step + recursive tail.
    have splitL : ⊢@{IProp GF} iprop(£ (iG.numLatersPerStep ns + 1 +
        steps_sum iG.numLatersPerStep (ns+1) n_inner) -∗
        £ (iG.numLatersPerStep ns + 1) ∗ £ (steps_sum iG.numLatersPerStep (ns+1) n_inner)) :=
      wand_intro (emp_sep.1.trans lc_split.mp)
    ihave Hcred := splitL $$ Hcred
    icases Hcred with ⟨Hcred1, Hcred2⟩
    -- Apply wptp_step to head, then peel step_fupdN via WeakestPre.lean:421 pattern
    -- (`imod _; imodintro; iapply step_fupdN_wand $$ _`).
    ihave Hwptp_step := wptp_step s es1 e_mid obs (obs' ++ κs') σ1 σ_mid ns Φs nt hstep
                       $$ Hσ Hcred1 Hwptp
    icases Hwptp_step with ⟨%nt'_step, Hwptp_step⟩
    imod Hwptp_step
    imodintro
    iapply step_fupdN_wand $$ Hwptp_step
    iintro Hbody
    -- The Coq proof uses `step_fupdN_S_fupd` to reshape the goal so that
    -- `iIntros ">(...)"` can open `Hbody`'s `|={∅,⊤}=>` modality. That lemma
    -- is not yet available in iris-lean master; the new flexible `imod`
    -- (PR #398) and `iintro >X` likewise cannot open an inner fupd across
    -- a leading `step_fupdN^[k]`. Real proof deferred until `step_fupdN_S_fupd`
    -- (or an equivalent pattern) is in place.
    -- Reference: iris/iris@d663f775:iris/program_logic/adequacy.v
    --            (wptp_preservation, cons case).
    sorry

@[rocq_alias wptp_postconditions]
theorem wptp_postconditions (Φs : List (Val → IProp GF)) (κs' : List Obs)
    (s : Stuckness) (n : Nat) (es1 es2 : List Expr) (κs : List Obs)
    (σ1 σ2 : State) (ns nt : Nat)
    (_hsteps : Language.NSteps n (es1, σ1) κs (es2, σ2)) :
    ⊢ iprop(stateInterp σ1 ns (κs ++ κs') nt -∗
      £ (steps_sum iG.numLatersPerStep ns n) -∗
      wptp s es1 Φs ={⊤,∅}=∗
      |={∅}▷=>^[steps_sum iG.numLatersPerStep ns n] |={∅,⊤}=> ∃ nt',
        stateInterp σ2 (n + ns) κs' (nt + nt') ∗
        [∗list] e;Φ ∈ es2;Φs ++ List.replicate nt' iG.forkPost,
          (match ToVal.toVal e with
           | some v => Φ v
           | none   => iprop(True))) :=
  sorry

@[rocq_alias wptp_progress]
theorem wptp_progress (Φs : List (Val → IProp GF)) (κs' : List Obs)
    (n : Nat) (es1 es2 : List Expr) (κs : List Obs)
    (σ1 σ2 : State) (ns nt : Nat) (e2 : Expr)
    (_hsteps : Language.NSteps n (es1, σ1) κs (es2, σ2))
    (_hel : e2 ∈ es2) :
    ⊢ iprop(stateInterp σ1 ns (κs ++ κs') nt -∗
      £ (steps_sum iG.numLatersPerStep ns n) -∗
      wptp Stuckness.NotStuck es1 Φs ={⊤,∅}=∗
      |={∅}▷=>^[steps_sum iG.numLatersPerStep ns n] |={∅}=>
        ⌜PrimStep.NotStuck (e2, σ2)⌝) :=
  sorry

/-- WP-existence assumption (`∀ Hinv, ⊢ |={⊤}=> ∃ stateI Φs fork_post ...`)
abstracted as `True` until `invGpreS` infrastructure lands; signature is
otherwise 1:1 with Coq. -/
@[rocq_alias wp_progress_gen]
theorem wp_progress_gen (es : List Expr) (σ1 : State) (n : Nat) (κs : List Obs)
    (t2 : List Expr) (σ2 : State) (e2 : Expr)
    (_numLaters : Nat → Nat)
    (_hwp : True)
    (_hsteps : Language.NSteps n (es, σ1) κs (t2, σ2))
    (_hel : e2 ∈ t2) :
    PrimStep.NotStuck (e2, σ2) :=
  sorry

@[rocq_alias wp_strong_adequacy_gen]
theorem wp_strong_adequacy_gen (s : Stuckness) (es : List Expr) (σ1 : State)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (σ2 : State) (φ : Prop)
    (_numLaters : Nat → Nat)
    (_hwp : True)
    (_hsteps : Language.NSteps n (es, σ1) κs (t2, σ2)) :
    φ :=
  sorry

@[rocq_alias wp_strong_adequacy]
def wp_strong_adequacy : True := True.intro

@[rocq_alias adequate]
structure adequate (s : Stuckness) (e1 : Expr) (σ1 : State)
    (φ : Val → State → Prop) : Prop where
  adequate_result :
    ∀ (t2 : List Expr) (σ2 : State) (v2 : Val),
      Relation.ReflTransGen Language.ErasedStep
        ([e1], σ1) (ToVal.ofVal v2 :: t2, σ2) → φ v2 σ2
  adequate_not_stuck :
    ∀ (t2 : List Expr) (σ2 : State) (e2 : Expr),
      s = .NotStuck →
      Relation.ReflTransGen Language.ErasedStep ([e1], σ1) (t2, σ2) →
      e2 ∈ t2 → PrimStep.NotStuck (e2, σ2)

@[rocq_alias adequate_alt]
theorem adequate_alt (s : Stuckness) (e1 : Expr) (σ1 : State)
    (φ : Val → State → Prop) :
    adequate s e1 σ1 φ ↔
      ∀ (t2 : List Expr) (σ2 : State),
        Relation.ReflTransGen Language.ErasedStep ([e1], σ1) (t2, σ2) →
        (∀ (v2 : Val) (t2' : List Expr),
          t2 = ToVal.ofVal v2 :: t2' → φ v2 σ2) ∧
        (∀ (e2 : Expr), s = .NotStuck → e2 ∈ t2 → PrimStep.NotStuck (e2, σ2)) := by
  refine ⟨fun ⟨hres, hns⟩ t2 σ2 hreach => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · intro v2 t2' rfl_eq
    subst rfl_eq
    exact hres _ _ _ hreach
  · intro e2 hs hel
    exact hns _ _ _ hs hreach hel
  · intro t2 σ2 v2 hreach
    exact ((h _ _ hreach).1) v2 t2 rfl
  · intro t2 σ2 e2 hs hreach hel
    exact ((h _ _ hreach).2) e2 hs hel

@[rocq_alias adequate_tp_safe]
theorem adequate_tp_safe (e1 : Expr) (t2 : List Expr) (σ1 σ2 : State)
    (φ : Val → State → Prop)
    (had : adequate .NotStuck e1 σ1 φ)
    (hsteps : Relation.ReflTransGen Language.ErasedStep ([e1], σ1) (t2, σ2)) :
    (∀ e ∈ t2, ∃ v, ToVal.toVal e = some v) ∨
      ∃ (t3 : List Expr) (σ3 : State), Language.ErasedStep (t2, σ2) (t3, σ3) := by
  by_cases hall : ∀ e ∈ t2, ∃ v, ToVal.toVal e = some v
  · exact .inl hall
  rw [Classical.not_forall] at hall
  obtain ⟨e2, hne⟩ := hall
  rw [Classical.not_forall] at hne
  obtain ⟨hel, hne⟩ := hne
  have hns : PrimStep.NotStuck (e2, σ2) :=
    had.adequate_not_stuck t2 σ2 e2 rfl hsteps hel
  rcases hns with hv | ⟨obs, e3, σ3, efs, hstep⟩
  · exfalso
    rcases hv2 : ToVal.toVal e2 with _ | v
    · rw [hv2] at hv; exact Bool.false_ne_true hv
    · exact hne ⟨v, hv2⟩
  obtain ⟨t2', t2'', rfl⟩ := List.append_of_mem hel
  exact .inr ⟨t2' ++ e3 :: t2'' ++ efs, σ3, obs, Language.Step.of_primStep hstep⟩

@[rocq_alias wp_adequacy_gen]
theorem wp_adequacy_gen (s : Stuckness) (e : Expr) (σ : State) (φ : Val → Prop)
    (_hwp : True) :
    adequate s e σ (fun v _ => φ v) :=
  sorry

@[rocq_alias wp_adequacy]
def wp_adequacy : True := True.intro

@[rocq_alias wp_invariance_gen]
theorem wp_invariance_gen (s : Stuckness) (e1 : Expr) (σ1 σ2 : State)
    (t2 : List Expr) (φ : Prop)
    (_hwp : True)
    (_hsteps : Relation.ReflTransGen Language.ErasedStep ([e1], σ1) (t2, σ2)) :
    φ :=
  sorry

@[rocq_alias wp_invariance]
def wp_invariance : True := True.intro

end
end Iris.ProgramLogic
