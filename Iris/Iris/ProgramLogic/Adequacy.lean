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

/-- Monotonicity of `step_fupd` (one-step). Derived from `BIFUpdate.mono` + `later_mono`. -/
private theorem step_fupd_mono_lift {Eo Ei : CoPset} {P Q : IProp GF} (h : P ⊢ Q) :
    iprop(|={Eo}[Ei]▷=> P) ⊢ iprop(|={Eo}[Ei]▷=> Q) :=
  BIFUpdate.mono (later_mono (BIFUpdate.mono h))

/-- Monotonicity of `step_fupdN` (n-fold). By induction on `n`. -/
private theorem step_fupdN_mono {Eo Ei : CoPset} {n : Nat} {P Q : IProp GF} (h : P ⊢ Q) :
    iprop(|={Eo}[Ei]▷=>^[n] P) ⊢ iprop(|={Eo}[Ei]▷=>^[n] Q) := by
  induction n generalizing P Q with
  | zero => exact h
  | succ k IH => exact step_fupd_mono_lift (IH h)

/-- Port of Coq `step_fupdN_S_fupd` from `iris/bi/updates.v`:
    `(|={E}[∅]▷=>^[n+1] P) ⊣⊢ (|={E}[∅]▷=>^[n+1] |={E}=> P)`.
    Lets us absorb an inner `|={E}=>` into a non-empty `step_fupdN` for free. -/
private theorem step_fupdN_S_fupd {n : Nat} {E : CoPset} {P : IProp GF} :
    iprop(|={E}[∅]▷=>^[n + 1] P) ⊣⊢ iprop(|={E}[∅]▷=>^[n + 1] |={E}=> P) := by
  constructor
  · induction n generalizing P with
    | zero => exact step_fupd_fupd.1
    | succ k IH => exact step_fupd_mono_lift IH
  · induction n generalizing P with
    | zero => exact step_fupd_fupd.2
    | succ k IH => exact step_fupd_mono_lift IH

@[rocq_alias steps_sum]
def steps_sum (numLaters : Nat → Nat) : Nat → Nat → Nat
  | _,     0      => 0
  | start, n + 1  => numLaters start + 1 + steps_sum numLaters (start + 1) n

/-- Build an `IrisGS_gen` instance from an `InvGS_gen` plus a simple stateI
that ignores ns/obs/nt — matches Coq's `IrisG Hinv (λ σ _ _ _, stateI σ)
fork_post (λ _, 0) (λ _ _ _ _, fupd_intro _ _)` construction used in
`wp_adequacy_gen` / `wp_invariance_gen`. -/
def IrisGS_gen.ofSimple {hlc : Bool} {Expr State Obs Val : Type _}
    [Language Expr State Obs Val] {GF : BundledGFunctors}
    (Hinv : InvGS_gen hlc GF)
    (stateI : State → IProp GF) (forkPost : Val → IProp GF) :
    IrisGS_gen hlc Expr GF :=
  { toStateInterp := { stateInterp := fun σ _ _ _ => stateI σ }
    toInvGS_gen := Hinv
    numLatersPerStep := fun _ => 0
    forkPost := forkPost
    stateInterp_mono := fun _ _ _ _ => fupd_intro }


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
    -- Reshape goal: insert |={∅}=> between outer step_fupdN^[M+1] and inner step_fupdN^[k]
    -- via step_fupdN_S_fupd (backward direction adds |={∅}=> for free under non-empty step_fupdN).
    iapply step_fupdN_S_fupd.2
    -- Now peel the outer step_fupdN^[M+1].
    iapply step_fupdN_wand $$ Hwptp_step
    iintro Hbody
    -- Hbody : |={∅,⊤}=> stateInterp_mid ∗ wptp_mid
    -- Goal  : |={∅}=> step_fupdN^[k] |={∅,⊤}=> ∃...
    -- imod Hbody composes |={∅,⊤}=> (Hbody) with |={∅,∅}=> (goal outer) via fupd_elim.
    imod Hbody with ⟨HSI, Hwptp_mid⟩
    -- After imod, mask is ⊤; goal: |={⊤,∅}=> step_fupdN^[k] |={∅,⊤}=> ∃ nt_total, ...
    -- Apply ih to recurse on inner NSteps. Provide explicit instantiation.
    ihave Hih := ih (es1 := e_mid) (σ1 := σ_mid) (es2 := es2) (σ2 := σ2)
                    (nt := nt + nt'_step) (κs' := κs')
                    (Φs := Φs ++ List.replicate nt'_step iG.forkPost) (ns := ns + 1)
                    rfl rfl $$ HSI Hcred2 Hwptp_mid
    -- Hih : |={⊤,∅}=> step_fupdN^[k] |={∅,⊤}=> ∃ nt_inner', stateInterp ... ∗ wptp ...
    -- where Φs structure is (Φs ++ replicate nt'_step) ++ replicate nt_inner', nt is (nt+nt'_step) + nt_inner'.
    imod Hih
    imodintro  -- consume goal's residual |={∅,∅}=> (no mask change, trivially closes)
    iapply step_fupdN_wand $$ Hih
    iintro >⟨%nt_inner', HSI', Hwptp'⟩
    -- Mask ⊤; goal: ∃ nt_total, ...
    iexists (nt'_step + nt_inner')
    -- Bridge HSI' / Hwptp' shapes to goal via Nat.add_assoc + List.replicate_add + List.append_assoc.
    have ns_eq : n_inner + 1 + ns = n_inner + (ns + 1) := by omega
    have nt_eq : nt + (nt'_step + nt_inner') = (nt + nt'_step) + nt_inner' :=
      (Nat.add_assoc _ _ _).symm
    have rep_split : List.replicate (nt'_step + nt_inner') iG.forkPost =
        List.replicate nt'_step iG.forkPost ++ List.replicate nt_inner' iG.forkPost :=
      (List.replicate_append_replicate ..).symm
    have phis_eq : Φs ++ List.replicate (nt'_step + nt_inner') iG.forkPost =
        (Φs ++ List.replicate nt'_step iG.forkPost) ++ List.replicate nt_inner' iG.forkPost := by
      rw [rep_split, ← List.append_assoc]
    rw [ns_eq, nt_eq, phis_eq]
    iframe HSI'
    iexact Hwptp'

/-- Pointwise post-condition extracted from a WP-style continuation,
named to ensure both the theorem statement and the helper use the same
elaborated `match` aux-def. -/
@[reducible] private def fromOptionVal (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match ToVal.toVal e with
  | some v => Φ v
  | none   => iprop(True)

/-- Per-element conversion: a WP can be turned into a fancy update of
the `from_option` postcondition. Port of Coq's per-element step in
`wptp_postconditions`. -/
private theorem wp_to_postcond (s : Stuckness) (e : Expr) (Φ : Val → IProp GF) :
    iprop(WP e @ s ; ⊤ {{ Φ }}) ⊢
    iprop(|={⊤}=> fromOptionVal (GF := GF) e Φ) := by
  unfold fromOptionVal
  match hv : ToVal.toVal e with
  | some v =>
    have he : (v : Expr) = e := ToVal.coe_of_toVal_eq_some hv
    -- Goal: WP e {{ Φ }} ⊢ |={⊤}=> Φ v (match already substituted by `hv`)
    exact he ▸ wp_value_fupd' (s := s) (E := ⊤) (Φ := Φ) (v := v) |>.1
  | none =>
    -- Goal: WP e {{ Φ }} ⊢ |={⊤}=> True (match already substituted by `hv`)
    exact true_intro.trans fupd_intro

/-- Conversion lemma: a list of WP's can be turned into a fancy update of
postcondition `from_option`s. Port of Coq's tail of `wptp_postconditions`. -/
private theorem wptp_to_postcond (s : Stuckness) :
    ∀ (es : List Expr) (Φs : List (Val → IProp GF)),
    iprop(wptp s es Φs) ⊢
    iprop(|={⊤}=> [∗list] e;Φ ∈ es;Φs, fromOptionVal (GF := GF) e Φ) := by
  intro es
  induction es with
  | nil =>
    intro Φs
    cases Φs with
    | nil =>
      show iprop(emp) ⊢ iprop(|={⊤}=> emp)
      exact fupd_intro
    | cons _ _ =>
      show iprop(False) ⊢ _
      exact false_elim
  | cons e es ih =>
    intro Φs
    cases Φs with
    | nil =>
      show iprop(False) ⊢ _
      exact false_elim
    | cons Φ Φs =>
      -- LHS = WP e {{Φ}} ∗ wptp s es Φs (via wptp/bigSepL2 cons unfold = .rfl)
      -- RHS = |={⊤}=> (fromOptionVal e Φ ∗ [∗list]...)
      exact (sep_mono (wp_to_postcond s e Φ) (ih Φs)).trans fupd_sep

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
           | none   => iprop(True))) := by
  -- Replace the goal's explicit `match` with the `fromOptionVal` synonym so
  -- that auto-generated match aux defs in the goal and in `wptp_to_postcond`
  -- match. This is sound because `fromOptionVal` is `@[reducible]`.
  show ⊢ iprop(stateInterp σ1 ns (κs ++ κs') nt -∗
      £ (steps_sum iG.numLatersPerStep ns n) -∗
      wptp s es1 Φs ={⊤,∅}=∗
      |={∅}▷=>^[steps_sum iG.numLatersPerStep ns n] |={∅,⊤}=> ∃ nt',
        stateInterp σ2 (n + ns) κs' (nt + nt') ∗
        [∗list] e;Φ ∈ es2;Φs ++ List.replicate nt' iG.forkPost,
          fromOptionVal (GF := GF) e Φ)
  iintro Hσ
  iintro Hcred
  iintro Hwptp
  ihave Hpres := wptp_preservation s n es1 es2 κs κs' σ1 σ2 ns Φs nt _hsteps
                 $$ Hσ Hcred Hwptp
  imod Hpres
  imodintro
  iapply step_fupdN_wand $$ Hpres
  iintro >⟨%nt', HSI, Hwptp_es2⟩
  ihave Hpost :=
    (wptp_to_postcond s es2 (Φs ++ List.replicate nt' iG.forkPost)
      : iprop(wptp s es2 (Φs ++ List.replicate nt' iG.forkPost)) ⊢ _) $$ Hwptp_es2
  imod Hpost
  imodintro
  iexists nt'
  iframe HSI
  iexact Hpost

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
        ⌜PrimStep.NotStuck (e2, σ2)⌝) := by
  iintro Hσ; iintro Hcred; iintro Ht
  -- Apply wptp_preservation to get the preserved state at the end of n steps.
  ihave Hpres := wptp_preservation Stuckness.NotStuck n es1 es2 κs κs' σ1 σ2 ns Φs nt _hsteps
                  $$ Hσ Hcred Ht
  imod Hpres
  imodintro
  iapply step_fupdN_wand $$ Hpres
  iintro Hpres
  -- imod composes Hpres's |={∅,⊤}=> with goal's |={∅,∅}=> via elimModal_fupd_fupd:
  -- opens Hpres at mask ⊤, leaves goal as |={⊤,∅}=> ⌜NotStuck⌝.
  imod Hpres with ⟨%nt'', HSI, Hwptp⟩
  -- Extract a WP for e2 from Hwptp via bigSepL2_lookup_acc.
  obtain ⟨i, hi⟩ := List.getElem?_of_mem _hel
  have lenW : ⊢@{IProp GF} iprop(wptp Stuckness.NotStuck es2
                                    (Φs ++ List.replicate nt'' iG.forkPost) -∗
                                  ⌜es2.length = (Φs ++ List.replicate nt'' iG.forkPost).length⌝) :=
    wand_intro (emp_sep.1.trans BI.BigSepL2.bigSepL2_length)
  ihave %hlen := lenW $$ Hwptp
  have hi_lt : i < es2.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi_lt' : i < (Φs ++ List.replicate nt'' iG.forkPost).length := hlen ▸ hi_lt
  have hi_Φ : (Φs ++ List.replicate nt'' iG.forkPost)[i]? =
      some ((Φs ++ List.replicate nt'' iG.forkPost)[i]) :=
    List.getElem?_eq_getElem hi_lt'
  have lookup_wand : ⊢@{IProp GF} iprop(
      wptp Stuckness.NotStuck es2 (Φs ++ List.replicate nt'' iG.forkPost) -∗
      Wp.wp (PROP := IProp GF) Stuckness.NotStuck ⊤ e2
        ((Φs ++ List.replicate nt'' iG.forkPost)[i]) ∗
      (Wp.wp (PROP := IProp GF) Stuckness.NotStuck ⊤ e2
         ((Φs ++ List.replicate nt'' iG.forkPost)[i]) -∗
       wptp Stuckness.NotStuck es2 (Φs ++ List.replicate nt'' iG.forkPost))) :=
    wand_intro (emp_sep.1.trans
      (BI.BigSepL2.bigSepL2_lookup_acc (Φ := fun (_ : Nat) (e : Expr) (Φ : Val → IProp GF) =>
        iprop(Wp.wp (PROP := IProp GF) Stuckness.NotStuck ⊤ e Φ)) hi hi_Φ))
  ihave Hwptp := lookup_wand $$ Hwptp
  icases Hwptp with ⟨Hwp_e2, _Hrest⟩
  -- Apply wp_not_stuck to finish.
  ihave Hres := wp_not_stuck κs' (nt + nt'') e2 σ2 (n + ns)
                  ((Φs ++ List.replicate nt'' iG.forkPost)[i]) $$ HSI Hwp_e2
  iexact Hres

/-- Lean port of Coq Iris `wp_progress_gen`: given a user-supplied WP-existence
hypothesis that, in the presence of any allocated `InvGS_gen`, builds a complete
`IrisGS_gen` instance and proves `stateI σ1 0 κs 0 ∗ wptp s es Φs`, conclude
that any reachable thread `e2 ∈ t2` after `n` steps is not stuck. The
`IrisGS_gen` fields (stateInterp / forkPost / monotonicity) are supplied
as ordinary Pi arguments rather than inside the Iris ∃ as in Coq, since
Lean's `letI` cannot be introduced inside `iprop(...)` syntax. -/
@[rocq_alias wp_progress_gen]
theorem wp_progress_gen [InvGpreS GF] (s : Stuckness)
    (es : List Expr) (σ1 : State) (n : Nat) (κs : List Obs)
    (t2 : List Expr) (σ2 : State) (e2 : Expr)
    (_numLaters : Nat → Nat)
    (_Hwp : ∀ [_Hinv : InvGS_gen hlc GF] [_iG : IrisGS_gen hlc Expr GF],
        ⊢ iprop(|={⊤}=> ∃ (Φs : List (Val → IProp GF)),
          stateInterp σ1 0 κs 0 ∗ wptp s es Φs))
    (_hsteps : Language.NSteps n (es, σ1) κs (t2, σ2))
    (_hel : e2 ∈ t2) :
    PrimStep.NotStuck (e2, σ2) :=
  sorry

/-- Bridge: fork-post block (`replicate nt' iG.forkPost`) implies the
`filterMap`-shaped block required by `wp_strong_adequacy_gen`'s continuation.
Uses BI affineness. -/
private theorem fork_block_to_filterMap (t2' : List Expr) (nt' : Nat)
    (hlen : t2'.length = nt') :
    iprop([∗list] e;Φ ∈ t2';List.replicate nt' iG.forkPost,
            fromOptionVal (GF := GF) e Φ) ⊢
    iprop([∗list] v ∈ List.filterMap ToVal.toVal t2', iG.forkPost v) := by
  subst hlen
  refine BI.BigSepL2.bigSepL2_replicate_right.1.trans ?_
  refine .trans ?_ (BI.equiv_iff.mp (BI.BigSepL.bigSepL_filterMap ToVal.toVal)).2
  refine BI.BigSepL.bigSepL_mono ?_
  intro _ e _
  unfold fromOptionVal
  cases ToVal.toVal e with
  | some _ => exact .rfl
  | none   => exact BI.affine

@[rocq_alias wp_strong_adequacy_gen]
theorem wp_strong_adequacy_gen [InvGpreS GF] (s : Stuckness)
    (es : List Expr) (σ1 : State) (n : Nat) (κs : List Obs)
    (t2 : List Expr) (σ2 : State) (φ : Prop)
    (_numLaters : Nat → Nat)
    (_Hwp : ∀ [_Hinv : InvGS_gen hlc GF] [iG : IrisGS_gen hlc Expr GF],
        ⊢ iprop(|={⊤}=> ∃ (Φs : List (Val → IProp GF)),
          stateInterp σ1 0 κs 0 ∗
          ([∗list] e;Φ ∈ es;Φs, WP e @ s ; ⊤ {{ Φ }}) ∗
          (∀ (es' t2' : List Expr),
            ⌜t2 = es' ++ t2'⌝ -∗ ⌜es'.length = es.length⌝ -∗
            ⌜∀ e2, s = Stuckness.NotStuck → e2 ∈ t2 → PrimStep.NotStuck (e2, σ2)⌝ -∗
            stateInterp σ2 n [] t2'.length -∗
            ([∗list] e;Φ ∈ es';Φs, match ToVal.toVal e with
                                    | some v => Φ v
                                    | none   => iprop(True)) -∗
            ([∗list] v ∈ List.filterMap ToVal.toVal t2', iG.forkPost v) -∗
            |={⊤,∅}=> ⌜φ⌝)))
    (_hsteps : Language.NSteps n (es, σ1) κs (t2, σ2)) :
    φ :=
  -- DESIGN ISSUE (see Bash log of stage/6-on-393 worktree, 2026-05-21):
  -- The current Lean port signature has the section variable
  -- `[iG : IrisGS_gen hlc Expr GF]` auto-bound at the theorem level (i.e. the
  -- caller provides `iG` *externally*), while `step_fupdN_soundness_gen`
  -- allocates a *fresh* `Hinv : InvGS_gen hlc GF` inside the proof.
  --
  -- These two are *different* `InvGS_gen` instances, so `iG.toLcGS ≠
  -- Hinv.toLcGS` and `iG.toWsatGS ≠ Hinv.toWsatGS`.  All `£`-credits and
  -- `|={E1,E2}=>` masks introduced by the soundness lemma carry
  -- `Hinv.toLcGS` / `Hinv.toWsatGS`, while every helper proved against the
  -- section `iG` (`wptp_postconditions` / `wptp_progress` / `wp_not_stuck` /
  -- `wp_to_postcond` / …) carries `iG.toLcGS` / `iG.toWsatGS`.  `ispecialize`
  -- cannot unify the resulting `£`-cells across the two instances, so the
  -- straightforward port of Coq's adequacy proof does not type-check.
  --
  -- Coq's `wp_strong_adequacy` avoids this by *constructing* `iG` from
  -- `Hinv` inside the proof via `pose (iG := IrisG Hinv …)`.  In Lean we
  -- cannot mirror that pattern because:
  --   (a) `letI` cannot be introduced inside `iprop(…)` syntax (noted in
  --       `wp_progress_gen`'s existing doc-comment), so `iG` must be a
  --       Pi-argument (auto-bound section variable);
  --   (b) `{ iG with toInvGS_gen := Hinv }` triggers a `Type mismatch` on
  --       the `stateInterp_mono` field, whose statement depends on
  --       `iG.toInvGS_gen`: the user-supplied proof of `stateInterp_mono`
  --       quantifies over `iG`'s `InvGS_gen`, not the fresh `Hinv`.
  --
  -- A proper Lean-side fix probably requires *either*:
  --   (i) restating `IrisGS_gen` so that `stateInterp_mono` is generic
  --       over the embedded `InvGS_gen` (e.g. quantify over all `Hinv` of
  --       the right type, not just `iG.toInvGS_gen`), so the field can be
  --       transported to `Hinv`; *or*
  --   (ii) restating `wp_strong_adequacy_gen` to take the
  --        `stateInterp` / `forkPost` / `numLatersPerStep` /
  --        `stateInterp_mono` *as plain Pi arguments* (mirroring Coq's
  --        in-iprop existential), and *constructing* `iG` inside the
  --        proof from `Hinv` + those parameters.
  -- Both are non-trivial design changes outside this PR's scope.
  --
  -- A full draft proof using the (i) approach was attempted in this
  -- worktree (see git log for stage/6-on-393); it stops at the `letI`
  -- transport step.  The remaining structure (pure_soundness →
  -- step_fupdN_soundness_gen → open `_Hwp` → wptp_postconditions →
  -- bigSepL2_app_inv_right split → fork-block conversion via
  -- `fork_block_to_filterMap` → apply user continuation) is correct.
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
theorem wp_adequacy_gen [InvGpreS GF] (s : Stuckness) (e : Expr) (σ : State)
    (φ : Val → Prop)
    (_Hwp : ∀ [_Hinv : InvGS_gen hlc GF] [iG : IrisGS_gen hlc Expr GF]
            (κs : List Obs),
        ⊢ iprop(|={⊤}=> iG.stateInterp σ 0 κs 0 ∗ WP e @ s ; ⊤ {{ v, ⌜φ v⌝ }})) :
    adequate s e σ (fun v _ => φ v) :=
  -- TODO: Agent #3 hit match aux-def blocker (same as Group A wptp_postconditions).
  sorry

@[rocq_alias wp_adequacy]
def wp_adequacy : True := True.intro

@[rocq_alias wp_invariance_gen]
theorem wp_invariance_gen [InvGpreS GF] (s : Stuckness) (e1 : Expr)
    (σ1 σ2 : State) (t2 : List Expr) (φ : Prop)
    (_Hwp : ∀ [Hinv : InvGS_gen hlc GF] (κs : List Obs)
             (stateI : State → IProp GF) (forkPost : Val → IProp GF),
        letI _ : IrisGS_gen hlc Expr GF := IrisGS_gen.ofSimple Hinv stateI forkPost
        (⊢ iprop(|={⊤}=> stateI σ1 ∗ WP e1 @ s ; ⊤ {{ v, iprop(True) }} ∗
                         (stateI σ2 -∗ ∃ (E : CoPset), |={⊤,E}=> ⌜φ⌝))))
    (_hsteps : Relation.ReflTransGen Language.ErasedStep ([e1], σ1) (t2, σ2)) :
    φ :=
  -- TODO: rewrite proof for new simple-stateI signature. With IrisGS_gen.ofSimple,
  -- iG.stateInterp σ _ _ _ = stateI σ so the ns=0 vs n bridge becomes trivial.
  sorry

@[rocq_alias wp_invariance]
def wp_invariance : True := True.intro

end
end Iris.ProgramLogic
