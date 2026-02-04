/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.Adequate
import Iris.ProgramLogic.Adequacy.WptpHelpersC

/-! # Adequacy: Strong Adequacy

Reference: `iris/program_logic/adequacy.v`

This file contains the main strong adequacy theorem.
-/

namespace Iris.ProgramLogic

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

variable {Λ : Language}
variable [inst : IrisGS Λ GF]

/-! ## Helper: Strip outer fupd from step_fupdN -/

omit [FiniteMapLaws Positive M] inst in
/-- Strip an outer `fupd` from a `step_fupdN` chain whose payload
is already a `fupd`. Uses `fupd_trans` in both the zero and successor cases. -/
theorem fupd_step_fupdN_fupd {W : WsatGS GF} (n : Nat) (P : IProp GF) :
    uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
      (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty P)) ⊢
    step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
      (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty P) := by
  cases n with
  | zero =>
      -- step_fupdN 0 Q = Q, so fupd univ univ (fupd univ empty P) ⊢ fupd univ empty P
      exact Iris.BaseLogic.fupd_trans (W := W) (M := M) (F := F)
        (E1 := Iris.Set.univ) (E2 := Iris.Set.univ) (E3 := maskEmpty) (P := P)
  | succ n =>
      -- step_fupdN (n+1) Q = fupd(later(fupd(step_fupdN n Q))), so
      -- fupd(fupd(later(...))) ⊢ fupd(later(...)) by fupd_trans
      exact Iris.BaseLogic.fupd_trans (W := W) (M := M) (F := F)
        (E1 := Iris.Set.univ) (E2 := Iris.Set.univ) (E3 := Iris.Set.univ)
        (P := BIBase.later
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
              (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty P))))

/-! ## Strong Adequacy -/

section StrongAdequacy

variable (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (n : Nat)
variable (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)

/-- Apply the adequacy post-condition to produce a fancy update to `φ`.
Coq: part of `wp_strong_adequacy` in `adequacy.v`. -/
theorem adequacy_post_apply {W : WsatGS GF}
    (Φs : List (Λ.val → IProp GF))
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hlen_init : es.length = Φs.length) :
    adequacy_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  -- discharge the continuation using the progress lemma
  let cont := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)
  let post := wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    s t2 Φs σ2 n [] 0
  have hns :=
    wp_progress_from_strong (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp hsteps
  have happly :=
    wptp_post_apply (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es) (t2 := t2) (Φs := Φs)
      (σ2 := σ2) (n := n) (φ := φ) hlen_init hns
  exact (sep_comm (PROP := IProp GF) (P := post) (Q := cont)).1.trans happly

/-- Lift the adequacy pre-condition to a `step_fupdN` chain.
Coq: part of `wp_strong_adequacy` in `adequacy.v`. -/
theorem adequacy_pre_to_step_fupd {W : WsatGS GF}
    (Φs : List (Λ.val → IProp GF))
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hlen_init : es.length = Φs.length) :
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) := by
  -- preserve the pool and apply the continuation under `step_fupdN`
  have happly :=
    adequacy_post_apply (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es) (σ1 := σ1) (n := n) (κs := κs)
      (t2 := t2) (σ2 := σ2) (φ := φ) (Φs := Φs) Hwp hsteps hlen_init
  have hmono := step_fupdN_mono (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n happly
  exact (wptp_preservation_frame (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (es := es) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) hsteps).trans hmono

/-- Push the adequacy invariant through preservation to obtain
a `step_fupdN` chain for every world.
Coq: part of `wp_strong_adequacy` in `adequacy.v`. -/
theorem wp_strong_adequacy_step
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) := by
  intro W -- push the adequacy invariant through preservation
  -- Step 1: show adequacy_inv ⊢ step_fupdN n (fupd (pure φ))
  have h_inv :
      adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) := by
    refine exists_elim ?_; intro Φs
    have hlen :=
      wptp_len_from_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (Φs := Φs) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)
    refine pure_elim (PROP := IProp GF)
      (φ := es.length = Φs.length) hlen ?_
    intro hlen_init
    exact adequacy_pre_to_step_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs)
      (φ := φ) Hwp hsteps hlen_init
  -- Step 2: lift through fupd_mono and strip via fupd_trans
  have h_fupd :=
    Iris.BaseLogic.fupd_mono (W := W) (M := M) (F := F)
      (E1 := Iris.Set.univ) (E2 := Iris.Set.univ) h_inv
  have h_strip :=
    fupd_step_fupdN_fupd (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (n := n) (P := BIBase.pure φ)
  exact (Hwp W).trans (h_fupd.trans h_strip)

end StrongAdequacy

omit inst in
/-- Helper: `n = 0` case for `wp_strong_adequacy_finish`. -/
theorem wp_strong_adequacy_finish_zero (φ : Prop)
    (hstep : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) 0
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))) :
    φ := by
  -- discharge the single fupd and apply pure soundness
  haveI : Plain (BIBase.pure (PROP := IProp GF) φ) :=
    ⟨(Iris.BI.plainly_pure (PROP := IProp GF) (φ := φ)).mpr⟩
  have hplain :
      ∀ W : WsatGS GF,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
    intro W
    simpa [step_fupdN] using (hstep W)
  have htrue :
      (True : IProp GF) ⊢ (BIBase.pure φ) :=
    (true_emp (PROP := IProp GF)).1.trans <|
      fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
        (E1 := Iris.Set.univ) (E2 := maskEmpty) (P := BIBase.pure φ)
        (h := hplain)
  exact UPred.pure_soundness (P := φ) htrue

omit inst in
/-- Helper: `n = n+1` case for `wp_strong_adequacy_finish`. -/
theorem wp_strong_adequacy_finish_succ (n : Nat) (φ : Prop)
    (hstep : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1)
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))) :
    φ := by
  -- strip the trailing fupd and apply step-fupd soundness
  haveI : Plain (BIBase.pure (PROP := IProp GF) φ) :=
    ⟨(Iris.BI.plainly_pure (PROP := IProp GF) (φ := φ)).mpr⟩
  have houter :
      ∀ W : WsatGS GF,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1)
              (BIBase.pure φ)) := by
    intro W
    have hplainW :
        (BIBase.emp : IProp GF) ⊢
          step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1)
            (BIBase.pure φ) :=
      (hstep W).trans (step_fupdN_strip_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
        (W := W) (n := n) (P := BIBase.pure φ))
    exact hplainW.trans (fupd_intro (W := W) (M := M) (F := F)
      (E := Iris.Set.univ)
      (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F)
        (W := W) (n + 1) (BIBase.pure φ)))
  have hplain :
      (BIBase.emp : IProp GF) ⊢ BIBase.pure φ :=
    step_fupdN_soundness (Λ := Λ) (GF := GF) (M := M) (F := F)
      (P := BIBase.pure φ) (n := n + 1) (h := houter)
  have htrue :
      (True : IProp GF) ⊢ (BIBase.pure φ) :=
    (true_emp (PROP := IProp GF)).1.trans hplain
  exact UPred.pure_soundness (P := φ) htrue

omit inst in
/-- Helper: conclude strong adequacy from the step-indexed soundness chain. -/
theorem wp_strong_adequacy_finish (n : Nat) (φ : Prop)
    (hstep : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))) :
    φ := by
  -- split on `n` and dispatch to the specialized helpers
  cases n with
  | zero =>
      exact wp_strong_adequacy_finish_zero (Λ := Λ) (GF := GF) (M := M) (F := F)
        (φ := φ) hstep
  | succ n =>
      exact wp_strong_adequacy_finish_succ (Λ := Λ) (GF := GF) (M := M) (F := F)
        (n := n) (φ := φ) hstep

/-- The main strong adequacy theorem of Iris.
Given an Iris proof of the weakest precondition for a thread pool,
any property `φ` that follows from the postconditions holds at the
meta-level after `n` steps of execution.
Coq: `wp_strong_adequacy` in `adequacy.v`. -/
theorem wp_strong_adequacy (s : Stuckness)
    (es : List Λ.expr) (σ1 : Λ.state) (n : Nat)
    (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    φ :=
  by
    -- strip the step-indexed update and conclude
    have hstep :=
      wp_strong_adequacy_step (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (σ1 := σ1) (n := n) (κs := κs)
        (t2 := t2) (σ2 := σ2) (φ := φ) Hwp hsteps
    exact wp_strong_adequacy_finish (Λ := Λ) (GF := GF) (M := M) (F := F)
      (n := n) (φ := φ) hstep


end Iris.ProgramLogic
