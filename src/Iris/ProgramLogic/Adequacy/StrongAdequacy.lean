/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.Adequate

/-! # Adequacy: Strong Adequacy

Reference: `iris/program_logic/adequacy.v`

This file contains the main strong adequacy theorem.
-/

namespace Iris.ProgramLogic

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [DecidableEq Positive]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

variable {Λ : Language}
variable [inst : IrisGS Λ GF]
variable {W : WsatGS GF}
/-! ## Strong Adequacy -/

section StrongAdequacy

variable (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (n : Nat)
variable (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)

noncomputable abbrev adq_inv : IProp GF :=
  -- packaged adequacy invariant for the current run
  adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)

theorem adequacy_post_apply
    (Φs : List (Λ.val → IProp GF))
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ adq_inv)
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hlen_init : es.length = Φs.length) :
    adequacy_post (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  -- discharge the continuation using the progress lemma
  let cont := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)
  let post := wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs σ2 n [] 0
  have hns :=
    wp_progress_from_strong (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp hsteps
  have happly :=
    wptp_post_apply (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (Φs := Φs)
      (σ2 := σ2) (n := n) (φ := φ) (hcont := cont) hlen_init hns
  exact (sep_comm (PROP := IProp GF) (P := post) (Q := cont)).1.trans happly

theorem adequacy_pre_to_step_fupd
    (Φs : List (Λ.val → IProp GF))
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ adq_inv)
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hlen_init : es.length = Φs.length) :
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) := by
  -- preserve the pool and apply the continuation under `step_fupdN`
  have happly :=
    adequacy_post_apply (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs)
      (φ := φ) Hwp hsteps hlen_init
  have hmono := step_fupdN_mono (Λ := Λ) (GF := GF) (M := M) (F := F) n happly
  exact (wptp_preservation_frame (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) hsteps).trans hmono

theorem wp_strong_adequacy_step
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ adq_inv)
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) := by
  intro W -- push the adequacy invariant through preservation
  refine (Hwp W).trans ?_
  refine fupd_mono (W := W)
    (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := adq_inv)
    (Q := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
      (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))) ?_
  refine exists_elim ?_; intro Φs
  have hlen :=
    wptp_len_from_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (Φs := Φs) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)
  refine pure_elim (PROP := IProp GF)
    (φ := es.length = Φs.length) hlen ?_
  intro hlen_init
  exact adequacy_pre_to_step_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs)
    (φ := φ) Hwp hsteps hlen_init

end StrongAdequacy

/-- Helper: conclude strong adequacy from the step-indexed soundness chain. -/
theorem wp_strong_adequacy_finish (n : Nat) (φ : Prop)
    (hstep : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))) :
    φ := by
  -- peel off `step_fupdN` and `fupd`, then use pure soundness
  have hplain :
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) :=
    step_fupdN_soundness (Λ := Λ) (GF := GF) (M := M) (F := F)
      (P := uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))
      (n := n) (h := hstep)
  have htrue :
      (True : IProp GF) ⊢ (BIBase.pure φ) :=
    (true_emp (PROP := IProp GF)).1.trans <|
      fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
        (E1 := Iris.Set.univ) (E2 := maskEmpty) (P := BIBase.pure φ)
        (h := fun _ => hplain)
  exact UPred.pure_soundness (P := φ) htrue

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
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
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
