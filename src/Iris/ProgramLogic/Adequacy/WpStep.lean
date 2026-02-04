/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.FUpd

/-! # Adequacy: WP Step Helpers

Reference: `iris/program_logic/adequacy.v`

This file proves the single-step preservation lemma for WP and the
auxiliary step continuations used in the thread-pool proof.
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
/-! ## WP Step Helpers -/

noncomputable abbrev wp_step_cont (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (κ : List Λ.observation) (Φ : Λ.val → IProp GF)
    (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- the recursive continuation of the step case in `wp_pre`
  BIBase.forall fun e2 : Λ.expr =>
    BIBase.forall fun σ2 : Λ.state =>
      BIBase.forall fun efs : List Λ.expr =>
        BIBase.wand (BIBase.pure (Λ.prim_step e1 σ1 κ e2 σ2 efs)) <|
          fupd' (W := W) (M := M) (F := F) maskEmpty Iris.Set.univ <|
            BIBase.later <|
              BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
                (BIBase.sep
                  (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
                (big_sepL (fun _ ef =>
                    wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))

noncomputable abbrev adq_wp_step_post
    (s : Stuckness) (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr)
    (ns : Nat) (κs : List Λ.observation) (nt : Nat) (Φ : Λ.val → IProp GF) : IProp GF :=
  -- post-state bundle after the primitive step
  BIBase.later <|
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (BIBase.sep
        (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (big_sepL (fun _ ef =>
          wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))

noncomputable abbrev adq_wp_step_pre_prop
    (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (Φ : Λ.val → IProp GF) : IProp GF :=
  -- precondition: state interpretation and focused WP
  BIBase.sep
    (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)

noncomputable abbrev adq_wp_step_cont_prop
    (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (Φ : Λ.val → IProp GF) : IProp GF :=
  -- precondition for the step continuation
  BIBase.sep (BIBase.pure (stuckness_pred s e1 σ1))
    (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
      (ns := ns) (κs := κs) (nt := nt))

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem adq_wp_step_pre (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (Φ : Λ.val → IProp GF) (hv : Λ.to_val e1 = none) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
    ⊢ fupd' (W := W) (M := M) (F := F) Iris.Set.univ maskEmpty
        (BIBase.sep (BIBase.pure (stuckness_pred s e1 σ1))
          (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
            (ns := ns) (κs := κs) (nt := nt))) := by
  -- unfold the WP and specialize the step case
  have hwp :
      wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ ⊢
        wp_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s
          (wp (W := W) (M := M) (F := F) (Λ := Λ) s) Iris.Set.univ e1 Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (E := Iris.Set.univ) (e := e1) (Φ := Φ)).1
  refine (sep_mono_r hwp).trans ?_
  -- specialize the quantified state parameters, then apply the wand
  simp [wp_pre, hv, wp_pre_step, wp_step_cont]
  refine (sep_mono_r ?_).trans (wand_elim_r (PROP := IProp GF))
  refine (forall_elim (PROP := IProp GF) (Ψ := fun σ => _) σ1).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun ns => _) ns).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun κ => _) κ).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun κs => _) κs).trans ?_
  exact (forall_elim (PROP := IProp GF) (Ψ := fun nt => _) nt)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wp_step_cont_wand (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (nt : Nat)
    (Φ : Λ.val → IProp GF) :
    wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
        (ns := ns) (κs := κs) (nt := nt) ⊢
      BIBase.wand (BIBase.pure (Λ.prim_step e1 σ1 κ e2 σ2 efs))
        (fupd' (W := W) (M := M) (F := F) maskEmpty Iris.Set.univ
          (BIBase.later
            (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
              (BIBase.sep
                (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
                (big_sepL (fun _ ef =>
                  wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))) := by
  -- specialize the nested `∀` binders
  refine (forall_elim (PROP := IProp GF) (Ψ := fun e2 => _) e2).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun σ2 => _) σ2).trans ?_
  exact (forall_elim (PROP := IProp GF) (Ψ := fun efs => _) efs)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wp_step_cont_pure (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (nt : Nat)
    (Φ : Λ.val → IProp GF)
    (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
        (ns := ns) (κs := κs) (nt := nt) ⊢
      BIBase.sep (BIBase.pure (Λ.prim_step e1 σ1 κ e2 σ2 efs))
        (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
          (ns := ns) (κs := κs) (nt := nt)) := by
  -- insert the pure step using `True ∗ P`
  exact (true_sep_2 (PROP := IProp GF)
    (P := wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
      (ns := ns) (κs := κs) (nt := nt))).trans
    (sep_mono (pure_intro hstep) .rfl)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem adq_wp_step_cont (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (nt : Nat)
    (Φ : Λ.val → IProp GF)
    (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    BIBase.sep (BIBase.pure (stuckness_pred s e1 σ1))
      (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
        (ns := ns) (κs := κs) (nt := nt))
    ⊢ fupd' (W := W) (M := M) (F := F) maskEmpty Iris.Set.univ
        (adq_wp_step_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (e2 := e2) (σ2 := σ2) (efs := efs)
          (ns := ns) (κs := κs) (nt := nt) (Φ := Φ)) := by
  -- drop the stuckness predicate and apply the step continuation
  refine (sep_elim_r (P := BIBase.pure _) (Q := wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
    (ns := ns) (κs := κs) (nt := nt))).trans ?_
  have hwand := wp_step_cont_wand (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
    (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ)
  have hpure := wp_step_cont_pure (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
    (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ) hstep
  exact hpure.trans (sep_mono .rfl hwand) |>.trans (wand_elim_r (PROP := IProp GF))

/-! ## Single Step -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: lift the step continuation through the outer `fupd`. -/
theorem adq_wp_step_finish (P Q : IProp GF)
    (hcont : P ⊢ fupd' (W := W) (M := M) (F := F) maskEmpty Iris.Set.univ Q) :
    fupd' (W := W) (M := M) (F := F) Iris.Set.univ maskEmpty P ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ Q := by
  -- lift under `fupd` and compose the update masks
  exact (Iris.BaseLogic.fupd_mono (W := W)
    (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
    (P := P) (Q := fupd' (W := W) (M := M) (F := F) maskEmpty Iris.Set.univ Q) hcont).trans
    (Iris.BaseLogic.fupd_trans (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
      (E3 := Iris.Set.univ) (P := Q))

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- A single primitive step preserves the weakest precondition.
Given a step `e1 → e2` producing new threads `efs`, the state
interpretation and WP transfer to the post-state.
Coq: `wp_step` in `adequacy.v`. -/
theorem adq_wp_step (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state)
    (efs : List Λ.expr) (nt : Nat) (Φ : Λ.val → IProp GF)
    (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    adq_wp_step_pre_prop (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
        (nt := nt) (Φ := Φ) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (adq_wp_step_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (e2 := e2) (σ2 := σ2) (efs := efs)
          (ns := ns) (κs := κs) (nt := nt) (Φ := Φ)) :=
  by
    -- unfold the WP step case and apply the concrete primitive step
    have hv : Λ.to_val e1 = none := val_stuck (Λ := Λ) (e := e1) (σ := σ1) (κ := κ) (e' := e2) (σ' := σ2) (efs := efs) hstep
    have hpre := adq_wp_step_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) (Φ := Φ) hv
    have hcont := adq_wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
      (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ) hstep
    -- lift the continuation through the outer update and compose
    let P := adq_wp_step_cont_prop (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) (Φ := Φ)
    let Q := adq_wp_step_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e2 := e2) (σ2 := σ2) (efs := efs) (ns := ns) (κs := κs) (nt := nt) (Φ := Φ)
    exact hpre.trans (adq_wp_step_finish (P := P) (Q := Q) hcont)


end Iris.ProgramLogic
