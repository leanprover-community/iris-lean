/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.WptpStep

/-! # Adequacy: Preservation and Progress

Reference: `iris/program_logic/adequacy.v`

This file proves multi-step preservation, thread-pool progress, and the
not-stuck consequences for WP.
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
variable {W : WsatGS GF}
/-! ## Multi-Step Preservation -/

/-- Induction hypothesis shape for `wptp_preservation`. -/
abbrev WptpPreservationIH (s : Stuckness) (n : Nat) (κs' : List Λ.observation) : Prop :=
  ∀ {es1 es2 : List Λ.expr} {κs : List Λ.observation}
      {σ1 σ2 : Λ.state} {ns nt : Nat} {Φs : List (Λ.val → IProp GF)},
    nsteps (Λ := Λ) n (es1, σ1) κs (es2, σ2) →
      BIBase.sep
        (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κs ++ κs') nt)
        (wptp (W := W) (M := M) (F := F) (Λ := Λ) s es1 Φs) ⊢
      step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (wptp_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
          s es2 Φs σ2 (n + ns) κs' nt)

/-- Helper: lift the induction hypothesis under `▷` and merge forked posts. -/
theorem wptp_preservation_later
    (s : Stuckness) (n : Nat) (κs_tail κs' : List Λ.observation)
    (es_mid es2 : List Λ.expr) (σ_mid σ2 : Λ.state)
    (ns nt : Nat) (Φs : List (Λ.val → IProp GF))
    (ih : WptpPreservationIH (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s n κs')
    (hrest : nsteps (Λ := Λ) n (es_mid, σ_mid) κs_tail (es2, σ2)) :
    BIBase.later
        (wptp_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
          s es_mid Φs σ_mid (ns + 1) (κs_tail ++ κs') nt) ⊢
      BIBase.later
        (step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
          (wptp_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
            s es2 Φs σ2 (n + (ns + 1)) κs' nt)) := by
  -- open the existential, apply the IH, then merge forked suffixes
  refine later_mono ?_
  refine exists_elim ?_
  intro nt'
  have ih' :=
    ih (es1 := es_mid) (es2 := es2) (κs := κs_tail)
      (σ1 := σ_mid) (σ2 := σ2)
      (Φs := Φs ++ List.replicate nt' fork_post)
      (ns := ns + 1) (nt := nt + nt') hrest
  have hmerge :=
    wptp_post_merge (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es2) (Φs := Φs) (σ := σ2)
      (ns := n + (ns + 1)) (κs := κs') (nt := nt) (nt' := nt')
  exact (by
    simpa [List.append_assoc, Nat.add_assoc] using
      ih'.trans (step_fupdN_mono (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n hmerge))

/-- Helper: finish the successor step of `step_fupdN`. -/
theorem step_fupdN_succ_finish (P mid X : IProp GF) (n : Nat)
    (hstep' :
      P ⊢ fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later mid))
    (hmono :
      BIBase.later mid ⊢
        BIBase.later
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n X))) :
    P ⊢ step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) (n + 1) X := by
  -- push the refinement under the outer `fupd`
  have hmono' :=
    Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.later mid)
      (Q := BIBase.later
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n X))) hmono
  simpa [step_fupdN, Iris.step_fupdN, fupd'] using hstep'.trans hmono'

/-- Helper: precondition for preservation statements. -/
noncomputable abbrev wptp_preservation_pre
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ : Λ.state) (ns : Nat) (κs κs' : List Λ.observation) (nt : Nat) : IProp GF :=
  -- state interpretation with the pool WP
  BIBase.sep
    (IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns (κs ++ κs') nt)
    (wptp (W := W) (M := M) (F := F) (Λ := Λ) s es Φs)

/-- Helper: postcondition for preservation statements. -/
noncomputable abbrev wptp_preservation_post
    (s : Stuckness) (n : Nat) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ : Λ.state) (ns : Nat) (κs' : List Λ.observation) (nt : Nat) : IProp GF :=
  -- `step_fupdN` wrapped `wptp_post`
  step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
    (wptp_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
      s es Φs σ (n + ns) κs' nt)

/-- Helper: single-step `fupd` for the successor case. -/
theorem wptp_preservation_succ_step
    (s : Stuckness) (κ κs_tail κs' : List Λ.observation)
    (es1 es_mid : List Λ.expr) (σ1 σ_mid : Λ.state)
    (ns nt : Nat) (Φs : List (Λ.val → IProp GF))
    (hstep : step (Λ := Λ) (es1, σ1) κ (es_mid, σ_mid)) :
    wptp_preservation_pre (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es1) (Φs := Φs) (σ := σ1) (ns := ns)
        (κs := κ ++ κs_tail) (κs' := κs') (nt := nt) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
            s es_mid Φs σ_mid (ns + 1) (κs_tail ++ κs') nt)) := by
  -- specialize `wptp_step'` and rewrite the trace shape
  simpa [wptp_preservation_pre, List.append_assoc] using
    wptp_step' (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es1 := es1) (es2 := es_mid) (κ := κ)
      (κs := κs_tail ++ κs') (σ1 := σ1) (ns := ns)
      (σ2 := σ_mid) (nt := nt) (Φs := Φs) hstep

/-- Helper: successor step of `wptp_preservation`. -/
theorem wptp_preservation_succ
    (s : Stuckness) (n : Nat) (κ κs_tail κs' : List Λ.observation)
    (es1 es_mid es2 : List Λ.expr) (σ1 σ_mid σ2 : Λ.state)
    (ns nt : Nat) (Φs : List (Λ.val → IProp GF))
    (ih : WptpPreservationIH (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s n κs')
    (hstep : step (Λ := Λ) (es1, σ1) κ (es_mid, σ_mid))
    (hrest : nsteps (Λ := Λ) n (es_mid, σ_mid) κs_tail (es2, σ2)) :
    wptp_preservation_pre (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es1) (Φs := Φs) (σ := σ1) (ns := ns)
        (κs := κ ++ κs_tail) (κs' := κs') (nt := nt) ⊢
      wptp_preservation_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (n := n + 1) (es := es2) (Φs := Φs) (σ := σ2)
        (ns := ns) (κs' := κs') (nt := nt) := by
  -- step once, then lift the induction hypothesis under `▷`
  have hstep' := wptp_preservation_succ_step (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (κ := κ) (κs_tail := κs_tail) (κs' := κs')
    (es1 := es1) (es_mid := es_mid) (σ1 := σ1) (σ_mid := σ_mid)
    (ns := ns) (nt := nt) (Φs := Φs) hstep
  have hlater :=
    wptp_preservation_later (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (n := n) (κs_tail := κs_tail) (κs' := κs')
      (es_mid := es_mid) (es2 := es2) (σ_mid := σ_mid) (σ2 := σ2)
      (ns := ns) (nt := nt) (Φs := Φs) (ih := ih) hrest
  have hintro :=
    fupd_intro (W := W) (GF := GF) (M := M) (F := F)
      (E := Iris.Set.univ)
      (P := step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (wptp_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
          s es2 Φs σ2 (n + (ns + 1)) κs' nt))
  have hmono :=
    hlater.trans (later_mono (PROP := IProp GF) hintro)
  simpa [wptp_preservation_post, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (step_fupdN_succ_finish (Λ := Λ) (GF := GF) (M := M) (F := F)
      (P := _) (mid := _) (X := _) (n := n) hstep' hmono)

/-- Multi-step preservation: after `n` steps, the thread pool WP
and state interpretation are preserved (modulo fupd and later).
Coq: `wptp_preservation` in `adequacy.v`. -/
theorem wptp_preservation (s : Stuckness) (n : Nat)
    (es1 es2 : List Λ.expr) (κs κs' : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hsteps : nsteps (Λ := Λ) n (es1, σ1) κs (es2, σ2)) :
    wptp_preservation_pre (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es1) (Φs := Φs) (σ := σ1) (ns := ns)
        (κs := κs) (κs' := κs') (nt := nt) ⊢
      wptp_preservation_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (n := n) (es := es2) (Φs := Φs) (σ := σ2)
        (ns := ns) (κs' := κs') (nt := nt) := by
  -- induct on the execution trace, generalizing `ns`/`nt`/`Φs`
  induction n generalizing es1 es2 κs σ1 σ2 Φs ns nt with
  | zero =>
      cases hsteps with
      | nsteps_refl ρ =>
          refine exists_intro' (a := 0) ?_
          simp [wptp_preservation_pre, wptp_preservation_post, step_fupdN, wptp_post,
            List.append_nil, Nat.add_comm, Nat.add_assoc]
  | succ n ih =>
      cases hsteps with
      | nsteps_l n' ρ1 ρ2 ρ3 κ κs_tail hstep hrest =>
          rcases ρ2 with ⟨es_mid, σ_mid⟩
          have ih' : WptpPreservationIH (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
              s n κs' := by
            -- unfold the pre/post abbreviations to match the IH shape
            intro es1 es2 κs σ1 σ2 ns nt Φs hsteps
            simpa [wptp_preservation_pre, wptp_preservation_post] using
              ih (es1 := es1) (es2 := es2) (κs := κs) (σ1 := σ1) (σ2 := σ2)
                (ns := ns) (nt := nt) (Φs := Φs) hsteps
          exact wptp_preservation_succ (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (n := n) (κ := κ) (κs_tail := κs_tail) (κs' := κs')
            (es1 := es1) (es_mid := es_mid) (es2 := es2)
            (σ1 := σ1) (σ_mid := σ_mid) (σ2 := σ2)
            (ns := ns) (nt := nt) (Φs := Φs) (ih := ih') hstep hrest

/-! ## Wptp Progress -/

/-- Helper: extract a single-thread WP from a thread pool. -/
theorem wptp_post_not_stuck_wp_of_get
    (t1 t2 : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF) (nt' : Nat)
    (hget : (Φs ++ List.replicate nt' fork_post)[t1.length]? = some Φ) :
    wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck
        (t1 ++ e2 :: t2) (Φs ++ List.replicate nt' fork_post) ⊢
      wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ := by
  -- peel `wptp` to the middle component and project the WP
  have hbody := wptp_body_of_wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := .notStuck) (es := t1 ++ e2 :: t2) (Φs := Φs ++ List.replicate nt' fork_post)
  have hmid :=
    (wptp_body_at_middle (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := .notStuck) (t1 := t1) (t2 := t2) (e := e2)
      (Φs := Φs ++ List.replicate nt' fork_post) (k := 0) (Φ := Φ)
      (by simpa [Nat.zero_add] using hget)).1
  have hsep := hbody.trans (by simpa using hmid)
  let A :=
    big_sepL (PROP := IProp GF)
      (wptp_body_at_fn (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        .notStuck (Φs ++ List.replicate nt' fork_post) 0) t1
  let C :=
    big_sepL (PROP := IProp GF)
      (wptp_body_at_fn (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        .notStuck (Φs ++ List.replicate nt' fork_post) (t1.length + 1)) t2
  have hsep' :
      wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck
          (t1 ++ e2 :: t2) (Φs ++ List.replicate nt' fork_post) ⊢
        BIBase.sep A
          (BIBase.sep
            (wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ) C) := by
    -- unfold `wptp_body_at` to align with `sep_elim`
    simpa [A, C, wptp_body_at_unfold] using hsep
  exact (hsep'.trans <|
    sep_elim_r (PROP := IProp GF) (P := A) (Q := BIBase.sep
      (wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ) C)).trans
    (sep_elim_l (PROP := IProp GF)
      (P := wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ)
      (Q := C))

/-! ## Not Stuck -/

/-- Helper: map reducibility to `not_stuck` in the step case. -/
theorem wp_not_stuck_step_mono (e : Λ.expr) (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) (Φ : Λ.val → IProp GF) :
    BIBase.sep (BIBase.pure (reducible e σ))
        (wp_step_cont (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := .notStuck) (e1 := e) (σ1 := σ) (κ := [])
          (Φ := Φ) (ns := ns) (κs := κs) (nt := nt)) ⊢
      BIBase.pure (not_stuck e σ) := by
  -- drop the continuation and lift reducibility into `not_stuck`
  exact (sep_elim_l (P := BIBase.pure (reducible e σ))
    (Q := wp_step_cont (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := .notStuck) (e1 := e) (σ1 := σ) (κ := [])
      (Φ := Φ) (ns := ns) (κs := κs) (nt := nt))).trans
    (pure_mono fun h => Or.inr h)

/-- Helper: WP not-stuck in the value case. -/
theorem wp_not_stuck_value (e : Λ.expr) (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) (Φ : Λ.val → IProp GF)
    (v : Λ.val) (hto : Λ.to_val e = some v) :
    BIBase.sep
        (IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt)
        (wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ)
      ⊢ uPred_fupd (M := M) (F := F) W
          Iris.Set.univ (fun _ => False) (BIBase.pure (not_stuck e σ)) := by
  -- discharge using pure introduction and `fupd` intro
  have hns : not_stuck e σ := Or.inl ⟨v, hto⟩
  have hpure :
      wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ ⊢
        BIBase.pure (not_stuck e σ) := pure_intro hns
  exact (sep_elim_r
    (P := IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt)
    (Q := wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ)).trans <|
    hpure.trans (fupd_intro_univ_empty (W := W) (GF := GF) (M := M) (F := F)
      (P := BIBase.pure (not_stuck e σ)))

/-- Helper: WP not-stuck in the non-value case. -/
theorem wp_not_stuck_step (e : Λ.expr) (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) (Φ : Λ.val → IProp GF)
    (hto : Λ.to_val e = none) :
    BIBase.sep
        (IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt)
        (wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ)
      ⊢ uPred_fupd (M := M) (F := F) W
          Iris.Set.univ (fun _ => False) (BIBase.pure (not_stuck e σ)) := by
  -- use the step case of the WP and map reducibility to not-stuck
  have hpre := adq_wp_step_pre (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := .notStuck) (e1 := e) (σ1 := σ) (ns := ns)
    (κ := []) (κs := κs) (nt := nt) (Φ := Φ) hto
  have hmono := wp_not_stuck_step_mono (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (e := e) (σ := σ) (ns := ns) (κs := κs) (nt := nt) (Φ := Φ)
  exact hpre.trans <|
    Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
      (P := BIBase.sep (BIBase.pure (reducible e σ))
        (wp_step_cont (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := .notStuck) (e1 := e) (σ1 := σ) (κ := [])
          (Φ := Φ) (ns := ns) (κs := κs) (nt := nt)))
      (Q := BIBase.pure (not_stuck e σ)) hmono

/-- WP at `NotStuck` stuckness implies the expression is not stuck.
Coq: `wp_not_stuck` in `adequacy.v`. -/
theorem wp_not_stuck' (e : Λ.expr) (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat)
    (Φ : Λ.val → IProp GF) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt)
      (wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ)
    ⊢ uPred_fupd (M := M) (F := F) W
        Iris.Set.univ (fun _ => False) (BIBase.pure (not_stuck e σ)) :=
  by
    -- split on the value case and use `adq_wp_step_pre` otherwise
    classical
    cases hto : Λ.to_val e with
    | some v =>
        exact wp_not_stuck_value (Λ := Λ) (GF := GF) (M := M) (F := F)
          (e := e) (σ := σ) (ns := ns) (κs := κs) (nt := nt)
          (Φ := Φ) (v := v) hto
    | none =>
        exact wp_not_stuck_step (Λ := Λ) (GF := GF) (M := M) (F := F)
          (e := e) (σ := σ) (ns := ns) (κs := κs) (nt := nt)
          (Φ := Φ) hto
/-- Helper: precondition for not-stuck extraction from `wptp`. -/
noncomputable abbrev wptp_post_not_stuck_pre
    (es2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt nt' : Nat) : IProp GF :=
  -- state interpretation paired with the extended thread pool
  BIBase.sep
    (state_interp (Λ := Λ) (GF := GF) σ2 ns κs (nt + nt'))
    (wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
      (Φs ++ List.replicate nt' fork_post))

/-- Helper: frame a WP with the state interpretation to derive not-stuck. -/
theorem wptp_post_not_stuck_frame
    (es2 : List Λ.expr) (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt nt' : Nat)
    (e2 : Λ.expr)
    (hwp :
      wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
          (Φs ++ List.replicate nt' fork_post) ⊢
        wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 ns κs (nt + nt'))
        (wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
          (Φs ++ List.replicate nt' fork_post)) ⊢
      uPred_fupd (M := M) (F := F) W
        Iris.Set.univ maskEmpty (BIBase.pure (not_stuck e2 σ2)) := by
  -- frame the WP and apply `wp_not_stuck'`
  have hframe :
      BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ2 ns κs (nt + nt'))
          (wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
            (Φs ++ List.replicate nt' fork_post)) ⊢
        BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ2 ns κs (nt + nt'))
          (wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ) :=
    sep_mono (PROP := IProp GF) .rfl hwp
  exact hframe.trans
    (wp_not_stuck' (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (e := e2) (σ := σ2) (ns := ns) (κs := κs) (nt := nt + nt') (Φ := Φ))

/-- Helper: the length-known branch of `wptp_post_not_stuck_aux`. -/
theorem wptp_post_not_stuck_aux_core
    (es2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt nt' : Nat)
    (e2 : Λ.expr) (hemem : e2 ∈ es2)
    (hlen' : es2.length = (Φs ++ List.replicate nt' fork_post).length) :
    wptp_post_not_stuck_pre (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        (es2 := es2) (Φs := Φs) (σ2 := σ2) (ns := ns) (κs := κs)
        (nt := nt) (nt' := nt') ⊢
      uPred_fupd (M := M) (F := F) W
        Iris.Set.univ maskEmpty (BIBase.pure (not_stuck e2 σ2)) := by
  -- split the list, locate the focused thread, then apply `wp_not_stuck'`
  rcases mem_split hemem with ⟨t1, t2, ht⟩
  have hlen_es : es2.length = t1.length + t2.length + 1 := by
    simpa [ht, List.length_append, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hlen'' : (Φs ++ List.replicate nt' fork_post).length = t1.length + t2.length + 1 :=
    hlen'.symm.trans hlen_es
  rcases wptp_lookup_middle (Λ := Λ) (GF := GF)
      (t1 := t1) (t2 := t2) (Φs := Φs ++ List.replicate nt' fork_post) hlen'' with ⟨Φ, hget⟩
  have hwp :
      wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
          (Φs ++ List.replicate nt' fork_post) ⊢
        wp (W := W) (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ := by
    simpa [ht] using
      (wptp_post_not_stuck_wp_of_get (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        (t1 := t1) (t2 := t2) (e2 := e2) (Φs := Φs) (Φ := Φ)
        (nt' := nt') hget)
  exact wptp_post_not_stuck_frame (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
    (es2 := es2) (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs)
    (nt := nt) (nt' := nt') (e2 := e2) hwp

/-- Helper: extract not-stuck from a concrete `wptp` instance. -/
theorem wptp_post_not_stuck_aux
    (es2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt nt' : Nat)
    (e2 : Λ.expr) (hemem : e2 ∈ es2) :
    wptp_post_not_stuck_pre (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        (es2 := es2) (Φs := Φs) (σ2 := σ2) (ns := ns) (κs := κs)
        (nt := nt) (nt' := nt') ⊢
      uPred_fupd (M := M) (F := F) W
        Iris.Set.univ maskEmpty (BIBase.pure (not_stuck e2 σ2)) := by
  -- derive the relevant WP and apply `wp_not_stuck'`
  have hlen :
      wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
          (Φs ++ List.replicate nt' fork_post) ⊢
        BIBase.pure (es2.length = (Φs ++ List.replicate nt' fork_post).length) :=
    wptp_length (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := .notStuck) (es := es2) (Φs := Φs ++ List.replicate nt' fork_post)
  refine (pure_elim (PROP := IProp GF)
    (φ := es2.length = (Φs ++ List.replicate nt' fork_post).length) ?_ ?_)
  · exact (sep_elim_r (P := state_interp (Λ := Λ) (GF := GF) σ2 ns κs (nt + nt'))
      (Q := wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
        (Φs ++ List.replicate nt' fork_post))).trans hlen
  · intro hlen'
    exact wptp_post_not_stuck_aux_core (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
      (es2 := es2) (Φs := Φs) (σ2 := σ2) (ns := ns) (κs := κs)
      (nt := nt) (nt' := nt') (e2 := e2) hemem hlen'

theorem wptp_post_not_stuck
    (es2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat)
    (e2 : Λ.expr) (hemem : e2 ∈ es2) :
    wptp_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
        .notStuck es2 Φs σ2 ns κs nt ⊢
      uPred_fupd (M := M) (F := F) W
        Iris.Set.univ maskEmpty (BIBase.pure (not_stuck e2 σ2)) := by
  -- open the existential and extract the WP for `e2`
  classical
  refine exists_elim ?_
  intro nt'
  exact wptp_post_not_stuck_aux (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
    (es2 := es2) (Φs := Φs) (σ2 := σ2) (ns := ns) (κs := κs)
    (nt := nt) (nt' := nt') (e2 := e2) hemem

theorem wptp_progress (n : Nat)
    (es1 es2 : List Λ.expr) (κs κs' : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF)) (e2 : Λ.expr)
    (hsteps : nsteps (Λ := Λ) n (es1, σ1) κs (es2, σ2)) (hemem : e2 ∈ es2) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κs ++ κs') nt)
      (wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es1 Φs) ⊢
    step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
      (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
        (BIBase.pure (not_stuck e2 σ2))) := by
  -- preserve the thread pool, then extract not-stuck for the chosen thread
  have hpres :=
    wptp_preservation (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := .notStuck) (n := n) (es1 := es1) (es2 := es2)
      (κs := κs) (κs' := κs') (σ1 := σ1) (ns := ns)
      (σ2 := σ2) (nt := nt) (Φs := Φs) hsteps
  have hmono :
      wptp_post (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
          .notStuck es2 Φs σ2 (n + ns) κs' nt ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
          (BIBase.pure (not_stuck e2 σ2)) :=
    wptp_post_not_stuck (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
      (es2 := es2) (Φs := Φs) (σ2 := σ2) (ns := n + ns)
      (κs := κs') (nt := nt) (e2 := e2) hemem
  exact hpres.trans (step_fupdN_mono (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n hmono)

/-- Helper: build the `step_fupdN` chain for `wp_progress`. -/
theorem wp_progress_fupd_elim (n : Nat)
    (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (e2 : Λ.expr)
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) (hemem : e2 ∈ t2) :
    (BIBase.«exists» (PROP := IProp GF) fun (Φs : List (Λ.val → IProp GF)) =>
        BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
          (wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es Φs)) ⊢
      step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
          (BIBase.pure (not_stuck e2 σ2))) := by
  -- pick the existential witness and apply `wptp_progress`
  refine exists_elim ?_
  intro Φs
  have hprogress :=
    wptp_progress (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (n := n) (es1 := es) (es2 := t2) (κs := κs) (κs' := [])
      (σ1 := σ1) (ns := 0) (σ2 := σ2) (nt := 0)
      (Φs := Φs) (e2 := e2) hsteps hemem
  -- normalize the empty trace suffix
  simpa [List.append_nil] using hprogress

/-- Helper: build the `step_fupdN` chain for `wp_progress`. -/
theorem wp_progress_fupd (n : Nat)
    (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (e2 : Λ.expr)
    (Hwp : ∀ W : WsatGS GF, (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
          BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
            (wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es Φs)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hemem : e2 ∈ t2) :
    ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
            (BIBase.pure (not_stuck e2 σ2)))) := by
  -- specialize the existential and apply `wptp_progress`
  intro W
  refine (Hwp W).trans ?_
  refine Iris.BaseLogic.fupd_mono (W := W)
    (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
      BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es Φs))
    (Q := step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
      (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
        (BIBase.pure (not_stuck e2 σ2)))) ?_
  exact wp_progress_fupd_elim
    (n := n) (es := es) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (e2 := e2) hsteps hemem

/-- Helper: `n = 0` case for `wp_progress_soundness_pure`. -/
theorem wp_progress_soundness_pure_zero (σ2 : Λ.state) (e2 : Λ.expr)
    (hmono : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) 0
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
              (BIBase.pure (not_stuck e2 σ2))))) :
    (True : IProp GF) ⊢ BIBase.pure (not_stuck e2 σ2) := by
  -- collapse the nested update, then apply soundness
  haveI : Plain (BIBase.pure (not_stuck e2 σ2)) :=
    -- pure propositions are plain via `■ ⌜φ⌝ ⊣⊢ ⌜φ⌝`
    ⟨(Iris.BI.plainly_pure (PROP := IProp GF) (φ := not_stuck e2 σ2)).mpr⟩
  have hplain :
      (BIBase.emp : IProp GF) ⊢ BIBase.pure (not_stuck e2 σ2) :=
    fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
      (E1 := Iris.Set.univ) (E2 := maskEmpty)
      (P := BIBase.pure (not_stuck e2 σ2)) (h := fun W => by
        have hmono0 :
            (BIBase.emp : IProp GF) ⊢
              uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
                (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
                  (BIBase.pure (not_stuck e2 σ2))) := by
          simpa [step_fupdN] using (hmono W)
        have htrans :=
          Iris.BaseLogic.fupd_trans (W := W)
            (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
            (E3 := maskEmpty) (P := BIBase.pure (not_stuck e2 σ2))
        exact hmono0.trans htrans)
  exact (true_emp (PROP := IProp GF)).1.trans hplain

/-- Helper: `n = n+1` case for `wp_progress_soundness_pure`. -/
theorem wp_progress_soundness_pure_succ (n : Nat) (σ2 : Λ.state) (e2 : Λ.expr)
    (hmono : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) (n + 1)
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
              (BIBase.pure (not_stuck e2 σ2))))) :
    (True : IProp GF) ⊢ BIBase.pure (not_stuck e2 σ2) := by
  -- strip the final fupd and apply step-fupd soundness
  haveI : Plain (BIBase.pure (not_stuck e2 σ2)) :=
    -- reuse the plainness of pure propositions
    ⟨(Iris.BI.plainly_pure (PROP := IProp GF) (φ := not_stuck e2 σ2)).mpr⟩
  have hstep :
      ∀ W : WsatGS GF,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1)
              (BIBase.pure (not_stuck e2 σ2))) := by
    intro W
    exact (hmono W).trans
      (fupd_step_fupdN_strip_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
        (W := W) (n := n) (P := BIBase.pure (not_stuck e2 σ2)))
  have hplain :
      (BIBase.emp : IProp GF) ⊢ BIBase.pure (not_stuck e2 σ2) :=
    step_fupdN_soundness (Λ := Λ) (GF := GF) (M := M) (F := F)
      (P := BIBase.pure (not_stuck e2 σ2)) (n := n + 1) (h := hstep)
  exact (true_emp (PROP := IProp GF)).1.trans hplain

/-- Helper: extract `not_stuck` from the `step_fupdN` chain. -/
theorem wp_progress_soundness_pure (n : Nat) (σ2 : Λ.state) (e2 : Λ.expr)
    (hmono : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
              (BIBase.pure (not_stuck e2 σ2))))) :
    (True : IProp GF) ⊢ BIBase.pure (not_stuck e2 σ2) := by
  -- split on `n` and delegate to the specialized helpers
  cases n with
  | zero =>
      exact wp_progress_soundness_pure_zero (Λ := Λ) (GF := GF) (M := M) (F := F)
        (σ2 := σ2) (e2 := e2) hmono
  | succ n =>
      exact wp_progress_soundness_pure_succ (Λ := Λ) (GF := GF) (M := M) (F := F)
        (n := n) (σ2 := σ2) (e2 := e2) hmono

/-- Helper: extract `not_stuck` from the `step_fupdN` chain. -/
theorem wp_progress_soundness (n : Nat) (σ2 : Λ.state) (e2 : Λ.expr)
    (hmono : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) n
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
              (BIBase.pure (not_stuck e2 σ2))))) :
    not_stuck e2 σ2 := by
  -- peel updates and apply pure soundness
  have htrue :=
    wp_progress_soundness_pure (Λ := Λ) (GF := GF) (M := M) (F := F)
      (n := n) (σ2 := σ2) (e2 := e2) hmono
  exact UPred.pure_soundness (P := not_stuck e2 σ2) htrue

theorem wp_progress (n : Nat)
    (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (e2 : Λ.expr)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.«exists» (PROP := IProp GF) fun (Φs : List (Λ.val → IProp GF)) =>
            BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
              (wptp (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es Φs)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hemem : e2 ∈ t2) :
    not_stuck e2 σ2 := by
  -- run preservation and soundness to extract not-stuck at the meta-level
  have hmono :=
    wp_progress_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
      (n := n) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (e2 := e2) Hwp hsteps hemem
  exact wp_progress_soundness (Λ := Λ) (GF := GF) (M := M) (F := F)
    (n := n) (σ2 := σ2) (e2 := e2) hmono



end Iris.ProgramLogic
