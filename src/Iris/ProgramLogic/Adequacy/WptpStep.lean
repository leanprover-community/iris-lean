/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.WpStep

/-! # Adequacy: Thread Pool Step

Reference: `iris/program_logic/adequacy.v`

This file packages the step-preservation lemmas for thread pools.
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

/-! ## Wptp Step Helpers -/

noncomputable abbrev wptp_step_post_body
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- post-step body before rebuilding `wptp`
  BIBase.sep
    (BIBase.later
      (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
        (BIBase.sep
          (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
          (big_sepL (fun _ ef =>
            wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t2 Φs (t1.length + 1)))

noncomputable abbrev wptp_step_post_target
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- rebuilt `wptp` after the step
  BIBase.later
    (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
        (t1 ++ e2 :: t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post)))

noncomputable abbrev wptp_step_split_src
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    IProp GF :=
  -- pool state paired with the full `wptp` body
  BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
      s (t1 ++ e1 :: t2) Φs 0)

noncomputable abbrev wptp_step_split_mid
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    IProp GF :=
  -- `wptp` body with the focused thread separated
  BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
      (BIBase.sep
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs (t1.length + 1))))

noncomputable abbrev wptp_step_split_tgt
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    IProp GF :=
  -- `wptp` body reordered with the focused WP next to the state
  BIBase.sep
    (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ))
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t2 Φs (t1.length + 1)))

theorem wptp_step_split_body
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_step_split_src (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      wptp_step_split_mid (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) := by
  -- split the middle element inside the `big_sepL`
  have hsplit :=
    (wptp_body_at_middle (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (t1 := t1) (t2 := t2) (e := e1) (Φs := Φs) (k := 0)
      (Φ := Φ) (by simpa [Nat.zero_add] using hget)).1
  let P :=
    wptp_step_split_src (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
      (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
  let Q :=
    wptp_step_split_mid (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
      (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
  have hbody :
      P ⊢ Q :=
    sep_mono (PROP := IProp GF) .rfl hsplit
  simpa [P, Q] using hbody

theorem wptp_step_split_reorder
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    wptp_step_split_mid (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      wptp_step_split_tgt (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) := by
  -- reassociate and swap the middle elements
  have hassoc := (sep_assoc
    (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
    (R := BIBase.sep (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t2 Φs (t1.length + 1)))).2
  have hswap := (sep_sep_sep_comm
    (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
    (R := wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
    (S := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
      s t2 Φs (t1.length + 1))).1
  exact hassoc.trans hswap

theorem wptp_step_split
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_step_split_src (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      wptp_step_split_tgt (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) := by
  -- split the middle element, then reorder the `sep` chain
  have hbody := wptp_step_split_body (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (e1 := e1)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) hget
  have hreorder := wptp_step_split_reorder (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (e1 := e1)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
  exact hbody.trans hreorder

theorem wptp_step_apply
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    BIBase.sep
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
          (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ))
        (BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 Φs (t1.length + 1))) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_post_body (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
          (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) := by
  -- step the focused thread and frame the remaining pool
  let X :=
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (BIBase.sep
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))
  have hwp := adq_wp_step (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
    (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ) hstep
  exact (sep_mono (PROP := IProp GF) hwp .rfl).trans
    (fupd_frame_r (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.later X)
      (Q := BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs (t1.length + 1))))

theorem wptp_step_frame
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s (t1 ++ e1 :: t2) Φs 0) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_post_target (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
          (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) := by
  -- split the middle thread, step it, then rebuild the pool
  have hsplit := wptp_step_split (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
    (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) hget
  have happly := wptp_step_apply (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns)
    (κ := κ) (κs := κs) (nt := nt) hstep
  have hpost := wptp_step_post (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) hlen hget
  let P := wptp_step_post_body (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)
  let Q := wptp_step_post_target (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)
  have hmono :=
    fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := P) (Q := Q) hpost
  exact hsplit.trans (happly.trans hmono)

/-! ## Thread Pool Step -/

/-- A step of the thread pool preserves the thread pool WP.
Coq: `wptp_step` in `adequacy.v`. -/
theorem wptp_step_len_false (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hlen : es1.length ≠ Φs.length) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es1 Φs) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
            s es2 Φs σ2 (ns + 1) κs nt)) := by
  -- discharge the inconsistent-length case via pure elimination
  let Q :=
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es1 Φs)
  have hlenP : Q ⊢ BIBase.pure (es1.length = Φs.length) :=
    (sep_elim_r (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (Q := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es1 Φs)).trans
      (wptp_length (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (es := es1) (Φs := Φs))
  have hkill : es1.length = Φs.length → Q ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
          s es2 Φs σ2 (ns + 1) κs nt)) := by
    intro h; exact (False.elim (hlen h))
  exact pure_elim (φ := es1.length = Φs.length) hlenP hkill

/-- Helper: step a focused thread starting from a full `wptp`. -/
theorem wptp_step_len_true_frame
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (t1 ++ [e1] ++ t2) Φs) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (t1 ++ [e2] ++ t2 ++ efs)
              (Φs ++ List.replicate efs.length fork_post)))) := by
  -- open `wptp`, apply the frame rule, then rewrite list structure
  have hbody := wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := t1 ++ e1 :: t2) (Φs := Φs)
  have hframe := wptp_step_frame (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns)
    (κ := κ) (κs := κs) (nt := nt) hstep hlen hget
  have hmain := (sep_mono (PROP := IProp GF) .rfl hbody).trans hframe
  simpa [List.singleton_append, List.append_assoc] using hmain

/-- Helper: package a `wptp_post` existential under `▷`. -/
theorem wptp_post_later_intro
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt nt' : Nat) :
    BIBase.later
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ ns κs (nt' + nt))
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es
            (Φs ++ List.replicate nt' fork_post))) ⊢
      BIBase.later
        (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
          s es Φs σ ns κs nt) := by
  -- introduce the existential fork count under the `later`
  refine later_mono ?_
  refine exists_intro' (a := nt') ?_
  simpa [Nat.add_comm] using (.rfl : _ ⊢ _)

theorem wptp_step_len_true (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hstep : step (Λ := Λ) (es1, σ1) κ (es2, σ2))
    (hlen : es1.length = Φs.length) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es1 Φs) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
            s es2 Φs σ2 (ns + 1) κs nt)) := by
  -- focus the stepping thread, then rebuild the pool and add the existential
  classical
  cases hstep with
  | step_atomic e1 σ1' e2 σ2' efs t1 t2 _ hprim =>
      have hlen' : Φs.length = t1.length + t2.length + 1 := by
        simpa [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen.symm
      rcases wptp_lookup_middle (t1 := t1) (t2 := t2) (Φs := Φs) hlen' with ⟨Φ, hget⟩
      have hmain := wptp_step_len_true_frame (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
        (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns)
        (κ := κ) (κs := κs) (nt := nt) hprim hlen' hget
      have hpost :=
        wptp_post_later_intro (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := t1 ++ [e2] ++ t2 ++ efs) (Φs := Φs)
          (σ := σ2) (ns := ns + 1) (κs := κs) (nt := nt) (nt' := efs.length)
      exact hmain.trans <|
        fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later
            (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
              (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
                (t1 ++ [e2] ++ t2 ++ efs)
                (Φs ++ List.replicate efs.length fork_post))))
          (Q := BIBase.later
            (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
              s (t1 ++ [e2] ++ t2 ++ efs) Φs σ2 (ns + 1) κs nt)) hpost

theorem wptp_step' (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hstep : step (es1, σ1) κ (es2, σ2)) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (M := M) (F := F) (Λ := Λ) s es1 Φs)
    ⊢ uPred_fupd (M := M) (F := F) W
        Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
            s es2 Φs σ2 (ns + 1) κs nt)) := by
  -- split on length consistency, then dispatch to the appropriate lemma
  classical
  by_cases hlen : es1.length = Φs.length
  · simpa [state_interp] using
      wptp_step_len_true (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es1 := es1) (es2 := es2) (κ := κ) (κs := κs)
        (σ1 := σ1) (ns := ns) (σ2 := σ2) (nt := nt)
        (Φs := Φs) hstep hlen
  · simpa [state_interp] using
      wptp_step_len_false (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es1 := es1) (es2 := es2) (κ := κ) (κs := κs)
        (σ1 := σ1) (ns := ns) (σ2 := σ2) (nt := nt)
        (Φs := Φs) hlen


end Iris.ProgramLogic
