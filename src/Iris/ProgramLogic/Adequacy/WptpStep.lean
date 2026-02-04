/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.WpStep
import Iris.ProgramLogic.Adequacy.WptpHelpersA
import Iris.ProgramLogic.Adequacy.WptpHelpersB

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
          (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
          (big_sepL (fun _ ef =>
            wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        s t2 Φs (t1.length + 1)))

set_option linter.unusedVariables false in
noncomputable abbrev wptp_step_post_target
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- rebuilt `wptp` after the step
  BIBase.later
    (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s
        (t1 ++ e2 :: t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post)))

set_option linter.unusedVariables false in
noncomputable abbrev wptp_step_split_src
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    IProp GF :=
  -- pool state paired with the full `wptp` body
  BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      s (t1 ++ e1 :: t2) Φs 0)

noncomputable abbrev wptp_step_split_mid
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    IProp GF :=
  -- `wptp` body with the focused thread separated
  BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
      (BIBase.sep
        (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          s t2 Φs (t1.length + 1))))

noncomputable abbrev wptp_step_split_tgt
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    IProp GF :=
  -- `wptp` body reordered with the focused WP next to the state
  BIBase.sep
    (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ))
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        s t2 Φs (t1.length + 1)))

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wptp_step_split_body
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_step_split_src (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      wptp_step_split_mid (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) := by
  -- split the middle element inside the `big_sepL`
  have hsplit :=
    (wptp_body_at_middle (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (t1 := t1) (t2 := t2) (e := e1) (Φs := Φs) (k := 0)
      (Φ := Φ) (by simpa [Nat.zero_add] using hget)).1
  have hsplit' :
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          s (t1 ++ e1 :: t2) Φs 0 ⊢
        BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
          (BIBase.sep
            (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
              s t2 Φs (t1.length + 1))) := by
    -- normalize the tail offset in the split lemma
    simpa [Nat.zero_add] using hsplit
  let P :=
    wptp_step_split_src (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
      (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
  let Q :=
    wptp_step_split_mid (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
      (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
  have hbody : P ⊢ Q :=
    sep_mono (PROP := IProp GF) .rfl hsplit'
  simpa [P, Q] using hbody

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wptp_step_split_reorder
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    wptp_step_split_mid (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      wptp_step_split_tgt (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) := by
  -- reassociate and swap the middle elements
  have hassoc := (sep_assoc
    (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
    (R := BIBase.sep (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        s t2 Φs (t1.length + 1)))).2
  have hswap := (sep_sep_sep_comm
    (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
    (R := wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
    (S := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      s t2 Φs (t1.length + 1))).1
  exact hassoc.trans hswap

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wptp_step_split
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_step_split_src (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      wptp_step_split_tgt (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) := by
  -- split the middle element, then reorder the `sep` chain
  have hbody := wptp_step_split_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (e1 := e1)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) hget
  have hreorder := wptp_step_split_reorder (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (e1 := e1)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
  exact hbody.trans hreorder

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wptp_step_apply
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    wptp_step_split_tgt (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_post_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
          (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) := by
  -- step the focused thread and frame the remaining pool
  let X :=
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (BIBase.sep
        (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (big_sepL (fun _ ef =>
          wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))
  have hwp := adq_wp_step (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
    (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ) hstep
  exact (sep_mono (PROP := IProp GF) hwp .rfl).trans
    (Iris.BaseLogic.fupd_frame_r (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.later X)
      (Q := BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          s t2 Φs (t1.length + 1))))

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: combine split and apply for `wptp_step_frame`. -/
theorem wptp_step_frame_apply
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_step_split_src (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_post_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
          (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) := by
  -- split the middle thread, then apply the step rule
  have hsplit := wptp_step_split (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
    (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) hget
  have happly := wptp_step_apply (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns)
    (κ := κ) (κs := κs) (nt := nt) hstep
  exact hsplit.trans happly

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: lift the rebuild lemma under `fupd`. -/
theorem wptp_step_frame_post
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_post_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
          (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_post_target (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
          (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) := by
  -- lift `wptp_step_post` under the outer `fupd`
  exact Iris.BaseLogic.fupd_mono (W := W)
    (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := wptp_step_post_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
      (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt))
    (Q := wptp_step_post_target (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
      (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt))
    (wptp_step_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
      (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) hlen hget)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wptp_step_frame
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_step_split_src (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_post_target (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
          (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) := by
  -- split the middle thread, step it, then rebuild the pool
  have happly := wptp_step_frame_apply (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns)
    (κ := κ) (κs := κs) (nt := nt) hstep hget
  have hpost := wptp_step_frame_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs)
    (nt := nt) hlen hget
  exact happly.trans hpost

/-! ## Thread Pool Step -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- A step of the thread pool preserves the thread pool WP.
Coq: `wptp_step` in `adequacy.v`. -/
theorem wptp_step_len_false (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hlen : es1.length ≠ Φs.length) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es1 Φs) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            s es2 Φs σ2 (ns + 1) κs nt)) := by
  -- discharge the inconsistent-length case via pure elimination
  let Q :=
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es1 Φs)
  have hlenP : Q ⊢ BIBase.pure (es1.length = Φs.length) :=
    (sep_elim_r (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (Q := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es1 Φs)).trans
      (wptp_length (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (s := s) (es := es1)
        (Φs := Φs))
  have hkill : es1.length = Φs.length → Q ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          s es2 Φs σ2 (ns + 1) κs nt)) := by
    intro h; exact (False.elim (hlen h))
  exact pure_elim (φ := es1.length = Φs.length) hlenP hkill

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: step a focused thread starting from a full `wptp`. -/
theorem wptp_step_len_true_frame
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s
          (t1 ++ [e1] ++ t2) Φs) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s
              (t1 ++ [e2] ++ t2 ++ efs)
              (Φs ++ List.replicate efs.length fork_post)))) := by
  -- open `wptp`, apply the frame rule, then rewrite list structure
  have hbody := wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (es := t1 ++ e1 :: t2) (Φs := Φs)
  have hframe := wptp_step_frame (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns)
    (κ := κ) (κs := κs) (nt := nt) hstep hlen hget
  have hmain := (sep_mono (PROP := IProp GF) .rfl hbody).trans hframe
  simpa [wptp_step_post_target, List.singleton_append, List.append_assoc] using hmain

/-- Helper: precondition for `wptp_step_len_true`. -/
noncomputable abbrev wptp_step_len_pre
    (s : Stuckness) (es1 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat) :
    IProp GF :=
  -- state interpretation paired with the pool WP
  BIBase.sep
    (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es1 Φs)

/-- Helper: post-step body for `wptp_step_len_true`. -/
noncomputable abbrev wptp_step_len_body
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (σ2 : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- later-guarded state interpretation and rebuilt pool
  BIBase.later
    (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s
        (t1 ++ [e2] ++ t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post)))

/-- Helper: `wptp_post` target for `wptp_step_len_true`. -/
noncomputable abbrev wptp_step_len_post
    (s : Stuckness) (es2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- later-guarded thread-pool postcondition
  BIBase.later
    (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      s es2 Φs σ2 (ns + 1) κs nt)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: package a `wptp_post` existential under `▷`. -/
theorem wptp_post_later_intro
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt nt' : Nat) :
    BIBase.later
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ ns κs (nt' + nt))
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es
            (Φs ++ List.replicate nt' fork_post))) ⊢
      BIBase.later
        (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          s es Φs σ ns κs nt) := by
  -- introduce the existential fork count under the `later`
  refine later_mono ?_
  refine exists_intro' (a := nt') ?_
  simp [Nat.add_comm]

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: lift the post body to `wptp_post` in the atomic case. -/
theorem wptp_step_len_true_atomic_post
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (σ2 : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) :
    wptp_step_len_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) ⊢
      wptp_step_len_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es2 := t1 ++ [e2] ++ t2 ++ efs) (Φs := Φs)
        (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) := by
  -- package the `wptp_post` existential under `▷`
  exact wptp_post_later_intro (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (es := t1 ++ [e2] ++ t2 ++ efs) (Φs := Φs)
    (σ := σ2) (ns := ns + 1) (κs := κs) (nt := nt) (nt' := efs.length)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: atomic step case for `wptp_step_len_true`. -/
theorem wptp_step_len_true_atomic
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF))
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hprim : Λ.prim_step e1 σ1 κ e2 σ2 efs)
    (hlen : (t1 ++ [e1] ++ t2).length = Φs.length) :
    wptp_step_len_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es1 := t1 ++ [e1] ++ t2) (Φs := Φs)
        (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_len_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es2 := t1 ++ [e2] ++ t2 ++ efs) (Φs := Φs)
          (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) := by
  -- rebuild the pool and package the `wptp_post`
  have hlen' : Φs.length = t1.length + t2.length + 1 := by
    simpa [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen.symm
  rcases wptp_lookup_middle (t1 := t1) (t2 := t2) (Φs := Φs) hlen' with ⟨Φ, hget⟩
  have hmain := wptp_step_len_true_frame (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns) (κ := κ) (κs := κs)
    (nt := nt) hprim hlen' hget
  have hpost := wptp_step_len_true_atomic_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)
  exact hmain.trans <|
    Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := wptp_step_len_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt))
      (Q := wptp_step_len_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es2 := t1 ++ [e2] ++ t2 ++ efs) (Φs := Φs)
        (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)) hpost

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wptp_step_len_true (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hstep : step (Λ := Λ) (es1, σ1) κ (es2, σ2))
    (hlen : es1.length = Φs.length) :
    wptp_step_len_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es1 := es1) (Φs := Φs) (σ1 := σ1) (ns := ns)
        (κ := κ) (κs := κs) (nt := nt) ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (wptp_step_len_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es2 := es2) (Φs := Φs) (σ2 := σ2) (ns := ns)
          (κs := κs) (nt := nt)) := by
  -- focus the stepping thread, then rebuild the pool and add the existential
  classical
  cases hstep with
  | step_atomic e1 σ1' e2 σ2' efs t1 t2 _ hprim =>
      exact wptp_step_len_true_atomic (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
        (Φs := Φs) (σ1 := σ1) (σ2 := σ2) (ns := ns) (κ := κ) (κs := κs)
        (nt := nt) hprim (by simpa using hlen)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
theorem wptp_step' (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hstep : step (es1, σ1) κ (es2, σ2)) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (M := M) (F := F) (Λ := Λ) (W := W) s es1 Φs)
    ⊢ uPred_fupd (M := M) (F := F) W
        Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            s es2 Φs σ2 (ns + 1) κs nt)) := by
  -- split on length consistency, then dispatch to the appropriate lemma
  classical
  by_cases hlen : es1.length = Φs.length
  · simpa [state_interp] using
      wptp_step_len_true (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es1 := es1) (es2 := es2) (κ := κ) (κs := κs)
        (σ1 := σ1) (ns := ns) (σ2 := σ2) (nt := nt)
        (Φs := Φs) hstep hlen
  · simpa [state_interp] using
      wptp_step_len_false (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es1 := es1) (es2 := es2) (κ := κ) (κs := κs)
        (σ1 := σ1) (ns := ns) (σ2 := σ2) (nt := nt)
        (Φs := Φs) hlen


end Iris.ProgramLogic
