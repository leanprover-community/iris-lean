/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.WptpHelpersA

/-! # Adequacy: Thread Pool Helpers (B)

Reference: `iris/program_logic/adequacy.v`

This file continues the thread-pool helper lemmas, focusing on rebuilding
`wptp` after a step and merging forked resources.
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

noncomputable abbrev wptp_step_post_inner_src
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- inner state and body layout before rebuilding `wptp`
  BIBase.sep
    (BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (BIBase.sep (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (big_sepL (fun _ ef =>
          wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)))
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2 Φs (t1.length + 1)))

noncomputable abbrev wptp_step_post_inner_tgt
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- rebuilt `wptp` in the post-state
  BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
    (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s
      (t1 ++ e2 :: t2 ++ efs)
      (Φs ++ List.replicate efs.length fork_post))

noncomputable abbrev wptp_step_post_src
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- `later`-wrapped variant of `wptp_step_post_inner_src`
  BIBase.sep
    (BIBase.later
      (BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
        (BIBase.sep (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
          (big_sepL (fun _ ef =>
            wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2 Φs (t1.length + 1)))

noncomputable abbrev wptp_step_post_tgt
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- `later`-wrapped variant of `wptp_step_post_inner_tgt`
  BIBase.later
    (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s
        (t1 ++ e2 :: t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post)))

noncomputable abbrev wptp_split_fork_pre
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF)) : IProp GF :=
  -- precondition for rebuilding a forked pool
  BIBase.sep
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
      (big_sepL (fun _ ef =>
        wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2)

noncomputable abbrev wptp_split_fork_post
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF)) : IProp GF :=
  -- combined `wptp` after reattaching forked threads
  wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s (es ++ t2)
    (Φs ++ List.replicate t2.length fork_post)
theorem wptp_step_post_push (X A C : IProp GF) :
    BIBase.sep (BIBase.later X) (BIBase.sep A C) ⊢
      BIBase.later (BIBase.sep X (BIBase.sep A C)) := by
  -- add the `later` frame to the right and combine with `later_sep`
  have hlat : BIBase.sep A C ⊢ BIBase.later (BIBase.sep A C) := later_intro
  exact (sep_mono (PROP := IProp GF) .rfl hlat).trans
    (later_sep (P := X) (Q := BIBase.sep A C)).2

theorem wptp_step_post_inner
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_step_post_inner_src (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) ⊢
      wptp_step_post_inner_tgt (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) := by
  -- reorder the pieces and rebuild the thread pool
  have hreorder := (sep_reorder_for_rebuild
    (P := state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
    (A := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0)
    (B := wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
    (C := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2 Φs (t1.length + 1))
    (D := big_sepL (fun _ ef =>
      wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)).1
  exact hreorder.trans <|
    sep_mono (PROP := IProp GF) .rfl
      (wptp_rebuild (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (Φ := Φ) hlen hget)

theorem wptp_step_post
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_step_post_src (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) ⊢
      wptp_step_post_tgt (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) := by
  -- push under `▷` then apply the rebuild lemma inside
  let X :=
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (BIBase.sep
        (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (big_sepL (fun _ ef =>
          wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))
  let A := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t1 Φs 0
  let C := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2 Φs (t1.length + 1)
  have hpush := wptp_step_post_push (X := X) (A := A) (C := C)
  have hinner := wptp_step_post_inner (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)
    hlen hget
  exact hpush.trans (later_mono (PROP := IProp GF) hinner)

theorem wptp_post_merge
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt nt' : Nat) :
    wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        s es (Φs ++ List.replicate nt' fork_post) σ ns κs (nt + nt')
      ⊢ wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        s es Φs σ ns κs nt := by
  -- repackage the existential by merging the replicate suffixes
  refine exists_elim ?_
  intro nt''
  refine exists_intro' (a := nt' + nt'') ?_
  simpa [append_replicate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (.rfl : _ ⊢ _)

theorem wptp_split_fork_left
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (hlen : es.length = Φs.length) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s (es ++ t2)
        (Φs ++ List.replicate t2.length fork_post) ⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
        (big_sepL (fun _ ef =>
          wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2) := by
  -- peel the body and apply the append-fork split
  have hbody := wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (es := es ++ t2) (Φs := Φs ++ List.replicate t2.length fork_post)
  have hsplit := (wptp_body_at_append_fork (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (t2 := es) (efs := t2) (Φs := Φs) (k := 0)
    (hlen := by simpa [Nat.zero_add, hlen, List.length_append, List.length_replicate])).2
  have hleft :
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs 0 ⊢
        wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs :=
    wptp_of_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es) (Φs := Φs) hlen
  exact (hbody.trans hsplit).trans (sep_mono (PROP := IProp GF) hleft .rfl)

theorem wptp_split_fork_right
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (hlen : es.length = Φs.length) :
    wptp_split_fork_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (t2 := t2) (Φs := Φs) ⊢
      wptp_split_fork_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (t2 := t2) (Φs := Φs) := by
  -- rebuild the combined `wptp` from the body and length equality
  have hbody' := wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (es := es) (Φs := Φs)
  have hcomb :=
    (wptp_body_at_append_fork (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (t2 := es) (efs := t2) (Φs := Φs) (k := 0)
      (hlen := by simpa [Nat.zero_add, hlen, List.length_append, List.length_replicate])).1
  have hlen' :
      (es ++ t2).length =
        (Φs ++ List.replicate t2.length fork_post).length := by
    simpa [hlen, List.length_append, List.length_replicate, Nat.add_assoc, Nat.add_left_comm]
  have hwrap := wptp_of_body (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (es := es ++ t2) (Φs := Φs ++ List.replicate t2.length fork_post) hlen'
  exact (sep_mono (PROP := IProp GF) hbody' .rfl).trans (hcomb.trans hwrap)

theorem wptp_split_fork
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (hlen : es.length = Φs.length) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s (es ++ t2)
        (Φs ++ List.replicate t2.length fork_post) ⊣⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
        (big_sepL (fun _ ef =>
          wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2) := by
  -- package the two directions using the helper lemmas
  exact ⟨
    wptp_split_fork_left (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (Φs := Φs) hlen,
    wptp_split_fork_right (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (Φs := Φs) hlen⟩

theorem wptp_split_take_drop
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (nt' : Nat) (hlen_init : es.length = Φs.length)
    (hlen_t2 : t2.length = Φs.length + nt') :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
        (Φs ++ List.replicate nt' fork_post) ⊣⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s (t2.take es.length) Φs)
        (big_sepL (fun _ ef =>
          wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post)
          (t2.drop es.length)) := by
  let es' := t2.take es.length -- split the pool at the original length
  let t2' := t2.drop es.length
  have ht2 : t2.length = es.length + nt' := by -- normalize the length equation
    simpa [hlen_init] using hlen_t2
  have hsplit : t2 = es' ++ t2' := by
    simpa [es', t2'] using (List.take_append_drop es.length t2).symm
  have hlen_es : es'.length = es.length := by
    simpa [es'] using length_take_eq (es := es) (t2 := t2) (n := nt') ht2
  have hlen_esΦ : es'.length = Φs.length := by
    simpa [hlen_es, hlen_init]
  have hlen_drop : t2'.length = nt' := by
    simpa [t2'] using length_drop_eq (es := es) (t2 := t2) (n := nt') ht2
  have hsplit_wptp :=
    wptp_split_fork (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es') (t2 := t2') (Φs := Φs) hlen_esΦ
  have hsplit_wptp' :
      wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
          (Φs ++ List.replicate nt' fork_post) ⊣⊢
        BIBase.sep
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es' Φs)
          (big_sepL (fun _ ef =>
            wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2') := by
    -- normalize the split to use `t2` and `nt'`
    simpa [hsplit, hlen_drop] using hsplit_wptp
  simpa [es', t2'] using hsplit_wptp'

theorem wptp_post_split_resources
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n nt' : Nat)
    (hlen_init : es.length = Φs.length)
    (hlen_t2 : t2.length = Φs.length + nt') :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] nt')
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
          (Φs ++ List.replicate nt' fork_post)) ⊢
      BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.drop es.length).length)
        (BIBase.sep
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s (t2.take es.length) Φs)
          (big_sepL (fun _ ef =>
            wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post)
            (t2.drop es.length))) := by
  have ht2 : t2.length = es.length + nt' := by
    simpa [hlen_init] using hlen_t2
  have hlen_drop : (t2.drop es.length).length = nt' := by
    simpa using length_drop_eq (es := es) (t2 := t2) (n := nt') ht2
  have hstate :
      state_interp (Λ := Λ) (GF := GF) σ2 n [] nt' ⊢
        state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.drop es.length).length := by
    simpa [hlen_drop]
  have hsplit :=
    wptp_split_take_drop (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es) (t2 := t2) (Φs := Φs) (nt' := nt') hlen_init hlen_t2
  exact sep_mono (PROP := IProp GF) hstate hsplit.1

theorem wptp_post_len
    (s : Stuckness) (t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n nt' : Nat) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] nt')
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
          (Φs ++ List.replicate nt' fork_post)) ⊢
      BIBase.pure (t2.length = Φs.length + nt') := by
  have hlen := -- extract the length equality from `wptp`
    (sep_elim_r
      (P := state_interp (Λ := Λ) (GF := GF) σ2 n [] nt')
      (Q := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
        (Φs ++ List.replicate nt' fork_post))).trans
      (wptp_length (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := t2) (Φs := Φs ++ List.replicate nt' fork_post))
  refine hlen.trans ?_
  refine pure_mono ?_
  intro h
  simpa [List.length_append, List.length_replicate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h


end Iris.ProgramLogic
