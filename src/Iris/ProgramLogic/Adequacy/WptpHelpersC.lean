/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.FUpd
import Iris.ProgramLogic.Adequacy.WptpHelpersB
import Iris.ProgramLogic.Adequacy.Preservation

/-! # Adequacy: Thread Pool Helpers (C)

Reference: `iris/program_logic/adequacy.v`

This file defines the adequacy continuation/invariant packaging and the
remaining `wptp` preservation helpers used by strong adequacy.
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
noncomputable abbrev adequacy_cont
    (s : Stuckness) (es t2 : List Λ.expr) (σ2 : Λ.state)
    (n : Nat) (Φs : List (Λ.val → IProp GF)) (φ : Prop) : IProp GF :=
  -- continuation that consumes the final resources to establish `φ`
  BIBase.forall fun es' =>
    BIBase.forall fun t2' =>
      BIBase.wand (BIBase.pure (t2 = es' ++ t2')) <|
      BIBase.wand (BIBase.pure (es'.length = es.length)) <|
      BIBase.wand
        (BIBase.pure (∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2)) <|
      BIBase.wand (state_interp (Λ := Λ) (GF := GF) σ2 n [] t2'.length) <|
      BIBase.wand
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es' Φs) <|
      BIBase.wand
        (big_sepL (fun _ ef =>
          wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2') <|
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)

noncomputable abbrev adequacy_pre
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φs : List (Λ.val → IProp GF)) (φ : Prop) : IProp GF :=
  -- precondition: initial state interpretation, pool WP, and continuation
  BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
    (BIBase.sep
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
      (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2)
        (n := n) (Φs := Φs) (φ := φ)))

noncomputable abbrev adequacy_inv
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Prop) : IProp GF :=
  -- existentially package the postconditions for the thread pool
  BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)

noncomputable abbrev adequacy_post
    (s : Stuckness) (es t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φs : List (Λ.val → IProp GF)) (φ : Prop) : IProp GF :=
  -- postcondition: final state interpretation, post WPs, and continuation
  BIBase.sep
    (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      s t2 Φs σ2 n [] 0)
    (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))

theorem adequacy_cont_drop
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ1 : Λ.state) (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state)
    (n : Nat) (φ : Prop) :
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (BIBase.sep
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
          (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))) ⊢
      BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs) := by
  -- discard the continuation from the precondition
  exact sep_mono (PROP := IProp GF) .rfl
    (sep_elim_l
      (P := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
      (Q := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)))

theorem wptp_len_from_pre
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ1 : Λ.state) (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state)
    (n : Nat) (φ : Prop) :
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (BIBase.sep
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
          (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))) ⊢
      BIBase.pure (es.length = Φs.length) := by
  -- extract the length equality hidden in `wptp`
  exact (sep_elim_r (P := state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
    (Q := BIBase.sep
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
      (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)))).trans
    ((sep_elim_l (P := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)
      (Q := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))).trans
      (wptp_length (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (Φs := Φs)))

theorem wptp_preservation_core
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (Φs : List (Λ.val → IProp GF))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
        (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          s t2 Φs σ2 n [] 0) := by
  -- specialize preservation to an empty fork suffix
  have hpres :=
    wptp_preservation (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (n := n) (es1 := es) (es2 := t2) (κs := κs) (κs' := [])
      (σ1 := σ1) (ns := 0) (σ2 := σ2) (nt := 0) (Φs := Φs) hsteps
  simpa [List.append_nil] using hpres

theorem wptp_preservation_frame
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φs : List (Λ.val → IProp GF)) (φ : Prop)
  (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
        (adequacy_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)) := by
  let cont := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) -- frame continuation
    (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)
  let post := wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2 Φs σ2 n [] 0
  have hmono :
      BIBase.sep
          (BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs)) cont ⊢
        BIBase.sep
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n post) cont :=
    sep_mono (PROP := IProp GF)
      (wptp_preservation_core (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (σ1 := σ1) (κs := κs) (t2 := t2) (σ2 := σ2)
        (n := n) (Φs := Φs) hsteps) .rfl
  exact (sep_assoc (P := state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
    (Q := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs) (R := cont)).2.trans
    (hmono.trans
      (step_fupdN_frame_r (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n := n)
        (P := post) (Q := cont)))

theorem apply_cont
    (s : Stuckness) (es t2 es' t2' : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n : Nat) (φ : Prop)
    (hsplit : t2 = es' ++ t2')
    (hlen_es : es'.length = es.length)
    (hns : ∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2) :
  BIBase.sep
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
        (BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ2 n [] t2'.length)
          (BIBase.sep
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es' Φs)
            (big_sepL (fun _ ef =>
              wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2')))
      ⊢ uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  iintro ⟨Hcont, Hσ, Hwp, Hfork⟩ -- apply the stored continuation
  ispecialize Hcont $$ %es'
  ispecialize Hcont $$ %t2'
  ispecialize Hcont $$ %hsplit
  ispecialize Hcont $$ %hlen_es
  ispecialize Hcont $$ %hns
  ispecialize Hcont $$ Hσ
  ispecialize Hcont $$ Hwp
  ispecialize Hcont $$ Hfork
  iexact Hcont

theorem wptp_post_apply_core
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n nt' : Nat) (φ : Prop)
    (hlen_init : es.length = Φs.length)
    (hns : ∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2)
    (hlen_t2 : t2.length = Φs.length + nt') :
  BIBase.sep
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
        (BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ2 n [] nt')
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
            (Φs ++ List.replicate nt' fork_post))) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  let es' := t2.take es.length -- isolate the original threads
  let t2' := t2.drop es.length
  have hsplit : t2 = es' ++ t2' := by
    simpa [es', t2'] using (List.take_append_drop es.length t2).symm
  have hlen_es : es'.length = es.length := by
    have ht2 : t2.length = es.length + nt' := by simpa [hlen_init] using hlen_t2
    simpa [es'] using length_take_eq (es := es) (t2 := t2) (n := nt') ht2
  have hres :=
    wptp_post_split_resources (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es) (t2 := t2) (Φs := Φs)
      (σ2 := σ2) (n := n) (nt' := nt') hlen_init hlen_t2
  have happly :=
    apply_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (es' := es') (t2' := t2') (Φs := Φs) (W := W)
      (σ2 := σ2) (n := n) (φ := φ) hsplit hlen_es hns
  exact (sep_mono (PROP := IProp GF) .rfl hres).trans happly

theorem wptp_post_apply
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n : Nat) (φ : Prop)
    (hlen_init : es.length = Φs.length)
    (hns : ∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2) :
    BIBase.sep
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
        (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          s t2 Φs σ2 n [] 0) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  let cont :=
    adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)
  refine (sep_exists_l (P := cont) (Ψ := fun nt' => -- open the post-state existential
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ2 n [] (0 + nt'))
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
        (Φs ++ List.replicate nt' fork_post)))).1.trans ?_
  refine exists_elim ?_
  intro nt'
  have hlenP :=
    wptp_post_len (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (t2 := t2) (Φs := Φs) (σ2 := σ2) (n := n) (nt' := nt')
  have hlenP' :
      BIBase.sep cont
          (BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ2 n [] (0 + nt'))
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
              (Φs ++ List.replicate nt' fork_post))) ⊢
        BIBase.pure (t2.length = Φs.length + nt') :=
    (sep_elim_r
      (P := cont)
      (Q := BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] (0 + nt'))
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s t2
          (Φs ++ List.replicate nt' fork_post)))).trans hlenP
  refine pure_elim (PROP := IProp GF)
    (φ := t2.length = Φs.length + nt') hlenP' ?_
  intro hlen_t2
  exact wptp_post_apply_core (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (t2 := t2) (Φs := Φs)
    (σ2 := σ2) (n := n) (nt' := nt') (φ := φ) hlen_init hns hlen_t2

theorem wp_progress_drop_cont
    (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := .notStuck) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ))) :
    ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
            BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
              (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) .notStuck es Φs)) := by
  intro W -- drop the continuation to obtain the plain pool WP
  refine (Hwp W).trans ?_
  refine Iris.BaseLogic.fupd_mono (W := W)
    (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := .notStuck) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ))
    (Q := BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
      BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) .notStuck es Φs)) ?_
  refine exists_elim ?_; intro Φs
  refine exists_intro' (a := Φs) ?_
  -- peel the continuation and rebuild the existential witness
  simpa [adequacy_pre] using
    (adequacy_cont_drop (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := .notStuck) (es := es) (Φs := Φs) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ))

theorem wp_progress_from_strong
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
            (s := s) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    ∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2 := by
  intro e2 hs hemem -- reduce to the non-stuck case and reuse `wp_progress`
  cases s with
  | notStuck =>
      have hwp' :=
        wp_progress_drop_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
          (es := es) (σ1 := σ1) (κs := κs) (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp
      exact wp_progress (Λ := Λ) (GF := GF) (M := M) (F := F)
        (n := n) (es := es) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (e2 := e2) hwp' hsteps hemem
  | maybeStuck =>
      cases hs


end Iris.ProgramLogic
