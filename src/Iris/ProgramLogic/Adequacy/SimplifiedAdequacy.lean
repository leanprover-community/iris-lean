/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.StrongAdequacy

/-! # Adequacy: Simplified Adequacy

Reference: `iris/program_logic/adequacy.v`

This file derives simplified adequacy for single expressions and the
auxiliary adequacy invariants used in the proof.
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
/-! ## Simplified Adequacy -/

theorem head_eq_of_splits (e2 : Λ.expr) (t2 t2' t2'' : List Λ.expr) (v2 : Λ.val)
    (hsplit' : t2 = e2 :: t2'') (ht2 : t2 = Λ.of_val v2 :: t2') :
    e2 = Λ.of_val v2 := by
  -- compare heads of the two decompositions of `t2`
  have hcons : e2 :: t2'' = Λ.of_val v2 :: t2' := by
    calc
      e2 :: t2'' = t2 := by simp [hsplit']
      _ = Λ.of_val v2 :: t2' := by simp [ht2]
  cases hcons
  rfl

omit [FiniteMapLaws Positive M] in
theorem wp_value_fupd_mask (s : Stuckness) (v2 : Λ.val) (φ : Λ.val → Prop) :
    wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ (Λ.of_val v2)
        (fun v => BIBase.pure (φ v)) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure (φ v2)) := by
  -- use the value case and then shrink the mask
  have hval :
      wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ (Λ.of_val v2)
          (fun v => BIBase.pure (φ v)) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.pure (φ v2)) := by
    simpa using
      (wp_value_fupd (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (E := Iris.Set.univ) (Φ := fun v => BIBase.pure (φ v)) (v := v2)).1
  have hmask :
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ (BIBase.pure (φ v2)) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure (φ v2)) :=
    (Iris.BaseLogic.fupd_mono (W := W) (M := M) (F := F)
      Iris.Set.univ Iris.Set.univ
      (fupd_intro_univ_empty (GF := GF) (M := M) (F := F) (W := W)
        (P := BIBase.pure (φ v2)))).trans
    (Iris.BaseLogic.fupd_trans (W := W) (M := M) (F := F)
      Iris.Set.univ Iris.Set.univ maskEmpty (BIBase.pure (φ v2)))
  exact hval.trans hmask

omit [FiniteMapLaws Positive M] in
theorem wptp_singleton_fupd
    (s : Stuckness) (e2 : Λ.expr) (v2 : Λ.val) (φ : Λ.val → Prop)
    (hhead : e2 = Λ.of_val v2) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s [e2]
        [fun v => BIBase.pure (φ v)] ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure (φ v2)) := by
  -- reduce to the singleton WP and use the value case
  have hwp :=
    wptp_singleton_elim (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e := e2) (Φ := fun v => BIBase.pure (φ v))
  have hval :=
    wp_value_fupd_mask (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (v2 := v2) (φ := φ)
  exact hwp.trans (by simpa [hhead] using hval)

omit [FiniteMapLaws Positive M] in
theorem adequacy_cont_value
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (v2 : Λ.val) (t2' : List Λ.expr) (φ : Λ.val → Prop)
    (ht2 : t2 = Λ.of_val v2 :: t2') :
    (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [fun v => BIBase.pure (φ v)]) (φ := φ v2) := by
  -- discharge the continuation using the head value
  iintro _ %es' %t2'' ⌜hsplit⌝ ⌜hlen⌝ _ _ Hwp _
  rcases list_length_eq_one (l := es') (by simpa using hlen) with ⟨e2, hes⟩
  subst hes
  have hsplit' : t2 = e2 :: t2'' := by simpa using hsplit
  have hhead := head_eq_of_splits (Λ := Λ) (e2 := e2) (t2 := t2)
    (t2' := t2') (t2'' := t2'') (v2 := v2) hsplit' ht2
  iapply (wptp_singleton_fupd (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (e2 := e2) (v2 := v2) (φ := φ) hhead)
  iexact Hwp

omit [FiniteMapLaws Positive M] in
theorem adequacy_cont_true
    (s : Stuckness) (es t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φs : List (Λ.val → IProp GF)) :
    (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := Φs) (φ := True) := by
  -- ignore the resources and return `True` under a fancy update
  iintro _ %es' %t2' _ _ _ _ _ _
  exact (pure_intro True.intro).trans <|
    fupd_intro_univ_empty (GF := GF) (M := M) (F := F) (W := W)
      (P := BIBase.pure True)

omit [FiniteMapLaws Positive M] in
theorem adequacy_cont_invariance
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (φ : Prop) :
    BIBase.wand
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.length - 1))
        (BIBase.«exists» fun (_ : Iris.Set Positive) =>
          uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [fun _ => BIBase.pure True]) (φ := φ) := by
  -- use the provided wand to discharge the final state interpretation
  iintro Hφ
  iintro %es' %t2' ⌜hsplit⌝ ⌜hlen⌝ _ Hσ _ _
  rcases list_length_eq_one (l := es') (by simpa using hlen) with ⟨e2, hes⟩
  subst hes
  have hsplit' : t2 = e2 :: t2' := by simpa using hsplit
  have hlen' : t2.length - 1 = t2'.length := by
    simp [hsplit']
  simp only [hlen']
  ispecialize Hφ $$ Hσ
  iapply (exists_elim
    (Φ := fun (_ : Iris.Set Positive) =>
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))
    (Q := uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) ?_)
  · intro _; exact .rfl
  · iexact Hφ

omit [FiniteMapLaws Positive M] in
theorem wptp_frame_cont
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φ : Λ.val → IProp GF) (φ : Prop)
    (hcont : (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s [e] [Φ] ⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s [e] [Φ])
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
          (Φs := [Φ]) (φ := φ)) := by
  -- append the continuation using `emp` framing
  exact (sep_emp (P := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s [e] [Φ])).2.trans
    (sep_mono (PROP := IProp GF) .rfl hcont)

omit [FiniteMapLaws Positive M] in
theorem wp_to_wptp_cont_frame
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φ : Λ.val → IProp GF) (φ : Prop) (R : IProp GF)
    (hcont : R ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    BIBase.sep (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R ⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s [e] [Φ])
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
          (Φs := [Φ]) (φ := φ)) := by
  -- lift the singleton WP and swap in the continuation resource
  have hwp :=
    wptp_singleton_intro (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e := e) (Φ := Φ)
  have hframe :
      BIBase.sep (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R ⊢
        BIBase.sep (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s [e] [Φ]) R :=
    sep_mono (PROP := IProp GF) hwp .rfl
  exact hframe.trans (sep_mono (PROP := IProp GF) .rfl hcont)

omit [FiniteMapLaws Positive M] in
theorem wp_to_wptp_cont
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φ : Λ.val → IProp GF) (φ : Prop)
    (hcont : (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ ⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s [e] [Φ])
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
          (Φs := [Φ]) (φ := φ)) := by
  -- add `emp` and use the framed continuation lemma
  have hframe :=
    wp_to_wptp_cont_frame (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e := e) (t2 := t2) (σ2 := σ2) (n := n)
      (Φ := Φ) (φ := φ) (R := (BIBase.emp : IProp GF)) hcont
  exact (sep_emp (P := wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ)).2.trans hframe

section AdequacyInv

variable (s : Stuckness) (e : Λ.expr) (σ : Λ.state)
variable (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
variable (Φ : Λ.val → IProp GF) (φ : Prop)

omit [FiniteMapLaws Positive M] in
theorem wp_adequacy_inv_core
    (hcont : (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
        (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) ⊢
      adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (σ1 := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) := by
  -- package the singleton continuation into the adequacy invariant
  have hwp_cont :=
    wp_to_wptp_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e := e) (t2 := t2) (σ2 := σ2) (n := n) (Φ := Φ) (φ := φ) hcont
  exact (exists_intro' (Ψ := fun Φs =>
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := [e]) (σ1 := σ) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
    [Φ] (sep_mono (PROP := IProp GF) .rfl hwp_cont))

omit [FiniteMapLaws Positive M] in
theorem wp_adequacy_inv_frame_core
    (R : IProp GF)
    (hcont : R ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
        (BIBase.sep (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R) ⊢
      adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (σ1 := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) := by
  -- package the framed continuation into the adequacy invariant
  have hwp_cont :=
    wp_to_wptp_cont_frame (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (e := e) (t2 := t2) (σ2 := σ2) (n := n)
      (Φ := Φ) (φ := φ) (R := R) hcont
  exact (exists_intro' (Ψ := fun Φs =>
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
      (s := s) (es := [e]) (σ1 := σ) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
    [Φ] (sep_mono (PROP := IProp GF) .rfl hwp_cont))

omit [FiniteMapLaws Positive M] in
theorem wp_adequacy_inv
    (Hwp : ∀ W : WsatGS GF, ∀ κs : List Λ.observation,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
            (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ)))
    (hcont : ∀ W : WsatGS GF, (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    ∀ W : WsatGS GF, (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := [e]) (σ1 := σ) (κs := κs)
          (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)) := by
  -- repackage the single-thread WP into the adequacy invariant
  intro W
  have hcore := wp_adequacy_inv_core (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (e := e) (σ := σ) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φ := Φ) (φ := φ) (hcont W)
  exact (Hwp W κs).trans <|
    Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
        (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ))
      (Q := adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (σ1 := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)) hcore

omit [FiniteMapLaws Positive M] in
theorem wp_adequacy_inv_frame
    (W : WsatGS GF) (R : IProp GF)
    (Hwp : (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
          (BIBase.sep (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R)))
    (hcont : R ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := [e]) (σ1 := σ) (κs := κs)
          (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)) := by
  -- frame the extra resource into the continuation
  have hcore := wp_adequacy_inv_frame_core (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (e := e) (σ := σ) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φ := Φ) (φ := φ) (R := R) hcont
  exact Hwp.trans <|
    Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
        (BIBase.sep (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R))
      (Q := adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (s := s) (es := [e]) (σ1 := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)) hcore

end AdequacyInv

theorem wp_adequacy_value
    (s : Stuckness) (e : Λ.expr) (σ : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Λ.val → Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.sep
              (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
              (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e
                (fun v => BIBase.pure (φ v)))))
    (hsteps : nsteps (Λ := Λ) n ([e], σ) κs (t2, σ2))
    (v2 : Λ.val) (t2' : List Λ.expr) (ht2 : t2 = Λ.of_val v2 :: t2') :
    φ v2 := by
  -- apply strong adequacy with the value continuation
  have Hinv :=
    wp_adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (σ := σ) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φ := fun v => BIBase.pure (φ v))
      (φ := φ v2) Hwp (fun W =>
        adequacy_cont_value (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (e := e) (t2 := t2) (σ2 := σ2) (n := n)
          (v2 := v2) (t2' := t2') (φ := φ) ht2)
  exact wp_strong_adequacy (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := [e]) (σ1 := σ) (n := n) (κs := κs)
    (t2 := t2) (σ2 := σ2) (φ := φ v2) Hinv hsteps

theorem wp_adequacy_not_stuck
    (s : Stuckness) (e : Λ.expr) (σ : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Λ.val → Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.sep
              (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
              (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e
                (fun v => BIBase.pure (φ v)))))
    (hsteps : nsteps (Λ := Λ) n ([e], σ) κs (t2, σ2))
    (e2 : Λ.expr) (hs : s = .notStuck) (hemem : e2 ∈ t2) :
    not_stuck (Λ := Λ) e2 σ2 := by
  -- reuse strong adequacy to extract the progress property
  have Hinv :=
    wp_adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (σ := σ) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φ := fun v => BIBase.pure (φ v))
      (φ := True) Hwp (fun W =>
        adequacy_cont_true (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
          (Φs := [fun v => BIBase.pure (φ v)]))
  exact wp_progress_from_strong (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := [e]) (σ1 := σ) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (φ := True) Hinv hsteps e2 hs hemem

section InvarianceInv

variable (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
variable (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
variable (φ : Prop)

omit [FiniteMapLaws Positive M] in
theorem wp_invariance_inv
    (Hwp : ∀ W : WsatGS GF, (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
          (BIBase.sep
            (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1
              (fun _ => BIBase.pure True))
            (BIBase.wand
              (state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.length - 1))
              (BIBase.«exists» fun (_ : Iris.Set Positive) =>
                uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
                  (BIBase.pure φ)))))) :
    ∀ W : WsatGS GF, (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (es := [e1]) (σ1 := σ1) (κs := κs) (t2 := t2)
          (σ2 := σ2) (n := n) (φ := φ)) := by
  -- wrap the invariance wand into the adequacy invariant
  intro W
  let R : IProp GF :=
    BIBase.wand (state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.length - 1))
      (BIBase.«exists» fun (_ : Iris.Set Positive) =>
        uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))
  exact wp_adequacy_inv_frame (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
    (s := s) (e := e1) (σ := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φ := fun _ => BIBase.pure True)
    (φ := φ) (R := R) (by simpa [R] using (Hwp W)) (by
      simpa [R] using
        (adequacy_cont_invariance (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
          (s := s) (e := e1) (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))

end InvarianceInv


/-- Simplified adequacy for a single expression. This requires the
`IrisGS` instance to use `num_laters_per_step = 0` and a simple
state interpretation that ignores step count and fork count.
Coq: `wp_adequacy` in `adequacy.v`. -/
theorem wp_adequacy (s : Stuckness) (e : Λ.expr) (σ : Λ.state)
    (φ : Λ.val → Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.sep
              (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
              (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e
                (fun v => BIBase.pure (φ v))))) :
    Adequate (Λ := Λ) s e σ (fun v _ => φ v) :=
  by
    -- unpack `rtc` into `nsteps` and use strong adequacy for value/progress
    refine (adequate_alt (Λ := Λ) (s := s) (e1 := e) (σ1 := σ)
      (φ := fun v _ => φ v)).2 ?_
    intro t2 σ2 hrtc
    rcases (erased_steps_nsteps (Λ := Λ) ([e], σ) (t2, σ2)).1 hrtc with
      ⟨n, κs, hsteps⟩
    refine ⟨?_, ?_⟩
    · intro v2 t2' ht2
      exact wp_adequacy_value (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (e := e) (σ := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp hsteps v2 t2' ht2
    · intro e2 hs hemem
      exact wp_adequacy_not_stuck (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (e := e) (σ := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp hsteps e2 hs hemem


end Iris.ProgramLogic
