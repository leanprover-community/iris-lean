/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.ThreadPool

/-! # Adequacy: Fancy-Update Helpers

Reference: `iris/program_logic/adequacy.v`

This file defines the local fancy-update helpers and the step-indexed
`step_fupdN` modality used in adequacy.
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
/-! ## FUpd Helpers -/

theorem fupd_intro (E : Iris.Set Positive) (P : IProp GF) :
    P ⊢ fupd' (W := W) (M := M) (F := F) E E P := by
  -- introduce a nested update and then collapse it
  have hsubset : Subset E E := by
    intro _ h; exact h
  have hintro :=
    Iris.BaseLogic.fupd_intro_mask (W := W)
      (M := M) (F := F) (E1 := E) (E2 := E) hsubset (P := P)
  exact hintro.trans <|
    Iris.BaseLogic.fupd_trans (W := W)
      (M := M) (F := F) (E1 := E) (E2 := E) (E3 := E) (P := P)

theorem fupd_intro_univ_empty (P : IProp GF) :
    P ⊢ fupd' (W := W) (M := M) (F := F) Iris.Set.univ maskEmpty P := by
  -- open to the empty mask, shrink, then compose
  have hsubset : Subset maskEmpty Iris.Set.univ := by
    intro _ h; exact False.elim h
  have hopen :=
    Iris.BaseLogic.fupd_intro_mask (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty) hsubset (P := P)
  have hshrink :
      fupd' (W := W) (M := M) (F := F) maskEmpty Iris.Set.univ P ⊢
        fupd' (W := W) (M := M) (F := F) maskEmpty maskEmpty P :=
    Iris.BaseLogic.fupd_plain_mask (W := W)
      (M := M) (F := F) (E1 := maskEmpty) (E2 := Iris.Set.univ) hsubset (P := P)
  have hmono :
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ maskEmpty
          (fupd' (W := W) (M := M) (F := F) maskEmpty Iris.Set.univ P) ⊢
        fupd' (W := W) (M := M) (F := F) Iris.Set.univ maskEmpty
          (fupd' (W := W) (M := M) (F := F) maskEmpty maskEmpty P) :=
    Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
      (P := fupd' (W := W) (M := M) (F := F) maskEmpty Iris.Set.univ P)
      (Q := fupd' (W := W) (M := M) (F := F) maskEmpty maskEmpty P) hshrink
  exact hopen.trans (hmono.trans <|
    Iris.BaseLogic.fupd_trans (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
      (E3 := maskEmpty) (P := P))

noncomputable def step_fupdN {Λ : Language} {W : WsatGS GF} (n : Nat) (P : IProp GF) :
    IProp GF :=
  -- iterate the Coq-style step-fupd: `|={E}=> ▷ |={E}=>` `n` times
  Nat.rec P
    (fun _ Q =>
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ <|
        BIBase.later
          (fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ Q))
    n

/-- Adequacy-local `step_fupdN_plain` specialized to the top mask.

    Coq: `step_fupdN_plain` in `updates.v`. -/
theorem step_fupdN_plain {W : WsatGS GF} (n : Nat) (P : IProp GF) [Plain P] :
    step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P ⊢
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P)) := by
  -- unfold to the BI step-fupd chain and apply the generic lemma
  simpa [step_fupdN, Iris.BI.step_fupdN, fupd'] using
    (Iris.BI.step_fupdN_plain (PROP := IProp GF) (MASK := Positive)
      (Eo := Iris.Set.univ) (Ei := Iris.Set.univ) (n := n) (P := P))

/-- Helper: lift `step_fupdN_plain` through an outer `fupd`. -/
theorem step_fupdN_plain_fupd {W : WsatGS GF} (n : Nat) (P : IProp GF) [Plain P] :
    uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P)) := by
  -- push the plain step-fupd under the outer update
  have hmono :=
    Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)
      (Q := uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P)))
      (step_fupdN_plain (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
        (n := n) (P := P))
  have htrans :=
    Iris.BaseLogic.fupd_trans (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (E3 := Iris.Set.univ)
      (P := BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P))
  exact hmono.trans htrans

/-- Introduce the `step_fupdN` chain from a plain goal. -/
theorem step_fupdN_intro {W : WsatGS GF} (n : Nat) (P : IProp GF) :
    P ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P := by
  -- iterate fupd/later introductions along the recursion
  induction n with
  | zero =>
      simpa [step_fupdN]
  | succ n ih =>
      have hinner :
          P ⊢ uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) :=
        ih.trans (fupd_intro (W := W) (M := M) (F := F)
          (E := Iris.Set.univ)
          (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))
      have hlater :
          P ⊢ BIBase.later
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) :=
        hinner.trans (later_intro (PROP := IProp GF))
      have houter :
          P ⊢ uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.later
              (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
                (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))) :=
        hlater.trans (fupd_intro (W := W) (M := M) (F := F)
          (E := Iris.Set.univ)
          (P := BIBase.later
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))))
      simpa [step_fupdN] using houter

/-! ## Plain Step-FUpd Rewrites -/

/-- `step_fupdN` commutes with a final `fupd` once a step is taken.

    Coq: `step_fupdN_S_fupd` in `updates.v`. -/
theorem step_fupdN_succ_fupd {W : WsatGS GF} (n : Nat) (P : IProp GF) :
    step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1) P ⊣⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1)
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ P) := by
  -- lift `step_fupd_fupd` through the iterated step-fupd chain
  induction n with
  | zero =>
      simpa [step_fupdN, Iris.BI.step_fupdN, fupd'] using
        (Iris.BI.step_fupd_fupd (PROP := IProp GF) (MASK := Positive)
          (Eo := Iris.Set.univ) (Ei := Iris.Set.univ) (P := P))
  | succ n ih =>
      constructor
      · -- forward direction: apply monotonicity under one outer step
        have hmono :=
          Iris.BI.step_fupd_mono (PROP := IProp GF) (MASK := Positive)
            (Eo := Iris.Set.univ) (Ei := Iris.Set.univ)
            (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
              (n + 1) P)
            (Q := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
              (n + 1)
              (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ P)) ih.1
        simpa [step_fupdN, Iris.BI.step_fupdN, fupd'] using hmono
      · -- backward direction: apply monotonicity under one outer step
        have hmono :=
          Iris.BI.step_fupd_mono (PROP := IProp GF) (MASK := Positive)
            (Eo := Iris.Set.univ) (Ei := Iris.Set.univ)
            (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
              (n + 1)
              (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ P))
            (Q := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W)
              (n + 1) P) ih.2
        simpa [step_fupdN, Iris.BI.step_fupdN, fupd'] using hmono

/-- Strip a final `fupd` inside a non-zero `step_fupdN` chain for plain goals. -/
theorem step_fupdN_strip_fupd {W : WsatGS GF} (n : Nat) (P : IProp GF) [Plain P] :
    step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1)
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty P) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1) P := by
  -- shrink the mask to `⊤`, then use `step_fupdN_succ_fupd`
  have hsubset : Subset maskEmpty Iris.Set.univ := by
    intro _ hfalse; exact False.elim hfalse
  have hmask :
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty P ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ P :=
    Iris.BaseLogic.fupd_plain_mask (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
      hsubset (P := P)
  have hmono :=
    step_fupdN_mono (W := W) (Λ := Λ) (GF := GF) (M := M) (F := F)
      (n := n + 1) hmask
  exact hmono.trans
    (step_fupdN_succ_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
      (W := W) (n := n) (P := P)).2

/-- Lift `step_fupdN_strip_fupd` through an outer `fupd`. -/
theorem fupd_step_fupdN_strip_fupd {W : WsatGS GF} (n : Nat) (P : IProp GF) [Plain P] :
    uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1)
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty P)) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1) P) := by
  -- apply `fupd_mono` to the stripped chain
  exact Iris.BaseLogic.fupd_mono (W := W)
    (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1)
      (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty P))
    (Q := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1) P)
    (step_fupdN_strip_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
      (W := W) (n := n) (P := P))

theorem step_fupdN_mono {W : WsatGS GF} (n : Nat) {P Q : IProp GF} (h : P ⊢ Q) :
    step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n Q := by
  -- recurse on `n`, pushing entailment through the step-fupd chain
  induction n with
  | zero =>
      simpa [step_fupdN] using h
  | succ n ih =>
      -- push the entailment through the inner and outer fupd layers
      have hinner :
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) ⊢
            uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n Q) :=
        Iris.BaseLogic.fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)
          (Q := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n Q) ih
      have hlater :
          BIBase.later
              (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
                (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) ⊢
            BIBase.later
              (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
                (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n Q)) :=
        later_mono (PROP := IProp GF) hinner
      have houter :=
        Iris.BaseLogic.fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)))
          (Q := BIBase.later
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n Q))) hlater
      simpa [step_fupdN] using houter

theorem step_fupdN_frame_r_later {W : WsatGS GF} (n : Nat) (P Q : IProp GF)
    (ih :
      BIBase.sep (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) Q ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n (BIBase.sep P Q)) :
    BIBase.sep
        (BIBase.later
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))) Q ⊢
      BIBase.later
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
            (BIBase.sep P Q))) := by
  -- move `later` across `sep`, then frame under the inner fupd
  have hsep :
      BIBase.sep
          (BIBase.later
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))) Q ⊢
        BIBase.later
          (BIBase.sep
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) Q) :=
    (sep_mono (PROP := IProp GF) .rfl later_intro).trans
      (later_sep (PROP := IProp GF)).2
  have hframe :
      BIBase.sep
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) Q ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
            (BIBase.sep P Q)) := by
    -- frame the inner fupd and apply the induction hypothesis
    refine (Iris.BaseLogic.fupd_frame_r (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)
      (Q := Q)).trans ?_
    exact Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.sep
        (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) Q)
      (Q := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
        (BIBase.sep P Q)) ih
  exact hsep.trans (later_mono (PROP := IProp GF) hframe)

theorem step_fupdN_frame_r {W : WsatGS GF} (n : Nat) (P Q : IProp GF) :
    BIBase.sep (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) Q ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n (BIBase.sep P Q) := by
  induction n with -- push framing under each `step_fupdN` layer
  | zero =>
      -- base: `step_fupdN 0` is identity
      simpa [step_fupdN] using
        (BIBase.Entails.of_eq (PROP := IProp GF)
          (P := BIBase.sep P Q) (Q := BIBase.sep P Q) rfl)
  | succ n ih =>
      have hinside :=
        step_fupdN_frame_r_later (GF := GF) (M := M) (F := F) (W := W)
          (n := n) (P := P) (Q := Q) ih
      have hframe :=
        Iris.BaseLogic.fupd_frame_r (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)))
          (Q := Q)
      have hmono :=
        Iris.BaseLogic.fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.sep
            (BIBase.later
              (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
                (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))) Q)
          (Q := BIBase.later
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n
                (BIBase.sep P Q))))
          hinside
      simpa [step_fupdN] using hframe.trans hmono

/-- Helper: strip `▷^[n]` from `True` using `later_soundness`. -/
theorem laterN_soundness (n : Nat) (P : IProp GF)
    (h : (True : IProp GF) ⊢ BIBase.laterN (PROP := IProp GF) n P) :
    (True : IProp GF) ⊢ P := by
  -- iterate the single-step `later_soundness`
  induction n with
  | zero =>
      simpa [BIBase.laterN] using h
  | succ n ih =>
      have hstep :
          (True : IProp GF) ⊢
            BIBase.later (BIBase.laterN (PROP := IProp GF) n P) := by
        simpa [BIBase.laterN] using h
      have hnext :
          (True : IProp GF) ⊢ BIBase.laterN (PROP := IProp GF) n P :=
        UPred.later_soundness hstep
      exact ih hnext

/-- Helper: turn `▷^[n] ◇ P` into `▷^[n+1] P`. -/
theorem laterN_except0_to_later (n : Nat) (P : IProp GF) :
    BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P) ⊢
      BIBase.laterN (PROP := IProp GF) (n + 1) P := by
  -- push `◇` through `laterN`, then re-associate one extra `▷`
  have hmono :
      BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P) ⊢
        BIBase.laterN (PROP := IProp GF) n (BIBase.later (PROP := IProp GF) P) :=
    laterN_mono (PROP := IProp GF) n (except0_into_later (PROP := IProp GF))
  exact hmono.trans
    (laterN_later (PROP := IProp GF) (n := n) (P := P)).2

/-- Strip a `step_fupdN` chain to obtain `▷^[n] ◇ P`. -/
theorem step_fupdN_soundness_later (P : IProp GF) [Plain P] (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) :
    (BIBase.emp : IProp GF) ⊢
      BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P) := by
  -- lift the plain step-fupd under `fupd`, then apply soundness
  haveI : Plain (BIBase.except0 (PROP := IProp GF) P) := ⟨plain_except0 (P := P)⟩
  haveI :
      Plain (BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P)) :=
    ⟨plain_laterN (P := BIBase.except0 (PROP := IProp GF) P) n⟩
  have hstep :
      ∀ W : WsatGS GF,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P)) := by
    intro W
    exact (h W).trans (step_fupdN_plain_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
      (W := W) (n := n) (P := P))
  exact fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
    (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P))
    (h := hstep)

/-- Soundness step: peel one `step_fupdN` layer and rebuild the chain. -/
theorem step_fupdN_soundness_step (P : IProp GF) [Plain P] (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) (n + 1) P)) :
    (BIBase.emp : IProp GF) ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M)
      (F := F) (W := W) n P := by
  -- strip to `P` and re-introduce the chain
  have hP :
      (BIBase.emp : IProp GF) ⊢ P :=
    step_fupdN_soundness (Λ := Λ) (GF := GF) (M := M) (F := F)
      (P := P) (n := n + 1) (h := h)
  exact hP.trans (step_fupdN_intro (Λ := Λ) (GF := GF) (M := M) (F := F)
    (W := W) (n := n) (P := P))

/-- Soundness: extract a plain proposition from the step-fupd chain. -/
theorem step_fupdN_soundness (P : IProp GF) [Plain P] (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) :
    (BIBase.emp : IProp GF) ⊢ P := by
  -- use plain step-fupd soundness, then strip the remaining laters
  have hlate :
      (BIBase.emp : IProp GF) ⊢
        BIBase.laterN (PROP := IProp GF) n (BIBase.except0 (PROP := IProp GF) P) :=
    step_fupdN_soundness_later (Λ := Λ) (GF := GF) (M := M) (F := F)
      (P := P) (n := n) (h := h)
  have hnext :
      (BIBase.emp : IProp GF) ⊢
        BIBase.laterN (PROP := IProp GF) (n + 1) P :=
    hlate.trans (laterN_except0_to_later (PROP := IProp GF) (n := n) (P := P))
  have htrue :
      (True : IProp GF) ⊢ BIBase.laterN (PROP := IProp GF) (n + 1) P :=
    (true_emp (PROP := IProp GF)).1.trans hnext
  have hP : (True : IProp GF) ⊢ P :=
    laterN_soundness (n := n + 1) (P := P) htrue
  exact (true_emp (PROP := IProp GF)).2.trans hP


end Iris.ProgramLogic
