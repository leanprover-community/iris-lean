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

/-- Strip one `fupd` layer to obtain a `later`-guarded step. -/
theorem step_fupdN_soundness_later (P : IProp GF) (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M)
        (F := F) (W := W) (n + 1) P) :
    (BIBase.emp : IProp GF) ⊢
      BIBase.later
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) := by
  -- TODO: port Coq step-fupd soundness (use step_fupdN_plain + fupd soundness)
  -- This proof currently needs the Coq-style plain step-fupd chain.
  sorry

/-- Soundness step: peel one `fupd`/`▷` layer. -/
theorem step_fupdN_soundness_step (P : IProp GF) (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M)
        (F := F) (W := W) (n + 1) P) :
    (BIBase.emp : IProp GF) ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M)
      (F := F) (W := W) n P := by
  -- TODO: peel one step-fupd layer using the updated soundness lemma.
  sorry

theorem step_fupdN_soundness (P : IProp GF) (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) :
    (BIBase.emp : IProp GF) ⊢ P := by
  -- TODO: rework to Coq-style step-fupd soundness once `step_fupdN_plain` is available.
  sorry


end Iris.ProgramLogic
