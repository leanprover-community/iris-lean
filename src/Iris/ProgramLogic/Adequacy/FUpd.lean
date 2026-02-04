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
  -- iterate a single `fupd`/`▷` layer `n` times
  match n with
  | 0 => P
  | n + 1 =>
      fupd' (W := W) (M := M) (F := F) Iris.Set.univ Iris.Set.univ <|
        BIBase.later (step_fupdN (Λ := Λ) (W := W) n P)

theorem step_fupdN_mono {W : WsatGS GF} (n : Nat) {P Q : IProp GF} (h : P ⊢ Q) :
    step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n Q := by
  -- recurse on `n`, pushing entailment under fupd/later
  induction n with
  | zero =>
      simpa [step_fupdN] using h
  | succ n ih =>
      have hl :
          BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) ⊢
            BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n Q) :=
        later_mono (PROP := IProp GF) ih
      simpa [step_fupdN] using
        (Iris.BaseLogic.fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))
          (Q := BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n Q)) hl)

theorem step_fupdN_frame_r_later {W : WsatGS GF} (n : Nat) (P Q : IProp GF)
    (ih :
      BIBase.sep (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) Q ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n (BIBase.sep P Q)) :
    BIBase.sep
        (BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) Q ⊢
      BIBase.later
        (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n (BIBase.sep P Q)) := by
  have hsep : -- move `later` across `sep` before applying the induction hypothesis
      BIBase.sep
          (BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) Q ⊢
        BIBase.later
          (BIBase.sep
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) Q) :=
    (sep_mono (PROP := IProp GF) .rfl later_intro).trans
      (later_sep (PROP := IProp GF)).2
  exact hsep.trans (later_mono (PROP := IProp GF) ih)

theorem step_fupdN_frame_r {W : WsatGS GF} (n : Nat) (P Q : IProp GF) :
    BIBase.sep (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) Q ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n (BIBase.sep P Q) := by
  induction n with -- push framing under each `step_fupdN` layer
  | zero =>
      simpa [step_fupdN] using
        (BIBase.Entails.of_eq (PROP := IProp GF)
          (P := BIBase.sep P Q) (Q := BIBase.sep P Q) rfl)
  | succ n ih =>
      have hinside :=
        step_fupdN_frame_r_later  (GF := GF) (M := M) (F := F) (W := W)
          (n := n) (P := P) (Q := Q) ih
      have hframe :=
        Iris.BaseLogic.fupd_frame_r (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))
          (Q := Q)
      have hmono :=
        Iris.BaseLogic.fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.sep
            (BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) Q)
          (Q := BIBase.later
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n (BIBase.sep P Q)))
          hinside
      simpa [step_fupdN] using hframe.trans hmono

/-- Strip one `fupd` layer to obtain a `later`-guarded step. -/
theorem step_fupdN_soundness_later (P : IProp GF) (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M)
        (F := F) (W := W) (n + 1) P) :
    (BIBase.emp : IProp GF) ⊢
      BIBase.later
        (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) := by
  -- specialize soundness to the `step_fupdN` successor shape
  have hmono :
      ∀ W : WsatGS GF,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.later
              (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P)) := by
    intro W
    simpa [step_fupdN] using (h W)
  exact fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
    (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := BIBase.later
      (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P))
    (h := hmono)

/-- Soundness step: peel one `fupd`/`▷` layer. -/
theorem step_fupdN_soundness_step (P : IProp GF) (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M)
        (F := F) (W := W) (n + 1) P) :
    (BIBase.emp : IProp GF) ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M)
      (F := F) (W := W) n P := by
  -- lift to `True`, apply later soundness, then return to `emp`
  have hlate := step_fupdN_soundness_later  (GF := GF) (M := M) (F := F) (W := W)
    (P := P) (n := n) (h := h)
  have htrue :=
    (true_emp (PROP := IProp GF)).1.trans hlate
  have hpred :=
    UPred.later_soundness htrue
  exact (true_emp (PROP := IProp GF)).2.trans hpred

theorem step_fupdN_soundness (P : IProp GF) (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P) :
    (BIBase.emp : IProp GF) ⊢ P := by
  -- peel off `fupd`/`▷` layers, then apply the induction hypothesis
  induction n with
  | zero =>
      classical
      -- choose any world witness to specialize the `∀ W` hypothesis
      let W0 : WsatGS GF := ⟨0, 0, 0⟩
      simpa [step_fupdN] using (h W0)
  | succ n ih =>
      have hpred' :
          ∀ W : WsatGS GF,
            (BIBase.emp : IProp GF) ⊢
              step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) n P := by
        intro W
        exact step_fupdN_soundness_step  (GF := GF) (M := M) (F := F) (W := W)
          (P := P) (n := n) (h := h)
      exact ih (h := hpred')


end Iris.ProgramLogic
