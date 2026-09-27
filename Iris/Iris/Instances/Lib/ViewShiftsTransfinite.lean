/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.Lib.InvariantsTransfinite

/-! # View shifts over arbitrary step-indices (Transfinite Iris)

This file ports `theories/base_logic/lib/viewshifts.v` for the credit-free fancy update of
`Iris.Instances.Lib.FUpdTransfinite`. The view shift `vs E₁ E₂ P Q` (Rocq: `P ={E1,E2}=> Q`) is the
persistent fancy-update wand `□ (P -∗ |={E₁,E₂}=> Q)`. We omit the binary notation, which would
clash with the prefix fancy update notation.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris OFE BI Std.LawfulSet

variable {GF : BundledGFunctors} [W : WsatGS GF]

/-- The view shift (Rocq: `vs`, notation `P ={E1,E2}=> Q`). -/
def vs (E₁ E₂ : CoPset) (P Q : IProp GF) : IProp GF :=
  iprop(□ (P -∗ |={E₁,E₂}=> Q))

instance vs_persistent (E₁ E₂ : CoPset) (P Q : IProp GF) : Persistent (vs E₁ E₂ P Q) := by
  unfold vs; infer_instance

/-- Rocq: `vs_ne`. -/
theorem vs_ne (E₁ E₂ : CoPset) {n} {P P' Q Q' : IProp GF} (hP : P ≡{n}≡ P') (hQ : Q ≡{n}≡ Q') :
    vs E₁ E₂ P Q ≡{n}≡ vs E₁ E₂ P' Q' :=
  intuitionistically_ne.ne (wand_ne.ne hP (BIFUpdate.ne.ne hQ))

/-- Rocq: `vs_mono`. -/
theorem vs_mono {E₁ E₂ : CoPset} {P P' Q Q' : IProp GF} (hP : P ⊢ P') (hQ : Q' ⊢ Q) :
    vs E₁ E₂ P' Q' ⊢ vs E₁ E₂ P Q :=
  intuitionistically_mono (wand_mono hP (BIFUpdate.mono hQ))

/-- Rocq: `vs_false_elim`. -/
theorem vs_false_elim (E₁ E₂ : CoPset) (P : IProp GF) : ⊢ vs E₁ E₂ iprop(False) P := by
  unfold vs
  iintro !> H
  iexfalso
  iexact H

/-- Rocq: `vs_timeless`. -/
theorem vs_timeless (E : CoPset) (P : IProp GF) [Timeless P] : ⊢ vs E E iprop(▷ P) P := by
  unfold vs
  iintro !> >HP
  imodintro
  iexact HP

/-- Rocq: `vs_transitive`. -/
theorem vs_transitive {E₁ E₂ E₃ : CoPset} {P Q R : IProp GF} :
    vs E₁ E₂ P Q ∧ vs E₂ E₃ Q R ⊢ vs E₁ E₃ P R := by
  unfold vs
  iintro #⟨HvsP, HvsQ⟩ !> HP
  imod HvsP $$ HP with HQ
  iapply HvsQ $$ HQ

/-- Rocq: `vs_reflexive`. -/
theorem vs_reflexive (E : CoPset) (P : IProp GF) : ⊢ vs E E P P := by
  unfold vs
  iintro !> HP
  imodintro
  iexact HP

/-- Rocq: `vs_impl`. -/
theorem vs_impl (E : CoPset) (P Q : IProp GF) : □ (P → Q) ⊢ vs E E P Q := by
  unfold vs
  iintro #HPQ !> HP
  imodintro
  iapply HPQ $$ HP

/-- Rocq: `vs_frame_l`. -/
theorem vs_frame_l {E₁ E₂ : CoPset} {P Q R : IProp GF} :
    vs E₁ E₂ P Q ⊢ vs E₁ E₂ iprop(R ∗ P) iprop(R ∗ Q) := by
  unfold vs
  iintro #Hvs !> ⟨HR, HP⟩
  imod Hvs $$ HP with HQ
  imodintro
  iframe

/-- Rocq: `vs_frame_r`. -/
theorem vs_frame_r {E₁ E₂ : CoPset} {P Q R : IProp GF} :
    vs E₁ E₂ P Q ⊢ vs E₁ E₂ iprop(P ∗ R) iprop(Q ∗ R) := by
  unfold vs
  iintro #Hvs !> ⟨HP, HR⟩
  imod Hvs $$ HP with HQ
  imodintro
  iframe

/-- Rocq: `vs_mask_frame_r`. -/
theorem vs_mask_frame_r {E₁ E₂ Ef : CoPset} {P Q : IProp GF} (h : E₁ ## Ef) :
    vs E₁ E₂ P Q ⊢ vs (E₁ ∪ Ef) (E₂ ∪ Ef) P Q := by
  unfold vs
  iintro #Hvs !> HP
  iapply fupd_mask_frame_right h
  iapply Hvs $$ HP

/-- Rocq: `vs_inv`. -/
theorem vs_inv {N : Namespace} {E : CoPset} {P Q R : IProp GF} (h : ↑N ⊆ E) :
    inv N R ∗ vs (E \ ↑N) (E \ ↑N) iprop(▷ R ∗ P) iprop(▷ R ∗ Q) ⊢ vs E E P Q := by
  unfold vs
  iintro #⟨Hinv, Hvs⟩ !> HP
  imod inv_acc h $$ Hinv with ⟨HR, Hclose⟩
  imod Hvs $$ [HR HP] with ⟨HR, HQ⟩
  · iframe
  imod Hclose $$ HR with -
  imodintro
  iexact HQ

/-- Rocq: `vs_alloc`. -/
theorem vs_alloc (N : Namespace) (P : IProp GF) : ⊢ vs ↑N ↑N iprop(▷ P) (inv N P) := by
  unfold vs
  iintro !> HP
  iapply inv_alloc $$ HP

/-- Rocq: `wand_fupd_alt`. -/
theorem wand_fupd_alt {E₁ E₂ : CoPset} {P Q : IProp GF} :
    (P ={E₁,E₂}=∗ Q) ⊣⊢ ∃ R, R ∗ vs E₁ E₂ iprop(P ∗ R) Q := by
  unfold vs
  constructor
  · iintro H
    iexists iprop(P ={E₁,E₂}=∗ Q)
    iframe H
    iintro !> ⟨HP, H⟩
    iapply H $$ HP
  · iintro ⟨%R, HR, #Hvs⟩ HP
    iapply Hvs
    iframe

end Iris.Transfinite
