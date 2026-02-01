/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.Wsat
import Iris.BI.Updates
import Iris.BI.DerivedLaws
import Iris.BI.DerivedLawsLater

/-! # Fancy Update Modality

Reference: `iris/base_logic/lib/fancy_updates.v`

The fancy update modality `|={E1,E2}=> P` is the central modality of Iris's
base logic. It allows mask-changing updates: temporarily changing the set of
enabled invariants from `E1` to `E2` while establishing `P`.

## Definition

```
fupd E1 E2 P := wsat ∗ ownE E1 -∗ |==> ◇ (wsat ∗ ownE E2 ∗ P)
```

where `◇ P` is the "except-0" modality (`▷ False ∨ P`).

## Main Results

- `fupd_intro_mask` — `E2 ⊆ E1 → P ⊢ |={E1,E2}=> |={E2,E1}=> P`
- `fupd_mono` — monotonicity
- `fupd_trans` — `|={E1,E2}=> |={E2,E3}=> P ⊢ |={E1,E3}=> P`
- `fupd_frame_r` — frame rule
- `fupd_plain_mask` — plain elimination
- `fupd_soundness_no_lc` — adequacy (no later credits)

## Simplifications

This port omits later credit support (`has_lc`, `le_upd_if`, `lcGS`).
All definitions use plain `bupd` rather than `le_upd_if`. This corresponds
to the `HasNoLc` branch in Coq.
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M]
variable [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

section

/-! ## Definition -/

/-- Coerce mask predicates to `CoPset` for `ownE`. -/
abbrev mask (E : Iris.Set Positive) : CoPset := ⟨E⟩

/-- Fix `wsat` to the current ghost state parameters. -/
noncomputable abbrev wsat' (W : WsatGS GF) : IProp GF :=
  wsat (GF := GF) (M := M) (F := F) W

/-- Alias to expose `M`/`F` in typeclass-driven instances. -/
abbrev IPropWsat (GF : BundledGFunctors) (_M : Type _ → Type _) (_F : Type _) : Type _ :=
  IProp GF

/-- Fancy update modality: `fupd E1 E2 P` asserts that starting from enabled
    mask `E1`, we can perform a basic update to reach a state where the enabled
    mask is `E2` and `P` holds (modulo except-0).

    Coq: `uPred_fupd_def` -/
noncomputable def uPred_fupd (_W : WsatGS GF)
    (E1 E2 : Iris.Set Positive) (P : IProp GF) : IProp GF :=
  -- unfold to: wsat ∗ ownE E1 -∗ |==> ◇ (wsat ∗ ownE E2 ∗ P)
  BIBase.wand
    (BIBase.sep (wsat' (M := M) (F := F) _W) (ownE _W (mask E1)))
    (BUpd.bupd <|
      BIBase.except0 <|
        BIBase.sep (wsat' (M := M) (F := F) _W) (BIBase.sep (ownE _W (mask E2)) P))

/-! ## FUpd Instance -/

/-- The `FUpd` instance for `IProp`, wiring `uPred_fupd` into the BI class.

    Coq: `uPred_bi_fupd` -/
noncomputable instance instFUpdIProp
    (M : Type _ → Type _) (F : Type _)
    [UFraction F] [FiniteMap Positive M] [HeapFiniteMap Positive M] [ElemG GF (InvF GF M F)]
    [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)]
    (W : WsatGS GF) :
    FUpd (IPropWsat GF M F) Positive where
  fupd := uPred_fupd (M := M) (F := F) W

/-! ## Helpers -/

omit [ElemG GF (COFE.constOF GSetDisj)] in
/-- Split an enabled mask using subset decomposition. -/
private theorem ownE_split_subset {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (h : Subset E2 E1) :
    ∃ E3 : CoPset,
      ownE W (mask E1) ⊣⊢ BIBase.sep (ownE W (mask E2)) (ownE W E3) := by
  -- use the standard disjoint-union decomposition on `CoPset`
  rcases CoPset.subseteq_disjoint_union (s₁ := mask E2) (s₂ := mask E1) h with
    ⟨E3, hE, hdisj⟩
  refine ⟨E3, ?_⟩
  simpa [hE] using (ownE_op (W := W) (E₁ := mask E2) (E₂ := E3) hdisj)

/-- Build a fancy update when we can rejoin the mask split. -/
private theorem fupd_from_split {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (E3 : CoPset)
    (hE : mask E1 = mask E2 ∪ E3) (hdisj : CoPset.Disjoint (mask E2) E3)
    (P : IProp GF) :
    BIBase.sep (ownE W E3) P ⊢ uPred_fupd (M := M) (F := F) W E2 E1 P := by
  -- reassemble the mask, then wrap with except-0 and bupd
  unfold uPred_fupd
  refine wand_intro ?_
  refine (sep_comm (P := BIBase.sep (ownE W E3) P)
    (Q := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E2)))).1.trans ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E2))
    (R := BIBase.sep (ownE W E3) P)).1.trans ?_
  refine (sep_mono .rfl
    (sep_assoc (P := ownE W (mask E2)) (Q := ownE W E3) (R := P)).2).trans ?_
  have hown : BIBase.sep (ownE W (mask E2)) (ownE W E3) ⊢ ownE W (mask E1) := by
    -- collapse the split mask back to `E1`
    simpa [hE] using (ownE_op (W := W) (E₁ := mask E2) (E₂ := E3) hdisj).2
  refine (sep_mono .rfl (sep_mono hown .rfl)).trans ?_
  exact (except0_intro).trans BIUpdate.intro

/-- Non-expansiveness of `uPred_fupd` in its postcondition. -/
theorem uPred_fupd_ne {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) :
    OFE.NonExpansive (uPred_fupd (M := M) (F := F) W E1 E2) := by
  -- Push non-expansiveness through wand, bupd, except-0, and sep.
  refine ⟨?_⟩
  intro n P Q hPQ
  unfold uPred_fupd
  have hsep :
      BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) P) ≡{n}≡
        BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) Q) :=
    (sep_ne.ne .rfl (sep_ne.ne .rfl hPQ))
  have hex :
      BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) P)) ≡{n}≡
        BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) Q)) :=
    (except0_ne.ne hsep)
  have hbupd :
      BUpd.bupd (PROP := IProp GF)
          (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
            (BIBase.sep (ownE W (mask E2)) P))) ≡{n}≡
        BUpd.bupd (PROP := IProp GF)
          (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
            (BIBase.sep (ownE W (mask E2)) Q))) :=
    (OFE.NonExpansive.ne (f := BUpd.bupd (PROP := IProp GF)) hex)
  exact (wand_ne.ne .rfl hbupd)

/-! ## Mask Introduction -/

/-- Weaken the mask: if `E2 ⊆ E1`, then `P ⊢ |={E1,E2}=> |={E2,E1}=> P`.

    Coq: `fupd_intro_mask` (part of `BiFUpdMixin`) -/
theorem fupd_intro_mask {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (h : Subset E2 E1) (P : IProp GF) :
    P ⊢ uPred_fupd (M := M) (F := F) W E1 E2 (uPred_fupd (M := M) (F := F) W E2 E1 P) := by
  -- split `E1` into `E2` and a disjoint remainder, then build the nested fupd
  rcases CoPset.subseteq_disjoint_union (s₁ := mask E2) (s₂ := mask E1) h with
    ⟨E3, hE, hdisj⟩
  have hsplit : ownE W (mask E1) ⊢ BIBase.sep (ownE W (mask E2)) (ownE W E3) := by
    -- expose the split mask via `ownE_op`
    simpa [hE] using (ownE_op (W := W) (E₁ := mask E2) (E₂ := E3) hdisj).1
  unfold uPred_fupd
  refine wand_intro ?_
  refine (sep_comm (P := P)
    (Q := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E1)))).1.trans ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E1))
    (R := P)).1.trans ?_
  refine (sep_mono .rfl (sep_mono hsplit .rfl)).trans ?_
  refine (sep_mono .rfl
    (sep_assoc (P := ownE W (mask E2)) (Q := ownE W E3) (R := P)).1).trans ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E2))
    (R := BIBase.sep (ownE W E3) P)).2.trans ?_
  have hfupd :
      BIBase.sep (ownE W E3) P ⊢ uPred_fupd (M := M) (F := F) W E2 E1 P :=
    fupd_from_split (W := W) (E1 := E1) (E2 := E2) (E3 := E3) hE hdisj P
  refine (sep_mono .rfl hfupd).trans ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E2))
    (R := uPred_fupd (M := M) (F := F) W E2 E1 P)).1.trans ?_
  exact (except0_intro).trans BIUpdate.intro

/-- Close a mask after opening a subset.

    Coq: `fupd_mask_subseteq` -/
theorem fupd_mask_subseteq {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (h : Subset E2 E1) :
    (True : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W E1 E2
        (uPred_fupd (M := M) (F := F) W E2 E1 (BIBase.emp : IProp GF)) := by
  -- use `fupd_intro_mask` with `emp`, and `True ⊣⊢ emp` in affine logics
  have hemp : (True : IProp GF) ⊢ (BIBase.emp : IProp GF) :=
    (true_emp (PROP := IProp GF)).1
  exact hemp.trans (fupd_intro_mask (W := W) (E1 := E1) (E2 := E2) h (P := BIBase.emp))

/-! ## Mask Framing -/

omit [ElemG GF (COFE.constOF GSetDisj)] in
/-- Split a union mask into disjoint components. -/
private theorem ownE_union_split {W : WsatGS GF}
    (E1 Ef : Iris.Set Positive)
    (hdisj : CoPset.Disjoint (mask E1) (mask Ef)) :
    ownE W (mask (fun x => E1 x ∨ Ef x)) ⊣⊢
      BIBase.sep (ownE W (mask E1)) (ownE W (mask Ef)) := by
  -- use the `ownE_op` equivalence on the union
  simpa using (ownE_op (W := W) (E₁ := mask E1) (E₂ := mask Ef) hdisj)

/-- Frame a mask through `except0` and rejoin the result. -/
private theorem fupd_mask_frame_r_frame {W : WsatGS GF}
    (E2 Ef : Iris.Set Positive) (P : IProp GF) :
    BIBase.sep (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
      (BIBase.sep (ownE W (mask E2)) P))) (ownE W (mask Ef)) ⊢
      BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
        (BIBase.sep (ownE W (mask (fun x => E2 x ∨ Ef x))) P)) := by
  -- push the frame under `except0`, then recombine the masks
  refine (except0_frame_r).trans ?_
  refine except0_mono ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W)
    (Q := BIBase.sep (ownE W (mask E2)) P) (R := ownE W (mask Ef))).1.trans ?_
  refine (sep_mono .rfl
    (sep_right_comm (P := ownE W (mask E2)) (Q := P) (R := ownE W (mask Ef))).1).trans ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W)
    (Q := BIBase.sep (ownE W (mask E2)) (ownE W (mask Ef))) (R := P)).2.trans ?_
  have hdisj :
      BIBase.sep (ownE W (mask E2)) (ownE W (mask Ef)) ⊢
        BIBase.pure (CoPset.Disjoint (mask E2) (mask Ef)) :=
    ownE_disjoint (W := W) (E₁ := mask E2) (E₂ := mask Ef)
  have hjoin :
      BIBase.sep (ownE W (mask E2)) (ownE W (mask Ef)) ⊢
        ownE W (mask (fun x => E2 x ∨ Ef x)) := by
    -- use the derived disjointness to rejoin the masks
    refine pure_elim (PROP := IProp GF)
      (φ := CoPset.Disjoint (mask E2) (mask Ef))
      (Q := BIBase.sep (ownE W (mask E2)) (ownE W (mask Ef)))
      (R := ownE W (mask (fun x => E2 x ∨ Ef x))) ?_ ?_
    · exact hdisj
    · intro hdisj'
      simpa using (ownE_op (W := W) (E₁ := mask E2) (E₂ := mask Ef) hdisj').2
  refine (sep_mono (PROP := IProp GF)
    (sep_mono (PROP := IProp GF) .rfl hjoin) .rfl).trans ?_
  exact (sep_assoc (P := wsat' (M := M) (F := F) W)
    (Q := ownE W (mask (fun x => E2 x ∨ Ef x))) (R := P)).1

/-- Apply a fancy update to its mask resources. -/
private theorem fupd_apply {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (P : IProp GF) :
    BIBase.sep (uPred_fupd (M := M) (F := F) W E1 E2 P)
        (BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E1))) ⊢
      BUpd.bupd (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
        (BIBase.sep (ownE W (mask E2)) P))) := by
  -- eliminate the fupd wand on the shared mask
  unfold uPred_fupd
  exact (wand_elim_l (PROP := IProp GF))

/-- Frame a disjoint mask onto a fancy update. -/
theorem fupd_mask_frame_r {W : WsatGS GF}
    (E1 E2 Ef : Iris.Set Positive) (P : IProp GF)
    (hdisj1 : CoPset.Disjoint (mask E1) (mask Ef)) :
    uPred_fupd (M := M) (F := F) W E1 E2 P ⊢
      uPred_fupd (M := M) (F := F) W
        (fun x => E1 x ∨ Ef x) (fun x => E2 x ∨ Ef x) P := by
  -- Apply the fupd and frame the extra mask through bupd/except-0.
  unfold uPred_fupd
  refine wand_intro ?_
  refine (sep_mono .rfl (sep_mono .rfl
    (ownE_union_split (W := W) (E1 := E1) (Ef := Ef) hdisj1).1)).trans ?_
  refine (sep_mono .rfl
    (sep_assoc (P := wsat' (M := M) (F := F) W)
      (Q := ownE W (mask E1)) (R := ownE W (mask Ef))).2).trans ?_
  refine (sep_assoc (P := uPred_fupd (M := M) (F := F) W E1 E2 P)
    (Q := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E1)))
    (R := ownE W (mask Ef))).2.trans ?_
  refine (sep_mono (fupd_apply (W := W) (E1 := E1) (E2 := E2) (P := P)) .rfl).trans ?_
  refine (BIUpdate.frame_r (PROP := IProp GF)
    (P := BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
      (BIBase.sep (ownE W (mask E2)) P)))
    (R := ownE W (mask Ef))).trans ?_
  have hframe :=
    fupd_mask_frame_r_frame (M := M) (F := F)
      (W := W) (E2 := E2) (Ef := Ef) (P := P)
  exact (BIUpdate.mono (PROP := IProp GF) hframe)

/-! ## Monotonicity and Composition -/

/-- Monotonicity of fancy updates.

    Coq: `fupd_mono` (part of `BiFUpdMixin`) -/
theorem fupd_mono {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) {P Q : IProp GF} (h : P ⊢ Q) :
    uPred_fupd (M := M) (F := F) W E1 E2 P ⊢ uPred_fupd (M := M) (F := F) W E1 E2 Q := by
  -- push monotonicity through wand, bupd, and except-0
  unfold uPred_fupd
  refine wand_mono_r ?_
  refine BIUpdate.mono ?_
  refine except0_mono ?_
  exact sep_mono .rfl (sep_mono .rfl h)

/-- Apply a nested fancy update under except-0. -/
private theorem fupd_except0_bind {W : WsatGS GF}
    (E2 E3 : Iris.Set Positive) (P : IProp GF) :
    BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
      (BIBase.sep (ownE W (mask E2)) (uPred_fupd (M := M) (F := F) W E2 E3 P))) ⊢
      BUpd.bupd (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
        (BIBase.sep (ownE W (mask E3)) P))) := by
  -- use the inner wand, then commute bupd with except-0 and collapse
  have happly :
      BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) (uPred_fupd (M := M) (F := F) W E2 E3 P)) ⊢
        BUpd.bupd (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E3)) P))) := by
    -- reorder to apply the wand
    refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E2))
      (R := uPred_fupd (M := M) (F := F) W E2 E3 P)).2.trans ?_
    refine (sep_comm (P := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E2)))
      (Q := uPred_fupd (M := M) (F := F) W E2 E3 P)).1.trans ?_
    -- unfold the wand and eliminate it
    unfold uPred_fupd
    exact (wand_elim_l (PROP := IProp GF))
  have hstep :
      BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
        (BIBase.sep (ownE W (mask E2)) (uPred_fupd (M := M) (F := F) W E2 E3 P))) ⊢
        BUpd.bupd (BIBase.except0 (BIBase.except0 (BIBase.sep
          (wsat' (M := M) (F := F) W) (BIBase.sep (ownE W (mask E3)) P)))) := by
    -- push `happly` under except-0, then move bupd outward
    refine (except0_mono happly).trans ?_
    simpa using (bupd_except0 (P := BIBase.except0 (BIBase.sep
      (wsat' (M := M) (F := F) W) (BIBase.sep (ownE W (mask E3)) P))))
  exact hstep.trans (BIUpdate.mono except0_idemp.1)

omit [ElemG GF (COFE.constOF GSetDisj)] in
/-- Shrink a top mask to any subset (dropping the remainder). -/
private theorem ownE_from_top {W : WsatGS GF}
    (E : Iris.Set Positive) :
    ownE W (mask Iris.Set.univ) ⊢ ownE W (mask E) := by
  -- split `⊤` into `E` and the disjoint remainder, then drop it
  have hsubset : Subset E Iris.Set.univ := by
    intro _ _; trivial
  rcases ownE_split_subset (W := W) (E1 := Iris.Set.univ) (E2 := E) hsubset with
    ⟨E3, hsplit⟩
  refine (hsplit.1).trans ?_
  exact (sep_elim_l (P := ownE W (mask E)) (Q := ownE W E3))

omit [ElemG GF (COFE.constOF GSetDisj)] in
/-- Shrink a mask along subset by discarding the remainder. -/
private theorem ownE_shrink {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (h : Subset E1 E2) :
    ownE W (mask E2) ⊢ ownE W (mask E1) := by
  -- decompose `E2` into `E1` and the remainder, then drop the remainder
  rcases ownE_split_subset (W := W) (E1 := E2) (E2 := E1) h with
    ⟨E3, hsplit⟩
  refine (hsplit.1).trans ?_
  exact (sep_elim_l (P := ownE W (mask E1)) (Q := ownE W E3))

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
/-- Plainness is preserved by the later modality. -/
private theorem later_plain {P : IProp GF} [Plain P] :
    Plain (BIBase.later P) := by
  -- move plainness under later using `later_plainly`
  refine ⟨(later_mono (Plain.plain (P := P))).trans ?_⟩
  exact (later_plainly (P := P)).1

/-- Transitivity of fancy updates.

    Coq: `fupd_trans` (part of `BiFUpdMixin`) -/
theorem fupd_trans {W : WsatGS GF}
    (E1 E2 E3 : Iris.Set Positive) (P : IProp GF) :
    uPred_fupd (M := M) (F := F) W E1 E2 (uPred_fupd (M := M) (F := F) W E2 E3 P) ⊢ uPred_fupd (M := M) (F := F) W E1 E3 P := by
  -- apply the outer wand, then bind the inner update
  unfold uPred_fupd
  refine wand_intro ?_
  have houter :
      BIBase.sep (uPred_fupd (M := M) (F := F) W E1 E2 (uPred_fupd (M := M) (F := F) W E2 E3 P))
        (BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E1))) ⊢
        BUpd.bupd (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) (uPred_fupd (M := M) (F := F) W E2 E3 P)))) := by
    -- eliminate the outer wand
    unfold uPred_fupd
    exact (wand_elim_l (PROP := IProp GF))
  refine houter.trans ?_
  refine (BIUpdate.mono (PROP := IProp GF)
    (fupd_except0_bind (W := W) (E2 := E2) (E3 := E3) (P := P))).trans ?_
  exact (BIUpdate.trans (PROP := IProp GF))

/-! ## Frame Rule -/

/-- Frame rule for fancy updates: framing preserves disjointness of masks.

    Coq: `fupd_frame_r` (part of `BiFUpdMixin`) -/
theorem fupd_frame_r {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (P Q : IProp GF) :
    BIBase.sep (uPred_fupd (M := M) (F := F) W E1 E2 P) Q ⊢
      uPred_fupd (M := M) (F := F) W E1 E2 (BIBase.sep P Q) := by
  -- frame `Q` through the bupd and except-0 layers
  unfold uPred_fupd
  refine wand_intro ?_
  refine (sep_right_comm (P := uPred_fupd (M := M) (F := F) W E1 E2 P) (Q := Q)
    (R := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E1)))).1.trans ?_
  have happly :
      BIBase.sep (uPred_fupd (M := M) (F := F) W E1 E2 P) (BIBase.sep (wsat' (M := M) (F := F) W)
        (ownE W (mask E1))) ⊢
        BUpd.bupd (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) P))) := by
    -- eliminate the wand of the outer fupd
    unfold uPred_fupd
    exact (wand_elim_l (PROP := IProp GF))
  refine (sep_mono happly .rfl).trans ?_
  refine (BIUpdate.frame_r (PROP := IProp GF)
    (P := BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
      (BIBase.sep (ownE W (mask E2)) P)))
    (R := Q)).trans ?_
  have hframe :
      BIBase.sep (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
        (BIBase.sep (ownE W (mask E2)) P))) Q ⊢
        BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) (BIBase.sep P Q))) := by
    -- move the frame inside except-0, then reassociate
    refine (except0_frame_r).trans ?_
    refine except0_mono ?_
    refine (sep_assoc (P := wsat' (M := M) (F := F) W)
      (Q := BIBase.sep (ownE W (mask E2)) P) (R := Q)).1.trans ?_
    exact (sep_mono .rfl
      (sep_assoc (P := ownE W (mask E2)) (Q := P) (R := Q)).1)
  exact (BIUpdate.mono (PROP := IProp GF) hframe)

/-! ## BUpd / FUpd Interaction -/

/-- Basic updates lift to fancy updates.

    Coq: `uPred_bi_bupd_fupd` -/
theorem bupd_fupd {W : WsatGS GF}
    (E : Iris.Set Positive) (P : IProp GF) :
    BUpd.bupd P ⊢ uPred_fupd (M := M) (F := F) W E E P := by
  -- frame the current mask through the basic update
  unfold uPred_fupd
  refine wand_intro ?_
  refine (sep_comm (P := BUpd.bupd P)
    (Q := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E)))).1.trans ?_
  refine (bupd_frame_l (P := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E)))
    (Q := P)).trans ?_
  have hassoc :
      BIBase.sep (BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E))) P ⊢
        BIBase.sep (wsat' (M := M) (F := F) W) (BIBase.sep (ownE W (mask E)) P) :=
    (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E)) (R := P)).1
  exact (BIUpdate.mono (PROP := IProp GF) (hassoc.trans except0_intro))

/-! ## Mask Weakening -/

/-- Mask shrinking for fancy updates: if `E1 ⊆ E2`, we can weaken to `E1`.

    Coq: `fupd_plain_mask` (from `BiFUpdSbi`) -/
theorem fupd_plain_mask {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (h : Subset E1 E2) (P : IProp GF) :
    uPred_fupd (M := M) (F := F) W E1 E2 P ⊢ uPred_fupd (M := M) (F := F) W E1 E1 P := by
  -- shrink the mask in the postcondition using subset monotonicity
  unfold uPred_fupd
  refine wand_mono_r ?_
  refine BIUpdate.mono ?_
  refine except0_mono ?_
  exact sep_mono .rfl (sep_mono (ownE_shrink (W := W) (E1 := E1) (E2 := E2) h) .rfl)

/-! ## Soundness -/

section

variable [FiniteMapLaws Positive M]

/-- Soundness of the fancy update (no later credits): if for any world
    satisfaction we can establish `P` via a fancy update, then `P` holds
    unconditionally.

    Proof strategy: allocate initial `wsat ∗ ownE ⊤` via `wsat_alloc`,
    unfold `fupd` to basic update, use `bupd_soundness` and
    `later_soundness` to strip modalities.

    Coq: `fupd_soundness_no_lc` -/
theorem fupd_soundness_no_lc
    (E1 E2 : Iris.Set Positive) (P : IProp GF) [Plain P]
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢ uPred_fupd (M := M) (F := F) W E1 E2 P) :
    (BIBase.emp : IProp GF) ⊢ P := by
  -- allocate the initial world, run the fupd, then strip bupd/except-0/later
  have hstep' :
      BIBase.exists (fun W' : WsatGS GF =>
        BIBase.sep (wsat' (M := M) (F := F) W') (ownE W' (mask Iris.Set.univ))) ⊢
        BUpd.bupd (BIBase.later P) := by
    -- pick the world, apply the fancy update, and map to `▷ P`
    refine exists_elim ?_
    intro W'
    have hmask :
        BIBase.sep (wsat' (M := M) (F := F) W') (ownE W' (mask Iris.Set.univ)) ⊢
          BIBase.sep (wsat' (M := M) (F := F) W') (ownE W' (mask E1)) := by
      -- shrink the top mask to `E1`
      exact sep_mono .rfl (ownE_from_top (W := W') E1)
    have happly :
        BIBase.sep (wsat' (M := M) (F := F) W') (ownE W' (mask E1)) ⊢
          BIBase.sep (uPred_fupd (M := M) (F := F) W' E1 E2 P)
            (BIBase.sep (wsat' (M := M) (F := F) W') (ownE W' (mask E1))) := by
      -- obtain the fupd from `emp` and frame the current resources
      refine (emp_sep.2).trans ?_
      exact sep_mono (h W') .rfl
    have hupd :
        BIBase.sep (wsat' (M := M) (F := F) W') (ownE W' (mask E1)) ⊢
          BUpd.bupd (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W')
            (BIBase.sep (ownE W' (mask E2)) P))) := by
      -- apply the wand of the fancy update
      refine happly.trans ?_
      unfold uPred_fupd
      exact (wand_elim_l (PROP := IProp GF))
    have hstrip :
        BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W')
          (BIBase.sep (ownE W' (mask E2)) P)) ⊢ BIBase.later P := by
      -- drop `wsat`/`ownE` and turn except-0 into later
      refine (except0_into_later (PROP := IProp GF)).trans ?_
      refine later_mono ?_
      refine (sep_assoc (P := wsat' (M := M) (F := F) W') (Q := ownE W' (mask E2))
        (R := P)).2.trans ?_
      exact sep_elim_r (P := BIBase.sep (wsat' (M := M) (F := F) W')
        (ownE W' (mask E2))) (Q := P)
    refine (hmask.trans hupd).trans ?_
    exact BIUpdate.mono hstrip
  have hstep :
      (BIBase.emp : IProp GF) ⊢ BUpd.bupd (BIBase.later P) := by
    -- allocate the world under bupd, then collapse nested updates
    refine (wsat_alloc (GF := GF) (M := M) (F := F)).trans ?_
    refine (BIUpdate.mono hstep').trans ?_
    exact BIUpdate.trans
  haveI : Plain (BIBase.later P) := later_plain (P := P)
  have hlate : (BIBase.emp : IProp GF) ⊢ BIBase.later P := hstep.trans bupd_elim
  have htrue : (True : IProp GF) ⊢ BIBase.later P :=
    (true_emp (PROP := IProp GF)).1.trans hlate
  have hP : (True : IProp GF) ⊢ P := UPred.later_soundness htrue
  exact (true_emp (PROP := IProp GF)).2.trans hP

/-- Step-indexed fancy update soundness (no later credits).

    Coq: `step_fupdN_soundness_no_lc` -/
theorem step_fupdN_soundness_no_lc
    (P : IProp GF) [Plain P] (_n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢ uPred_fupd (M := M) (F := F) W Iris.Set.univ (fun _ => False) P) :
    (BIBase.emp : IProp GF) ⊢ P := by
  -- specialize soundness to `⊤`/`∅` masks
  exact fupd_soundness_no_lc (E1 := Iris.Set.univ) (E2 := fun _ => False) (P := P) h

end

end

end Iris.BaseLogic
