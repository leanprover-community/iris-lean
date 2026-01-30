/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.Wsat
import Iris.BI.Updates
import Iris.BI.DerivedLaws

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

/-! ## Definition -/

/-- Fancy update modality: `fupd E1 E2 P` asserts that starting from enabled
    mask `E1`, we can perform a basic update to reach a state where the enabled
    mask is `E2` and `P` holds (modulo except-0).

    Coq: `uPred_fupd_def` -/
noncomputable def uPred_fupd {GF : BundledGFunctors} (_W : WsatGS GF)
    (E1 E2 : Iris.Set Positive) (P : IProp GF) : IProp GF :=
  sorry

/-! ## FUpd Instance -/

/-- The `FUpd` instance for `IProp`, wiring `uPred_fupd` into the BI class.

    Coq: `uPred_bi_fupd` -/
noncomputable instance instFUpdIProp {GF : BundledGFunctors} (W : WsatGS GF) :
    FUpd (IProp GF) Positive where
  fupd := uPred_fupd W

/-! ## Mask Introduction -/

/-- Weaken the mask: if `E2 ⊆ E1`, then `P ⊢ |={E1,E2}=> |={E2,E1}=> P`.

    Coq: `fupd_intro_mask` (part of `BiFUpdMixin`) -/
theorem fupd_intro_mask {GF : BundledGFunctors} {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (h : Subset E2 E1) (P : IProp GF) :
    P ⊢ uPred_fupd W E1 E2 (uPred_fupd W E2 E1 P) := sorry

/-! ## Monotonicity and Composition -/

/-- Monotonicity of fancy updates.

    Coq: `fupd_mono` (part of `BiFUpdMixin`) -/
theorem fupd_mono {GF : BundledGFunctors} {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) {P Q : IProp GF} (h : P ⊢ Q) :
    uPred_fupd W E1 E2 P ⊢ uPred_fupd W E1 E2 Q := sorry

/-- Transitivity of fancy updates.

    Coq: `fupd_trans` (part of `BiFUpdMixin`) -/
theorem fupd_trans {GF : BundledGFunctors} {W : WsatGS GF}
    (E1 E2 E3 : Iris.Set Positive) (P : IProp GF) :
    uPred_fupd W E1 E2 (uPred_fupd W E2 E3 P) ⊢ uPred_fupd W E1 E3 P := sorry

/-! ## Frame Rule -/

/-- Frame rule for fancy updates: framing preserves disjointness of masks.

    Coq: `fupd_frame_r` (part of `BiFUpdMixin`) -/
theorem fupd_frame_r {GF : BundledGFunctors} {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (P Q : IProp GF) :
    BIBase.sep (uPred_fupd W E1 E2 P) Q ⊢
      uPred_fupd W E1 E2 (BIBase.sep P Q) := sorry

/-! ## BUpd / FUpd Interaction -/

/-- Basic updates lift to fancy updates.

    Coq: `uPred_bi_bupd_fupd` -/
theorem bupd_fupd {GF : BundledGFunctors} {W : WsatGS GF}
    (E : Iris.Set Positive) (P : IProp GF) :
    BUpd.bupd P ⊢ uPred_fupd W E E P := sorry

/-! ## Plain Modality Interaction -/

/-- Fancy updates on plain propositions can eliminate the mask change.

    Coq: `fupd_plain_mask` (from `BiFUpdSbi`) -/
theorem fupd_plain_mask {GF : BundledGFunctors} {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (P : IProp GF)
    (hplain : Plainly.plainly P ⊢ P) :
    uPred_fupd W E1 E2 P ⊢ uPred_fupd W E1 E1 P := sorry

/-! ## Soundness -/

/-- Soundness of the fancy update (no later credits): if for any world
    satisfaction we can establish `P` via a fancy update, then `P` holds
    unconditionally.

    Proof strategy: allocate initial `wsat ∗ ownE ⊤` via `wsat_alloc`,
    unfold `fupd` to basic update, use `bupd_soundness` and
    `later_soundness` to strip modalities.

    Coq: `fupd_soundness_no_lc` -/
theorem fupd_soundness_no_lc {GF : BundledGFunctors}
    (E1 E2 : Iris.Set Positive) (P : IProp GF)
    (hplain : Plainly.plainly P ⊢ P)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢ uPred_fupd W E1 E2 P) :
    (BIBase.emp : IProp GF) ⊢ P := sorry

/-- Step-indexed fancy update soundness (no later credits).

    Coq: `step_fupdN_soundness_no_lc` -/
theorem step_fupdN_soundness_no_lc {GF : BundledGFunctors}
    (P : IProp GF) (hplain : Plainly.plainly P ⊢ P) (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢ uPred_fupd W Iris.Set.univ (fun _ => False) P) :
    (BIBase.emp : IProp GF) ⊢ P := sorry

end Iris.BaseLogic
