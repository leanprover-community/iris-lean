/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Instances.IProp.Instance
import Iris.Algebra.CoPset
import Iris.BI.BigOp

/-! # World Satisfaction

Reference: `iris/base_logic/lib/wsat.v`

World satisfaction (`wsat`) is the central invariant of the Iris base logic.
It asserts ownership of a map from invariant names to propositions, together
with the bookkeeping that each invariant is either *open* (its content has
been taken out, tracked by a disabled token `ownD`) or *closed* (the content
is still inside, tracked by an enabled token `ownE`).

The three ownership connectives are:
- `ownI i P` — invariant `i` is registered with content `P` (persistent)
- `ownE E` — the caller holds the enabled mask `E` (a set of invariant names)
- `ownD E` — the caller holds the disabled tokens `E`

The open/close lemmas (`ownI_open`, `ownI_close`) allow temporarily
extracting `▷ P` from a closed invariant and putting it back, exchanging
enabled and disabled tokens in the process. This is the engine behind fancy
updates and the `iInv` tactic.

## Main Definitions

- `WsatGS` — ghost state names for the three ghost cells
- `ownI`, `ownE`, `ownD` — ownership connectives
- `wsat` — world satisfaction assertion

## Main Results

- `ownE_op`, `ownD_op` — disjoint union splits
- `ownE_singleton_twice`, `ownD_singleton_twice` — no duplication
- `ownI_open` — open an invariant: extract `▷ P`, get disabled token
- `ownI_close` — close an invariant: return `▷ P`, get enabled token back
- `ownI_alloc` — allocate a fresh invariant name
- `wsat_alloc` — allocate the initial world satisfaction
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI

/-! ## Ghost State Configuration -/

/-- Ghost state names for world satisfaction.
    Tracks the three ghost cells: invariant map, enabled mask, disabled tokens. -/
structure WsatGS (GF : BundledGFunctors) where
  /-- Ghost name for the invariant map (HeapView auth over agree ∘ later ∘ iProp) -/
  invariant_name : GName
  /-- Ghost name for the enabled mask (CoPsetDisj) -/
  enabled_name : GName
  /-- Ghost name for the disabled tokens (GSetDisj) -/
  disabled_name : GName

variable {GF : BundledGFunctors} (W : WsatGS GF)

/-! ## Ownership Connectives -/

/-- Invariant ownership: `ownI i P` asserts that invariant `i` is registered
    with content `P`. This is persistent — once registered, an invariant
    exists forever. -/
noncomputable def ownI (_W : WsatGS GF) (i : Positive) (P : IProp GF) : IProp GF := sorry

/-- Enabled mask ownership: `ownE E` asserts the caller holds the right to
    open invariants in the set `E`. Implemented via the `CoPsetDisj` CMRA. -/
noncomputable def ownE (_W : WsatGS GF) (E : CoPset) : IProp GF := sorry

/-- Disabled token ownership: `ownD E` asserts the caller holds disabled
    tokens for invariants in `E`. Implemented via the `GSetDisj` CMRA. -/
noncomputable def ownD (_W : WsatGS GF) (E : GSet) : IProp GF := sorry

/-! ## World Satisfaction -/

/-- World satisfaction: asserts existence of an invariant map `I` such that
    the caller owns the authoritative view of `I`, and for each invariant
    `i ↦ Q` in `I`, either `Q` is closed (content `▷ Q` present with a
    disabled token) or open (an enabled token is present).

    ```
    wsat := ∃ I : gmap positive (iProp Σ),
      own γ_inv (gmap_view_auth 1 I) ∗
      [∗ map] i ↦ Q ∈ I, (▷ Q ∗ ownD {[i]}) ∨ ownE {[i]}
    ``` -/
noncomputable def wsat (_W : WsatGS GF) : IProp GF := sorry

/-! ## Enabled Mask Properties -/

/-- Allocate an empty enabled mask. -/
theorem ownE_empty : (BIBase.emp : IProp GF) ⊢ BUpd.bupd (ownE W ∅) := sorry

/-- Disjoint union of enabled masks splits into separating conjunction. -/
theorem ownE_op (E₁ E₂ : CoPset) (h : E₁.Disjoint E₂) :
    ownE W (E₁.union E₂) ⊣⊢ BIBase.sep (ownE W E₁) (ownE W E₂) := sorry

/-- Enabled masks in separating conjunction must be disjoint. -/
theorem ownE_disjoint (E₁ E₂ : CoPset) :
    BIBase.sep (ownE W E₁) (ownE W E₂) ⊢
      BIBase.pure (E₁.Disjoint E₂) := sorry

/-- Cannot own the same singleton enabled token twice. -/
theorem ownE_singleton_twice (i : Positive) :
    BIBase.sep (ownE W (CoPset.singleton i)) (ownE W (CoPset.singleton i)) ⊢
      (BIBase.pure False : IProp GF) := sorry

/-! ## Disabled Token Properties -/

/-- Allocate empty disabled tokens. -/
theorem ownD_empty : (BIBase.emp : IProp GF) ⊢ BUpd.bupd (ownD W ∅) := sorry

/-- Disjoint union of disabled tokens splits into separating conjunction. -/
theorem ownD_op (E₁ E₂ : GSet) (h : E₁.Disjoint E₂) :
    ownD W (E₁.union E₂) ⊣⊢ BIBase.sep (ownD W E₁) (ownD W E₂) := sorry

/-- Disabled tokens in separating conjunction must be disjoint. -/
theorem ownD_disjoint (E₁ E₂ : GSet) :
    BIBase.sep (ownD W E₁) (ownD W E₂) ⊢
      BIBase.pure (E₁.Disjoint E₂) := sorry

/-- Cannot own the same singleton disabled token twice. -/
theorem ownD_singleton_twice (i : Positive) :
    BIBase.sep (ownD W (GSet.singleton i)) (ownD W (GSet.singleton i)) ⊢
      (BIBase.pure False : IProp GF) := sorry

/-! ## Invariant Properties -/

/-- `ownI` is persistent. -/
theorem ownI_persistent (i : Positive) (P : IProp GF) :
    ownI W i P ⊢ BIBase.persistently (ownI W i P) := sorry

/-! ## Open and Close -/

/-- Open an invariant: given world satisfaction, invariant ownership, and
    the enabled token for `i`, extract the later'd content and a disabled
    token.

    Proof strategy (from Coq `wsat.v`):
    1. Unfold `wsat` to get the invariant map `I` and auth fragment
    2. Use `invariant_lookup` to find `Q` with `I !! i = Some Q` and `▷(Q ≡ P)`
    3. Use `big_sepM_delete` to extract the entry for `i`
    4. The entry is `(▷ Q ∗ ownD {[i]}) ∨ ownE {[i]}` — eliminate the disjunction
    5. In the `ownE` case, derive contradiction from `ownE_singleton_twice`
    6. In the `▷ Q ∗ ownD` case, rewrite `Q` to `P` and reassemble `wsat` -/
theorem ownI_open (i : Positive) (P : IProp GF) :
    BIBase.sep (BIBase.sep (wsat W) (ownI W i P)) (ownE W (CoPset.singleton i)) ⊢
      BIBase.sep (BIBase.sep (wsat W) (BIBase.later P)) (ownD W (GSet.singleton i)) := sorry

/-- Close an invariant: given world satisfaction, invariant ownership,
    the later'd content, and the disabled token, return the enabled token.

    Proof strategy: dual of `ownI_open` — put the content back into the big sep,
    swap disabled for enabled. -/
theorem ownI_close (i : Positive) (P : IProp GF) :
    BIBase.sep (BIBase.sep (BIBase.sep (wsat W) (ownI W i P)) (BIBase.later P))
      (ownD W (GSet.singleton i)) ⊢
      BIBase.sep (wsat W) (ownE W (CoPset.singleton i)) := sorry

/-! ## Allocation -/

/-- Allocate a fresh invariant name satisfying predicate `φ`.
    Given world satisfaction and `▷ P`, produces a fresh name `i` with
    `φ i`, updated world satisfaction, and `ownI i P`. -/
theorem ownI_alloc (φ : Positive → Prop) (P : IProp GF)
    (hfresh : ∀ E : GSet, ∃ i, ¬E.mem i ∧ φ i) :
    BIBase.sep (wsat W) (BIBase.later P) ⊢
      BUpd.bupd (BIBase.exists fun i =>
        BIBase.sep (BIBase.pure (φ i))
          (BIBase.sep (wsat W) (ownI W i P))) := sorry

/-- Allocate a fresh invariant and immediately open it.
    Returns the fresh name, a closing wand, `ownI`, and `ownD`. -/
theorem ownI_alloc_open (φ : Positive → Prop) (P : IProp GF)
    (hfresh : ∀ E : GSet, ∃ i, ¬E.mem i ∧ φ i) :
    BUpd.bupd (wsat W) ⊢
      BUpd.bupd (BIBase.exists fun i =>
        BIBase.sep (BIBase.pure (φ i))
          (BIBase.sep (BIBase.wand (ownE W (CoPset.singleton i)) (wsat W))
            (BIBase.sep (ownI W i P) (ownD W (GSet.singleton i))))) := sorry

/-! ## Initial World -/

/-- Allocate the initial world satisfaction and top-level enabled mask.
    This is the entry point: from nothing, produce `wsat ∗ ownE ⊤`. -/
theorem wsat_alloc :
    (BIBase.emp : IProp GF) ⊢
      BUpd.bupd (BIBase.exists fun W' : WsatGS GF =>
        BIBase.sep (wsat W') (ownE W' CoPset.top)) := sorry

end Iris.BaseLogic
