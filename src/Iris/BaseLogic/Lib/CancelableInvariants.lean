/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.Invariants

/-! # Cancelable Invariants

Reference: `iris/base_logic/lib/cancelable_invariants.v`

Cancelable invariants extend standard invariants with a fractional ownership
token that can be used to *cancel* the invariant, permanently extracting its
content. A cancelable invariant `cinv N γ P` is defined as:

```
cinv N γ P := inv N (P ∗ cinv_excl γ ∨ cinv_own γ 1)
```

where `cinv_own γ p` is a fractional ghost token and `cinv_excl γ` is an
exclusive internal token used to prove `cinv_acc_1`.

## Ghost State

The ghost state uses a product RA:
  `prodR (optionR (exclR unitO)) (optionR fracR)`

- Left component: exclusive token (`cinv_excl`) — internal, used in proofs
- Right component: fractional token (`cinv_own`) — user-facing

## Main Results

- `cinv_persistent` — `cinv N γ P` is persistent (inherits from `inv`)
- `cinv_alloc` — `▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ cinv_own γ 1`
- `cinv_acc` — open with fractional token: `cinv_own γ p ={E,E∖↑N}=∗ ▷ P ∗ cinv_own γ p ∗ (▷ P ={E∖↑N,E}=∗ True)`
- `cinv_cancel` — consume full token: `cinv_own γ 1 ={E}=∗ ▷ P`
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [DecidableEq Positive]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

-- TODO: cinvG requires an ElemG instance for the product RA
-- `prodR (optionR (exclR unitO)) (optionR fracR)`
-- This needs to be added as a variable once the concrete functor is identified.

private abbrev maskDiff (E : Iris.Set Positive) (N : Namespace) :
    Iris.Set Positive :=
  fun x => E x ∧ ¬(nclose N).mem x

section

/-! ## Definitions -/

/-- Fractional ownership token for a cancelable invariant.
Coq: `cinv_own γ p := own γ (None, Some p)` in `cancelable_invariants.v`. -/
noncomputable def cinv_own (_W : WsatGS GF)
    (γ : GName) (p : F) : IProp GF :=
  sorry

/-- Internal exclusive token for cancelable invariant proofs.
Coq: `cinv_excl γ := own γ (Some (Excl ()), None)` in `cancelable_invariants.v`. -/
noncomputable def cinv_excl (_W : WsatGS GF)
    (γ : GName) : IProp GF :=
  sorry

/-- Cancelable invariant: an invariant that can be permanently opened by
consuming the full ownership token.
Coq: `cinv N γ P := inv N (P ∗ cinv_excl γ ∨ cinv_own γ 1)` in
`cancelable_invariants.v`. -/
noncomputable def cinv (W : WsatGS GF)
    (N : Namespace) (γ : GName) (P : IProp GF) : IProp GF :=
  sorry

/-! ## Properties -/

/-- `cinv_own` is timeless.
Coq: `cinv_own_timeless` in `cancelable_invariants.v`. -/
theorem cinv_own_timeless (W : WsatGS GF) (γ : GName) (p : F) :
    Timeless (cinv_own W γ p) :=
  sorry

/-- `cinv` is persistent (inherits from `inv`).
Coq: `cinv_persistent` in `cancelable_invariants.v`. -/
theorem cinv_persistent (W : WsatGS GF) (N : Namespace) (γ : GName)
    (P : IProp GF) :
    Persistent (cinv W N γ P) :=
  sorry

/-- Two full ownership tokens are contradictory.
Coq: `cinv_own_1_l` in `cancelable_invariants.v`. -/
theorem cinv_own_1_l (W : WsatGS GF) (γ : GName) (q : F) :
    cinv_own W γ q ⊢
    BIBase.wand (cinv_own W γ q) (BIBase.pure False : IProp GF) :=
  sorry

/-- Two exclusive tokens are contradictory.
Coq: `cinv_excl_excl` in `cancelable_invariants.v`. -/
theorem cinv_excl_excl (W : WsatGS GF) (γ : GName) :
    cinv_excl W γ ⊢
    BIBase.wand (cinv_excl W γ) (BIBase.pure False : IProp GF) :=
  sorry

/-- Cancelable invariant respects logical equivalence.
Coq: `cinv_iff` in `cancelable_invariants.v`. -/
theorem cinv_iff (W : WsatGS GF) (N : Namespace) (γ : GName)
    (P Q : IProp GF) :
    cinv W N γ P ⊢
    BIBase.wand
      (BIBase.later (BIBase.persistently (BIBase.and (BIBase.wand P Q) (BIBase.wand Q P) : IProp GF)))
      (cinv W N γ Q) :=
  sorry

/-! ## Allocation -/

/-- Allocate a cancelable invariant from a later'd proposition.
Coq: `cinv_alloc` in `cancelable_invariants.v`. -/
theorem cinv_alloc (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (P : IProp GF) :
    BIBase.later P ⊢
    uPred_fupd (M := M) (F := F) W E E
      (BIBase.exists fun (γ : GName) =>
        BIBase.sep (cinv W N γ P) (cinv_own W γ (1 : F)) : IProp GF) :=
  sorry

/-- Allocate a cancelable invariant in the open state.
Coq: `cinv_alloc_open` in `cancelable_invariants.v`. -/
theorem cinv_alloc_open (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (P : IProp GF) (hN : Subset (nclose N).mem E) :
    (BIBase.emp : IProp GF) ⊢
    uPred_fupd (M := M) (F := F) W E (maskDiff E N)
      (BIBase.exists fun (γ : GName) =>
        BIBase.sep (cinv W N γ P)
          (BIBase.sep (cinv_own W γ (1 : F))
            (uPred_fupd (M := M) (F := F) W
              (maskDiff E N) E
              (BIBase.later P))) : IProp GF) :=
  sorry

/-! ## Accessors -/

/-- Open a cancelable invariant with a fractional token.
Returns `▷ P`, the token back, and a closing view shift.
Coq: `cinv_acc` in `cancelable_invariants.v`. -/
theorem cinv_acc (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (γ : GName) (p : F) (P : IProp GF) (hN : Subset (nclose N).mem E) :
    cinv W N γ P ⊢
    BIBase.wand (cinv_own W γ p)
      (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.sep (cinv_own W γ p)
            (uPred_fupd (M := M) (F := F) W
              (maskDiff E N) E
              (BIBase.later P) : IProp GF))) : IProp GF) :=
  sorry

/-- Open a cancelable invariant with a full token non-atomically.
Coq: `cinv_acc_1` in `cancelable_invariants.v`. -/
theorem cinv_acc_1 (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (γ : GName) (P : IProp GF) (hN : Subset (nclose N).mem E) :
    cinv W N γ P ⊢
    BIBase.wand (cinv_own W γ (1 : F))
      (uPred_fupd (M := M) (F := F) W E E
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W E E
              (cinv_own W γ (1 : F))) : IProp GF)) : IProp GF) :=
  sorry

/-- Cancel an invariant: consume the full token to permanently extract `▷ P`.
Coq: `cinv_cancel` in `cancelable_invariants.v`. -/
theorem cinv_cancel (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (γ : GName) (P : IProp GF) (hN : Subset (nclose N).mem E) :
    cinv W N γ P ⊢
    BIBase.wand (cinv_own W γ (1 : F))
      (uPred_fupd (M := M) (F := F) W E E
        (BIBase.later P) : IProp GF) :=
  sorry

end

end Iris.BaseLogic
