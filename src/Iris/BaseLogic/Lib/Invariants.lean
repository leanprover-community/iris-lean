/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.FancyUpdates
import Iris.Std.Namespace

/-! # Invariants

Reference: `iris/base_logic/lib/invariants.v`

Invariants are the main user-facing mechanism for shared ownership in Iris.
An invariant `inv N P` asserts that proposition `P` is maintained as an
invariant registered under namespace `N`. It is a *derived* definition built
on top of fancy updates and world satisfaction — not a new primitive.

## Definition

```
inv N P := □ ∀ E, ⌜↑N ⊆ E⌝ → |={E, E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N, E}=∗ True)
```

## Main Results

- `inv_persistent` — `inv N P` is persistent
- `inv_alloc` — `▷ P ={E}=∗ inv N P`
- `inv_alloc_open` — allocate and immediately open
- `inv_acc` — `↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True)`
- `inv_acc_timeless` — strip `▷` when `P` is timeless
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

/-- Mask difference: `E ∖ ↑N` as a set predicate. -/
private abbrev maskDiff (E : Iris.Set Positive) (N : Namespace) :
    Iris.Set Positive :=
  fun x => E x ∧ ¬(nclose N).mem x

/-! ## Internal Model -/

/-- Internal invariant ownership: existential over a name in the namespace.

    Coq: `own_inv` -/
noncomputable def own_inv (_W : WsatGS GF)
    (N : Namespace) (P : IProp GF) : IProp GF := sorry

/-- Access an internal invariant: open it to get `▷ P` and a closing view shift.

    Coq: `own_inv_acc` -/
theorem own_inv_acc {W : WsatGS GF}
    (N : Namespace) (E : Iris.Set Positive) (P : IProp GF)
    (h : Subset (nclose N).mem E) :
    own_inv W N P ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) := sorry

/-! ## Definition -/

/-- Semantic invariant: `inv N P` asserts that `P` is maintained as an
    invariant under namespace `N`. This is persistent — once allocated,
    the invariant exists forever.

    Coq: `inv_def` -/
noncomputable def inv (_W : WsatGS GF)
    (N : Namespace) (P : IProp GF) : IProp GF := sorry

/-! ## Properties -/

/-- `inv N P` is persistent.

    Coq: `inv_persistent` -/
theorem inv_persistent {W : WsatGS GF}
    (N : Namespace) (P : IProp GF) :
    inv W N P ⊢ BIBase.persistently (inv W N P) := sorry

/-! ## Allocation -/

/-- Allocate a new invariant from `▷ P`.

    Proof strategy: use `ownI_alloc` from wsat to get a fresh invariant name
    in `↑N`, then pack behind `□` to form `inv N P`.

    Coq: `inv_alloc` -/
theorem inv_alloc {W : WsatGS GF}
    (N : Namespace) (E : Iris.Set Positive) (P : IProp GF) :
    BIBase.later P ⊢ uPred_fupd (M := M) (F := F) W E E (inv W N P) := sorry

/-- Allocate an invariant and immediately open it.

    Coq: `inv_alloc_open` -/
theorem inv_alloc_open {W : WsatGS GF}
    (N : Namespace) (E : Iris.Set Positive) (P : IProp GF)
    (h : Subset (nclose N).mem E) :
    (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (inv W N P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) := sorry

/-! ## Access -/

/-- Open an invariant: given `↑N ⊆ E`, access `▷ P` with a closing view shift.

    Proof strategy: unfold `inv` definition, apply the universally quantified
    body to `E` with the subset proof.

    Coq: `inv_acc` -/
theorem inv_acc {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (P : IProp GF)
    (h : Subset (nclose N).mem E) :
    inv W N P ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) := sorry

/-- Access a timeless invariant: strip the `▷` when `P` is timeless.

    Coq: `inv_acc_timeless` -/
theorem inv_acc_timeless {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (P : IProp GF)
    (h : Subset (nclose N).mem E)
    (htimeless : (BIBase.later P : IProp GF) ⊢
      BIBase.or (BIBase.later (BIBase.pure False)) P) :
    inv W N P ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep P
          (BIBase.wand P
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) := sorry

/-! ## Derived Properties -/

/-- Alter the content of an invariant.

    Coq: `inv_alter` -/
theorem inv_alter {W : WsatGS GF}
    (N : Namespace) (P Q : IProp GF) :
    (BIBase.emp : IProp GF) ⊢
      BIBase.wand (inv W N P)
        (BIBase.wand (BIBase.later (BIBase.persistently
          (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P)))))
          (inv W N Q)) := sorry

/-- Invariant content equivalence.

    Coq: `inv_iff` -/
theorem inv_iff {W : WsatGS GF}
    (N : Namespace) (P Q : IProp GF) :
    (BIBase.emp : IProp GF) ⊢
      BIBase.wand (inv W N P)
        (BIBase.wand (BIBase.later (BIBase.persistently
          (BIBase.and (BIBase.wand P Q) (BIBase.wand Q P))))
          (inv W N Q)) := sorry

end Iris.BaseLogic
