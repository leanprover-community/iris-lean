/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.GhostMap

/-! # Generalized Heap

Reference: `iris/base_logic/lib/gen_heap.v`

A generic mechanism for a language-level points-to connective `l ↦{dq} v`
reflecting the physical heap. This library is designed as a singleton (i.e.,
with a single instance per proof), with the `GenHeapGS` typeclass providing
the ghost name. The mechanism can be plugged into a language by using
`gen_heap_interp σ` in the state interpretation of the weakest precondition.

## Main Definitions

- `GenHeapGS` — ghost state name for the heap ghost map
- `gen_heap_interp` — heap state interpretation
- `pointsto` — points-to predicate `l ↦{dq} v`

## Main Results

- `pointsto_valid`, `pointsto_agree` — validation and agreement
- `pointsto_persist` — make points-to read-only
- `gen_heap_alloc`, `gen_heap_valid`, `gen_heap_update` — heap operations

## Simplifications

Meta-data infrastructure (`meta_token`, `meta`, `reservation_map`) from the
Coq version is omitted — it requires `reservation_map` RA and namespace
indirection not yet ported. Timeless instances are omitted because the
required `ownM_timeless` infrastructure has not been ported from Coq yet.
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI COFE

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [FiniteMapLaws Positive M]
variable [HeapFiniteMap Positive M]
variable {V : Type _} [OFE V] [OFE.Discrete V] [OFE.Leibniz V]
variable [ElemG GF (GhostMapF GF M F V)]

/-! ## Ghost State Typeclass -/

/-- Ghost state for the generalized heap. Contains the ghost name for
    the value map.

    Coq: `gen_heapGS` -/
class GenHeapGS (GF : BundledGFunctors) (M : Type _ → Type _)
    (F : Type _) where
  /-- Ghost name for the value heap ghost map. -/
  gen_heap_name : GName

variable [GenHeapGS GF M F]

/-! ## Definitions -/

/-- Heap state interpretation: authoritative ownership of the physical
    heap `σ` at the designated ghost name.

    Coq: `gen_heap_interp` -/
noncomputable def gen_heap_interp (σ : M V) : IProp GF :=
  ghost_map_auth (GF := GF) (F := F)
    (GenHeapGS.gen_heap_name (GF := GF) (M := M) (F := F)) 1 σ

/-- Points-to predicate: `pointsto l dq v` asserts ownership of heap
    location `l` holding value `v` with discardable fraction `dq`.

    Coq: `pointsto` -/
noncomputable def pointsto (l : Positive) (dq : DFrac F) (v : V) :
    IProp GF :=
  ghost_map_elem (GF := GF) (M := M) (F := F) ∅
    (GenHeapGS.gen_heap_name (GF := GF) (M := M) (F := F)) l dq v

/-! ## Pointsto Instances -/

-- Timeless instances omitted: requires `ownM_timeless` infrastructure.

/-- `pointsto` with discarded fraction is persistent.

    Coq: `pointsto_persistent` -/
instance pointsto_persistent' (l : Positive) (v : V) :
    Persistent (pointsto (GF := GF) (M := M) (F := F) l .discard v) :=
  ghost_map_elem_persistent _ _ _

/-! ## Pointsto Lemmas -/

/-- A points-to carries a valid fraction.

    Coq: `pointsto_valid` -/
theorem pointsto_valid (l : Positive) (dq : DFrac F) (v : V) :
    pointsto (GF := GF) (M := M) (F := F) l dq v
      ⊢ BIBase.pure (DFrac.valid dq) :=
  ghost_map_elem_valid _ _ _ _

/-- Two points-to at the same location have valid combined fraction
    and equal values.

    Coq: `pointsto_valid_2` -/
theorem pointsto_valid_2 (l : Positive) (dq1 dq2 : DFrac F)
    (v1 v2 : V) :
    BIBase.sep
      (pointsto (GF := GF) (M := M) (F := F) l dq1 v1)
      (pointsto (GF := GF) (M := M) (F := F) l dq2 v2)
      ⊢ BIBase.pure (DFrac.valid (DFrac.op dq1 dq2) ∧ v1 = v2) :=
  ghost_map_elem_valid_2 _ _ _ _ _ _

/-- Two points-to at the same location agree on the value.

    Coq: `pointsto_agree` -/
theorem pointsto_agree' (l : Positive) (dq1 dq2 : DFrac F)
    (v1 v2 : V) :
    BIBase.sep
      (pointsto (GF := GF) (M := M) (F := F) l dq1 v1)
      (pointsto (GF := GF) (M := M) (F := F) l dq2 v2)
      ⊢ BIBase.pure (v1 = v2) :=
  ghost_map_elem_agree _ _ _ _ _ _

/-- Make a points-to read-only (persistent).

    Coq: `pointsto_persist` -/
theorem pointsto_persist (l : Positive) (dq : DFrac F) (v : V) :
    pointsto (GF := GF) (M := M) (F := F) l dq v
      ⊢ BUpd.bupd
          (pointsto (GF := GF) (M := M) (F := F) l .discard v) :=
  ghost_map_elem_persist _ _ _ _

/-! ## Heap Operations -/

/-- Allocate a single heap location.

    Coq: `gen_heap_alloc` -/
theorem gen_heap_alloc (σ : M V) (l : Positive) (v : V)
    (hfresh : FiniteMap.get? σ l = none) :
    gen_heap_interp (GF := GF) (M := M) (F := F) σ
      ⊢ BUpd.bupd (BIBase.sep
          (gen_heap_interp (GF := GF) (M := M) (F := F)
            (insert σ l v))
          (pointsto (GF := GF) (M := M) (F := F)
            l (DFrac.own 1) v)) :=
  ghost_map_insert _ _ _ _ hfresh

/-- Validate a heap location: if the heap has `σ` and we own
    `l ↦{dq} v`, then `σ !! l = some v`.

    Coq: `gen_heap_valid` -/
theorem gen_heap_valid (σ : M V) (l : Positive) (dq : DFrac F)
    (v : V) :
    BIBase.sep
      (gen_heap_interp (GF := GF) (M := M) (F := F) σ)
      (pointsto (GF := GF) (M := M) (F := F) l dq v)
      ⊢ BIBase.pure (FiniteMap.get? σ l = some v) :=
  ghost_map_lookup _ _ _ _ _ _

/-- Update a heap location.

    Coq: `gen_heap_update` -/
theorem gen_heap_update (σ : M V) (l : Positive) (v1 v2 : V) :
    BIBase.sep
      (gen_heap_interp (GF := GF) (M := M) (F := F) σ)
      (pointsto (GF := GF) (M := M) (F := F) l (DFrac.own 1) v1)
      ⊢ BUpd.bupd (BIBase.sep
          (gen_heap_interp (GF := GF) (M := M) (F := F)
            (insert σ l v2))
          (pointsto (GF := GF) (M := M) (F := F)
            l (DFrac.own 1) v2)) :=
  ghost_map_update _ _ _ _ _

end Iris.BaseLogic
