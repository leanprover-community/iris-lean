/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.GhostMap
import Iris.Std.Namespace

/-! # Generalized Heap

Reference: `iris/base_logic/lib/gen_heap.v`

A generic mechanism for a language-level points-to connective `l ↦{dq} v`
reflecting the physical heap. This library is designed as a singleton (i.e.,
with a single instance per proof), with the `GenHeapGS` typeclass providing
the ghost names. The mechanism can be plugged into a language by using
`gen_heap_interp σ` in the state interpretation of the weakest precondition.

In addition to the points-to connective, this library provides a mechanism
for attaching "meta" or "ghost" data to locations via namespaces:

- `meta_token l E` — exclusive token for meta-data allocation under mask `E`
- `meta l N x` — persistent assertion that data `x` is associated with
  location `l` under namespace `N`

## Main Definitions

- `GenHeapGS` — ghost state names for the heap and meta ghost maps
- `gen_heap_interp` — heap state interpretation (existential over meta map)
- `pointsto` — points-to predicate `l ↦{dq} v`
- `meta_token` — exclusive meta-data allocation token
- `meta` — persistent meta-data assertion

## Main Results

- `pointsto_valid`, `pointsto_agree` — validation and agreement for points-to
- `pointsto_persist` — make points-to read-only
- `meta_token_union`, `meta_token_difference` — mask splitting for meta tokens
- `meta_agree`, `meta_set` — meta-data agreement and allocation
- `gen_heap_alloc`, `gen_heap_valid`, `gen_heap_update` — heap operations
- `gen_heap_init` — initialize the generalized heap

## Simplifications

We omit `reservation_map` and the full meta-data indirection mechanism from
the Coq version. The `meta_token` and `meta` connectives are stubbed with
simplified types that will be refined during implementation.
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [FiniteMapLaws Positive M]
variable [HeapFiniteMap Positive M]

/-! ## Ghost State Typeclass -/

/-- Ghost state for the generalized heap. Contains the ghost names for the
    value map and the meta-data map.

    Coq: `gen_heapGS` -/
class GenHeapGS (GF : BundledGFunctors) (M : Type _ → Type _)
    (F : Type _) where
  /-- Ghost name for the value heap ghost map. -/
  gen_heap_name : GName
  /-- Ghost name for the meta-data ghost map. -/
  gen_meta_name : GName

variable [GenHeapGS GF M F]

/-! ## Definitions -/

/-- Heap state interpretation: authoritative ownership of the physical heap `σ`
    together with the meta-data map. The meta map's domain is a subset of the
    heap domain.

    Coq: `gen_heap_interp` -/
noncomputable def gen_heap_interp (σ : M V) : IProp GF :=
  let _ := (inferInstance : GenHeapGS GF M F)
  sorry

/-- Points-to predicate: `pointsto l dq v` asserts ownership of heap location
    `l` holding value `v` with discardable fraction `dq`.

    Coq: `pointsto` -/
noncomputable def pointsto (l : Positive) (dq : DFrac F) (v : V) :
    IProp GF :=
  ghost_map_elem (GF := GF) (M := M) (F := F) ∅
    (GenHeapGS.gen_heap_name (GF := GF) (M := M) (F := F)) l dq v

/-- Exclusive meta-data token for location `l` under mask `E`.

    Coq: `meta_token` -/
noncomputable def meta_token (l : Positive) (E : CoPset) :
    IProp GF :=
  let _ := (inferInstance : GenHeapGS GF M F)
  sorry

/-- Persistent meta-data assertion: data `x` is associated with location `l`
    under namespace `N`.

    Coq: `meta` -/
noncomputable def «meta» (l : Positive) (N : Namespace) (x : Positive) :
    IProp GF :=
  let _ := (inferInstance : GenHeapGS GF M F)
  sorry

/-! ## Pointsto Instances -/

/-- `pointsto` is timeless.

    Coq: `pointsto_timeless` -/
instance pointsto_timeless' (l : Positive) (dq : DFrac F) (v : V) :
    Timeless (pointsto (GF := GF) (M := M) (F := F) l dq v) :=
  sorry

/-- `pointsto` with discarded fraction is persistent.

    Coq: `pointsto_persistent` -/
instance pointsto_persistent' (l : Positive) (v : V) :
    Persistent (pointsto (GF := GF) (M := M) (F := F) l .discard v) :=
  sorry

/-! ## Pointsto Lemmas -/

/-- A points-to carries a valid fraction.

    Coq: `pointsto_valid` -/
theorem pointsto_valid (l : Positive) (dq : DFrac F) (v : V) :
    pointsto (GF := GF) (M := M) (F := F) l dq v
      ⊢ BIBase.pure (DFrac.valid dq) :=
  sorry

/-- Two points-to at the same location have valid combined fraction and equal
    values.

    Coq: `pointsto_valid_2` -/
theorem pointsto_valid_2 (l : Positive) (dq1 dq2 : DFrac F)
    (v1 v2 : V) :
    BIBase.sep
      (pointsto (GF := GF) (M := M) (F := F) l dq1 v1)
      (pointsto (GF := GF) (M := M) (F := F) l dq2 v2)
      ⊢ BIBase.pure (DFrac.valid (DFrac.op dq1 dq2) ∧ v1 = v2) :=
  sorry

/-- Two points-to at the same location agree on the value.

    Coq: `pointsto_agree` -/
theorem pointsto_agree' (l : Positive) (dq1 dq2 : DFrac F)
    (v1 v2 : V) :
    BIBase.sep
      (pointsto (GF := GF) (M := M) (F := F) l dq1 v1)
      (pointsto (GF := GF) (M := M) (F := F) l dq2 v2)
      ⊢ BIBase.pure (v1 = v2) :=
  sorry

/-- Combine two points-to into one with combined fraction.

    Coq: `pointsto_combine` -/
theorem pointsto_combine (l : Positive) (dq1 dq2 : DFrac F)
    (v1 v2 : V) :
    BIBase.sep
      (pointsto (GF := GF) (M := M) (F := F) l dq1 v1)
      (pointsto (GF := GF) (M := M) (F := F) l dq2 v2)
      ⊢ BIBase.sep
          (pointsto (GF := GF) (M := M) (F := F) l (DFrac.op dq1 dq2) v1)
          (BIBase.pure (v1 = v2)) :=
  sorry

/-- Invalid combined fractions imply distinct locations.

    Coq: `pointsto_frac_ne` -/
theorem pointsto_frac_ne (l1 l2 : Positive) (dq1 dq2 : DFrac F)
    (v1 v2 : V) (hinv : ¬ DFrac.valid (DFrac.op dq1 dq2)) :
    BIBase.sep
      (pointsto (GF := GF) (M := M) (F := F) l1 dq1 v1)
      (pointsto (GF := GF) (M := M) (F := F) l2 dq2 v2)
      ⊢ BIBase.pure (l1 ≠ l2) :=
  sorry

/-- Exclusive and fractional at the same location imply distinct locations.

    Coq: `pointsto_ne` -/
theorem pointsto_ne (l1 l2 : Positive) (dq2 : DFrac F)
    (v1 v2 : V) :
    BIBase.sep
      (pointsto (GF := GF) (M := M) (F := F) l1 (DFrac.own 1) v1)
      (pointsto (GF := GF) (M := M) (F := F) l2 dq2 v2)
      ⊢ BIBase.pure (l1 ≠ l2) :=
  sorry

/-- Make a points-to read-only (persistent).

    Coq: `pointsto_persist` -/
theorem pointsto_persist (l : Positive) (dq : DFrac F) (v : V) :
    pointsto (GF := GF) (M := M) (F := F) l dq v
      ⊢ BUpd.bupd
          (pointsto (GF := GF) (M := M) (F := F) l .discard v) :=
  sorry

/-! ## Meta Token Lemmas -/

/-- Split a meta token across a disjoint union.

    Coq: `meta_token_union_1` -/
theorem meta_token_union_1 (l : Positive) (E1 E2 : CoPset)
    (hdisj : CoPset.Disjoint E1 E2) :
    meta_token (GF := GF) (M := M) (F := F) l (E1 ∪ E2)
      ⊢ BIBase.sep
          (meta_token (GF := GF) (M := M) (F := F) l E1)
          (meta_token (GF := GF) (M := M) (F := F) l E2) :=
  sorry

/-- Combine two meta tokens into one.

    Coq: `meta_token_union_2` -/
theorem meta_token_union_2 (l : Positive) (E1 E2 : CoPset) :
    BIBase.sep
      (meta_token (GF := GF) (M := M) (F := F) l E1)
      (meta_token (GF := GF) (M := M) (F := F) l E2)
      ⊢ meta_token (GF := GF) (M := M) (F := F) l (E1 ∪ E2) :=
  sorry

/-- Bidirectional splitting of a meta token.

    Coq: `meta_token_union` -/
theorem meta_token_union (l : Positive) (E1 E2 : CoPset)
    (hdisj : CoPset.Disjoint E1 E2) :
    meta_token (GF := GF) (M := M) (F := F) l (E1 ∪ E2)
      = BIBase.sep
          (meta_token (GF := GF) (M := M) (F := F) l E1)
          (meta_token (GF := GF) (M := M) (F := F) l E2) :=
  sorry

/-- Decompose a meta token by subset.

    Coq: `meta_token_difference` -/
theorem meta_token_difference (l : Positive) (E1 E2 : CoPset)
    (hsub : E1 ⊆ E2) :
    meta_token (GF := GF) (M := M) (F := F) l E2
      = BIBase.sep
          (meta_token (GF := GF) (M := M) (F := F) l E1)
          (meta_token (GF := GF) (M := M) (F := F) l (E2 \ E1)) :=
  sorry

/-! ## Meta Instances -/

/-- `meta_token` is timeless.

    Coq: `meta_token_timeless` -/
instance meta_token_timeless' (l : Positive) (E : CoPset) :
    Timeless (meta_token (GF := GF) (M := M) (F := F) l E) :=
  sorry

/-- `meta` is timeless.

    Coq: `meta_timeless` -/
instance meta_timeless' (l : Positive) (N : Namespace) (x : Positive) :
    Timeless («meta» (GF := GF) (M := M) (F := F) l N x) :=
  sorry

/-- `meta` is persistent.

    Coq: `meta_persistent` -/
instance meta_persistent' (l : Positive) (N : Namespace) (x : Positive) :
    Persistent («meta» (GF := GF) (M := M) (F := F) l N x) :=
  sorry

/-! ## Meta Lemmas -/

/-- Two meta assertions at the same location and namespace agree on the data.

    Coq: `meta_agree` -/
theorem meta_agree (l : Positive) (N : Namespace)
    (x1 x2 : Positive) :
    BIBase.sep
      («meta» (GF := GF) (M := M) (F := F) l N x1)
      («meta» (GF := GF) (M := M) (F := F) l N x2)
      ⊢ BIBase.pure (x1 = x2) :=
  sorry

/-- Set meta data for a location under a namespace.

    Coq: `meta_set` -/
theorem meta_set (l : Positive) (N : Namespace)
    (x : Positive) (E : CoPset)
    (hsub : nclose N ⊆ E) :
    meta_token (GF := GF) (M := M) (F := F) l E
      ⊢ BUpd.bupd («meta» (GF := GF) (M := M) (F := F) l N x) :=
  sorry

/-- Meta data and meta token are inconsistent when the namespace is in the
    mask.

    Coq: `meta_meta_token_valid` -/
theorem meta_meta_token_valid (l : Positive) (N : Namespace)
    (x : Positive) (E : CoPset) :
    BIBase.sep
      («meta» (GF := GF) (M := M) (F := F) l N x)
      (meta_token (GF := GF) (M := M) (F := F) l E)
      ⊢ BIBase.pure (¬ nclose N ⊆ E) :=
  sorry

/-! ## Heap Operations -/

/-- Allocate a single heap location.

    Coq: `gen_heap_alloc` -/
theorem gen_heap_alloc (σ : M V) (l : Positive) (v : V)
    (hfresh : FiniteMap.get? σ l = none) :
    gen_heap_interp (GF := GF) (M := M) (F := F) σ
      ⊢ BUpd.bupd (BIBase.sep
          (BIBase.sep
            (gen_heap_interp (GF := GF) (M := M) (F := F) (insert σ l v))
            (pointsto (GF := GF) (M := M) (F := F) l (DFrac.own 1) v))
          (meta_token (GF := GF) (M := M) (F := F) l CoPset.top)) :=
  sorry

/-- Allocate multiple heap locations.

    Coq: `gen_heap_alloc_big` -/
theorem gen_heap_alloc_big (σ σ' : M V)
    (hdisj : FiniteMap.disjoint σ' σ) :
    gen_heap_interp (GF := GF) (M := M) (F := F) σ
      ⊢ BUpd.bupd (BIBase.sep
          (BIBase.sep
            (gen_heap_interp (GF := GF) (M := M) (F := F)
              (FiniteMap.union σ' σ))
            (big_sepM (M' := M) (fun l v =>
              pointsto (GF := GF) (M := M) (F := F)
                l (DFrac.own 1) v) σ'))
          (big_sepM (M' := M) (fun l (_ : V) =>
            meta_token (GF := GF) (M := M) (F := F)
              l CoPset.top) σ')) :=
  sorry

/-- Validate a heap location: if the heap has `σ` and we own `l ↦{dq} v`,
    then `σ !! l = some v`.

    Coq: `gen_heap_valid` -/
theorem gen_heap_valid (σ : M V) (l : Positive) (dq : DFrac F)
    (v : V) :
    BIBase.sep
      (gen_heap_interp (GF := GF) (M := M) (F := F) σ)
      (pointsto (GF := GF) (M := M) (F := F) l dq v)
      ⊢ BIBase.pure (FiniteMap.get? σ l = some v) :=
  sorry

/-- Update a heap location.

    Coq: `gen_heap_update` -/
theorem gen_heap_update (σ : M V) (l : Positive) (v1 v2 : V) :
    BIBase.sep
      (gen_heap_interp (GF := GF) (M := M) (F := F) σ)
      (pointsto (GF := GF) (M := M) (F := F) l (DFrac.own 1) v1)
      ⊢ BUpd.bupd (BIBase.sep
          (gen_heap_interp (GF := GF) (M := M) (F := F) (insert σ l v2))
          (pointsto (GF := GF) (M := M) (F := F) l (DFrac.own 1) v2)) :=
  sorry

/-! ## Initialization -/

/-- Initialize the generalized heap from a physical heap `σ`, returning the
    heap interpretation and all points-to and meta tokens.

    Coq: `gen_heap_init` -/
theorem gen_heap_init (σ : M V) :
    (BIBase.emp : IProp GF)
      ⊢ BUpd.bupd (BIBase.«exists» fun (_ : GenHeapGS GF M F) =>
          BIBase.sep
            (BIBase.sep
              (gen_heap_interp (GF := GF) (M := M) (F := F) σ)
              (big_sepM (M' := M) (fun l v =>
                pointsto (GF := GF) (M := M) (F := F)
                  l (DFrac.own 1) v) σ))
            (big_sepM (M' := M) (fun l (_ : V) =>
              meta_token (GF := GF) (M := M) (F := F)
                l CoPset.top) σ)) :=
  sorry

/-- Initialize the generalized heap with specific ghost names.

    Coq: `gen_heap_init_names` -/
theorem gen_heap_init_names (σ : M V) :
    (BIBase.emp : IProp GF)
      ⊢ BUpd.bupd (BIBase.«exists» fun (γh : GName) =>
          BIBase.«exists» fun (γm : GName) =>
            let _ : GenHeapGS GF M F := ⟨γh, γm⟩
            BIBase.sep
              (BIBase.sep
                (gen_heap_interp (GF := GF) (M := M) (F := F) σ)
                (big_sepM (M' := M) (fun l v =>
                  pointsto (GF := GF) (M := M) (F := F)
                    l (DFrac.own 1) v) σ))
              (big_sepM (M' := M) (fun l (_ : V) =>
                meta_token (GF := GF) (M := M) (F := F)
                  l CoPset.top) σ)) :=
  sorry

end Iris.BaseLogic
