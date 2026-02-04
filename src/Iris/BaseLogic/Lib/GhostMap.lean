/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.Wsat
import Iris.BI.BigOp

/-! # Ghost Map

Reference: `iris/base_logic/lib/ghost_map.v`

A "ghost map" (or "ghost heap") with a proposition controlling authoritative
ownership of the entire map, and a "points-to-like" proposition for (mutable,
fractional, or persistent read-only) ownership of individual elements.

The ghost map is parameterized by a key type `K` and value type `V`. It provides
two connectives:

- `ghost_map_auth γ q m` — authoritative ownership of the entire map `m` at
  ghost name `γ` with fractional quality `q`
- `ghost_map_elem γ k dq v` — fragment ownership of a single element `k ↦ v`
  with discardable fraction `dq`

## Main Definitions

- `ghost_map_auth` — authoritative ghost map ownership
- `ghost_map_elem` — fragment ownership of a single key-value pair

## Main Results

- `ghost_map_elem_valid`, `ghost_map_elem_agree` — element validation and
  agreement
- `ghost_map_elem_persist` — make an element read-only
- `ghost_map_auth_valid`, `ghost_map_auth_agree` — auth validation and
  agreement
- `ghost_map_lookup` — auth + element implies map lookup
- `ghost_map_insert`, `ghost_map_delete`, `ghost_map_update` —
  single-element updates
- `ghost_map_alloc` — allocate a fresh ghost map
- `ghost_map_lookup_big`, `ghost_map_insert_big`, `ghost_map_delete_big`,
  `ghost_map_update_big` — big-op versions of interaction lemmas

## Simplifications

We omit `gmap_viewR` / `agreeR (leibnizO V)` and instead use the existing
`HeapView` CMRA directly, mirroring how `wsat.lean` models the invariant
registry. The sealing mechanism is replaced by direct definitions.
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [FiniteMapLaws Positive M]
variable [HeapFiniteMap Positive M]

/-! ## Definitions -/

/-- Authoritative ownership of the ghost map `m` at ghost name `γ` with
    fractional quality `q`.

    Coq: `ghost_map_auth` -/
noncomputable def ghost_map_auth
    (γ : GName) (q : F) (m : M V) : IProp GF :=
  sorry

/-- Fragment ownership of a single element: key `k` maps to value `v`
    in the ghost map at name `γ` with discardable fraction `dq`.
    The `M` parameter is phantom — it ties the element to a specific
    finite map type.

    Coq: `ghost_map_elem` -/
noncomputable def ghost_map_elem
    (_phantom : M Unit := ∅) (γ : GName) (k : Positive) (dq : DFrac F)
    (v : V) : IProp GF :=
  sorry

/-! ## Element Instances -/

/-- `ghost_map_elem` is timeless.

    Coq: `ghost_map_elem_timeless` -/
instance ghost_map_elem_timeless (γ : GName) (k : Positive)
    (dq : DFrac F) (v : V) :
    Timeless (ghost_map_elem (GF := GF) (M := M) (F := F)
      ∅ γ k dq v) :=
  sorry

/-- `ghost_map_elem` with discarded fraction is persistent.

    Coq: `ghost_map_elem_persistent` -/
instance ghost_map_elem_persistent (γ : GName) (k : Positive)
    (v : V) :
    Persistent (ghost_map_elem (GF := GF) (M := M) (F := F)
      ∅ γ k .discard v) :=
  sorry

/-! ## Element Lemmas -/

/-- An element carries a valid discardable fraction.

    Coq: `ghost_map_elem_valid` -/
theorem ghost_map_elem_valid (γ : GName) (k : Positive) (dq : DFrac F)
    (v : V) :
    ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq v
      ⊢ BIBase.pure (DFrac.valid dq) :=
  sorry

/-- Two elements at the same key have a valid combined fraction and
    equal values.

    Coq: `ghost_map_elem_valid_2` -/
theorem ghost_map_elem_valid_2 (γ : GName) (k : Positive)
    (dq1 dq2 : DFrac F) (v1 v2 : V) :
    BIBase.sep
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq1 v1)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq2 v2)
      ⊢ BIBase.pure (DFrac.valid (DFrac.op dq1 dq2) ∧ v1 = v2) :=
  sorry

/-- Two elements at the same key agree on the value.

    Coq: `ghost_map_elem_agree` -/
theorem ghost_map_elem_agree (γ : GName) (k : Positive)
    (dq1 dq2 : DFrac F) (v1 v2 : V) :
    BIBase.sep
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq1 v1)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq2 v2)
      ⊢ BIBase.pure (v1 = v2) :=
  sorry

/-- Combine two elements into a single element with combined fraction.

    Coq: `ghost_map_elem_combine` -/
theorem ghost_map_elem_combine (γ : GName) (k : Positive)
    (dq1 dq2 : DFrac F) (v1 v2 : V) :
    BIBase.sep
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq1 v1)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq2 v2)
      ⊢ BIBase.sep
          (ghost_map_elem (GF := GF) (M := M) (F := F)
            ∅ γ k (DFrac.op dq1 dq2) v1)
          (BIBase.pure (v1 = v2)) :=
  sorry

/-- Invalid combined fractions imply distinct keys.

    Coq: `ghost_map_elem_frac_ne` -/
theorem ghost_map_elem_frac_ne (γ : GName) (k1 k2 : Positive)
    (dq1 dq2 : DFrac F) (v1 v2 : V)
    (hinv : ¬ DFrac.valid (DFrac.op dq1 dq2)) :
    BIBase.sep
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k1 dq1 v1)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k2 dq2 v2)
      ⊢ BIBase.pure (k1 ≠ k2) :=
  sorry

/-- Exclusive element and any element imply distinct keys.

    Coq: `ghost_map_elem_ne` -/
theorem ghost_map_elem_ne (γ : GName) (k1 k2 : Positive)
    (dq2 : DFrac F) (v1 v2 : V) :
    BIBase.sep
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k1 (.own 1) v1)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k2 dq2 v2)
      ⊢ BIBase.pure (k1 ≠ k2) :=
  sorry

/-- Make an element read-only (persistent).

    Coq: `ghost_map_elem_persist` -/
theorem ghost_map_elem_persist (γ : GName) (k : Positive)
    (dq : DFrac F) (v : V) :
    ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq v
      ⊢ BUpd.bupd
          (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k .discard v) :=
  sorry

/-! ## Auth Instances -/

/-- `ghost_map_auth` is timeless.

    Coq: `ghost_map_auth_timeless` -/
instance ghost_map_auth_timeless (γ : GName) (q : F) (m : M V) :
    Timeless (ghost_map_auth (GF := GF) (F := F) γ q m) :=
  sorry

/-! ## Auth Lemmas -/

/-- Authoritative element carries a valid fraction.

    Coq: `ghost_map_auth_valid` -/
theorem ghost_map_auth_valid (γ : GName) (q : F) (m : M V) :
    ghost_map_auth (GF := GF) (F := F) γ q m
      ⊢ BIBase.pure (Fraction.Proper q) :=
  sorry

/-- Two auths at the same name have a valid combined fraction and
    equal maps.

    Coq: `ghost_map_auth_valid_2` -/
theorem ghost_map_auth_valid_2 (γ : GName) (q1 q2 : F)
    (m1 m2 : M V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ q1 m1)
      (ghost_map_auth (GF := GF) (F := F) γ q2 m2)
      ⊢ BIBase.pure (Fraction.Proper (q1 + q2) ∧ m1 = m2) :=
  sorry

/-- Two auths at the same name agree on the map.

    Coq: `ghost_map_auth_agree` -/
theorem ghost_map_auth_agree (γ : GName) (q1 q2 : F)
    (m1 m2 : M V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ q1 m1)
      (ghost_map_auth (GF := GF) (F := F) γ q2 m2)
      ⊢ BIBase.pure (m1 = m2) :=
  sorry

/-! ## Auth-Element Interaction -/

/-- Looking up an element: if the auth has map `m` and there is a
    fragment for key `k` with value `v`, then `m !! k = some v`.

    Coq: `ghost_map_lookup` -/
theorem ghost_map_lookup (γ : GName) (q : F) (m : M V)
    (k : Positive) (dq : DFrac F) (v : V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ q m)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq v)
      ⊢ BIBase.pure (FiniteMap.get? m k = some v) :=
  sorry

/-- Insert a fresh element into the ghost map.

    Coq: `ghost_map_insert` -/
theorem ghost_map_insert (γ : GName) (m : M V) (k : Positive)
    (v : V) (hfresh : FiniteMap.get? m k = none) :
    ghost_map_auth (GF := GF) (F := F) γ 1 m
      ⊢ BUpd.bupd (BIBase.sep
          (ghost_map_auth (GF := GF) (F := F) γ 1 (insert m k v))
          (ghost_map_elem (GF := GF) (M := M) (F := F)
            ∅ γ k (.own 1) v)) :=
  sorry

/-- Insert a fresh element as persistent (read-only).

    Coq: `ghost_map_insert_persist` -/
theorem ghost_map_insert_persist (γ : GName) (m : M V)
    (k : Positive) (v : V)
    (hfresh : FiniteMap.get? m k = none) :
    ghost_map_auth (GF := GF) (F := F) γ 1 m
      ⊢ BUpd.bupd (BIBase.sep
          (ghost_map_auth (GF := GF) (F := F) γ 1 (insert m k v))
          (ghost_map_elem (GF := GF) (M := M) (F := F)
            ∅ γ k .discard v)) :=
  sorry

/-- Delete an element from the ghost map.

    Coq: `ghost_map_delete` -/
theorem ghost_map_delete (γ : GName) (m : M V) (k : Positive)
    (v : V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ 1 m)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k (.own 1) v)
      ⊢ BUpd.bupd
          (ghost_map_auth (GF := GF) (F := F) γ 1 (delete m k)) :=
  sorry

/-- Update the value of an existing element.

    Coq: `ghost_map_update` -/
theorem ghost_map_update (γ : GName) (m : M V) (k : Positive)
    (v w : V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ 1 m)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k (.own 1) v)
      ⊢ BUpd.bupd (BIBase.sep
          (ghost_map_auth (GF := GF) (F := F) γ 1 (insert m k w))
          (ghost_map_elem (GF := GF) (M := M) (F := F)
            ∅ γ k (.own 1) w)) :=
  sorry

/-! ## Allocation -/

/-- Allocate a ghost map with contents `m`, returning auth and all
    elements.

    Coq: `ghost_map_alloc` -/
theorem ghost_map_alloc (m : M V) :
    (BIBase.emp : IProp GF)
      ⊢ BUpd.bupd (BIBase.«exists» fun (γ : GName) =>
          BIBase.sep
            (ghost_map_auth (GF := GF) (F := F) γ 1 m)
            (big_sepM (fun k v =>
              ghost_map_elem (GF := GF) (M := M) (F := F)
                ∅ γ k (.own 1) v) m)) :=
  sorry

/-- Allocate an empty ghost map.

    Coq: `ghost_map_alloc_empty` -/
theorem ghost_map_alloc_empty :
    (BIBase.emp : IProp GF)
      ⊢ BUpd.bupd (BIBase.«exists» fun (γ : GName) =>
          ghost_map_auth (GF := GF) (F := F) γ 1
            (∅ : M V)) :=
  sorry

/-! ## Big-Op Versions -/

/-- Look up multiple elements: auth + big sep of elements implies
    submap.

    Coq: `ghost_map_lookup_big` -/
theorem ghost_map_lookup_big (γ : GName) (q : F)
    (m m0 : M V) (dq : DFrac F) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ q m)
      (big_sepM (fun k v =>
        ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq v) m0)
      ⊢ BIBase.pure (FiniteMap.submap m0 m) :=
  sorry

/-- Insert multiple fresh elements.

    Coq: `ghost_map_insert_big` -/
theorem ghost_map_insert_big (γ : GName) (m m' : M V)
    (hdisj : FiniteMap.disjoint m' m) :
    ghost_map_auth (GF := GF) (F := F) γ 1 m
      ⊢ BUpd.bupd (BIBase.sep
          (ghost_map_auth (GF := GF) (F := F) γ 1
            (FiniteMap.union m' m))
          (big_sepM (fun k v =>
            ghost_map_elem (GF := GF) (M := M) (F := F)
              ∅ γ k (.own 1) v) m')) :=
  sorry

/-- Delete multiple elements.

    Coq: `ghost_map_delete_big` -/
theorem ghost_map_delete_big (γ : GName) (m m0 : M V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ 1 m)
      (big_sepM (fun k v =>
        ghost_map_elem (GF := GF) (M := M) (F := F)
          ∅ γ k (.own 1) v) m0)
      ⊢ BUpd.bupd
          (ghost_map_auth (GF := GF) (F := F) γ 1
            (FiniteMap.difference m m0)) :=
  sorry

/-- Update multiple elements.

    Coq: `ghost_map_update_big` -/
theorem ghost_map_update_big (γ : GName) (m m0 m1 : M V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ 1 m)
      (big_sepM (fun k v =>
        ghost_map_elem (GF := GF) (M := M) (F := F)
          ∅ γ k (.own 1) v) m0)
      ⊢ BUpd.bupd (BIBase.sep
          (ghost_map_auth (GF := GF) (F := F) γ 1
            (FiniteMap.union m1 m))
          (big_sepM (fun k v =>
            ghost_map_elem (GF := GF) (M := M) (F := F)
              ∅ γ k (.own 1) v) m1)) :=
  sorry

end Iris.BaseLogic
