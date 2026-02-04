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

Timeless instances are omitted because the required `ownM_timeless`
infrastructure has not been ported from Coq yet (see TODO in
`Instances/UPred/Instance.lean`).
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI COFE

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [FiniteMapLaws Positive M]
variable [HeapFiniteMap Positive M]
variable {V : Type _} [OFE V] [OFE.Discrete V] [OFE.Leibniz V]

/-! ## Ghost Map Infrastructure -/

/-- Heap structure for all value types, derived from `HeapFiniteMap`. -/
private def gm_heapM (M : Type _ → Type _) [FiniteMap Positive M]
    [HeapFiniteMap Positive M] : ∀ W, Heap (M W) Positive W := fun W =>
  (HeapFiniteMap.heap (K := Positive) (M := M) W)

/-- View type for the ghost map CMRA. -/
abbrev GhostMapView (GF : BundledGFunctors) (M : Type _ → Type _)
    (F : Type _) (V : Type _)
    [UFraction F] [FiniteMap Positive M] [HeapFiniteMap Positive M]
    [OFE V] :=
  @HeapView F Positive (Agree V) M _ (gm_heapM M) _

/-- Constant functor for the ghost map ghost state. -/
abbrev GhostMapF (GF : BundledGFunctors) (M : Type _ → Type _)
    (F : Type _) (V : Type _)
    [UFraction F] [FiniteMap Positive M] [HeapFiniteMap Positive M]
    [OFE V] : OFunctorPre :=
  COFE.constOF (GhostMapView GF M F V)

variable [ElemG GF (GhostMapF GF M F V)]

/-- Authoritative element for the ghost map. -/
private abbrev gm_auth (dq : DFrac F) (m : M (Agree V)) :
    GhostMapView GF M F V :=
  @HeapView.Auth F Positive (Agree V) M _ (gm_heapM M) _ dq m

/-- Fragment element for a single ghost map entry. -/
private abbrev gm_frag (k : Positive) (dq : DFrac F) (v : Agree V) :
    GhostMapView GF M F V :=
  @HeapView.Frag F Positive (Agree V) M _ (gm_heapM M) _ k dq v

/-- Map values through `toAgree`.

    Coq: `to_agree <$> m` -/
noncomputable def agree_map (m : M V) : M (Agree V) :=
  FiniteMap.map toAgree m

/-! ## Definitions -/

/-- Authoritative ownership of the ghost map `m` at ghost name `γ` with
    fractional quality `q`.

    Coq: `ghost_map_auth` -/
noncomputable def ghost_map_auth
    (γ : GName) (q : F) (m : M V) : IProp GF :=
  iOwn (GF := GF) (F := GhostMapF GF M F V) γ
    (gm_auth (GF := GF) (M := M) (F := F) (V := V) (.own q) (agree_map m))

/-- Fragment ownership of a single element: key `k` maps to value `v`
    in the ghost map at name `γ` with discardable fraction `dq`.
    The `M` parameter is phantom — it ties the element to a specific
    finite map type.

    Coq: `ghost_map_elem` -/
noncomputable def ghost_map_elem
    (_phantom : M Unit := ∅) (γ : GName) (k : Positive) (dq : DFrac F)
    (v : V) : IProp GF :=
  iOwn (GF := GF) (F := GhostMapF GF M F V) γ
    (gm_frag (GF := GF) (M := M) (F := F) k dq (toAgree v))

/-! ## Element Instances -/

/-- `ghost_map_elem` with discarded fraction is persistent.

    Coq: `ghost_map_elem_persistent` -/
instance ghost_map_elem_persistent (γ : GName) (k : Positive)
    (v : V) :
    Persistent (ghost_map_elem (GF := GF) (M := M) (F := F)
      ∅ γ k .discard v) where
  persistent := by
    classical
    haveI : CMRA.CoreId (DFrac.discard (F := F)) := by
      refine CMRA.CoreId.of_pcore_eq_some (x := DFrac.discard (F := F)) ?_
      simp [CMRA.pcore, DFrac.pcore]
    haveI : CMRA.CoreId (toAgree v) := by
      refine CMRA.CoreId.of_pcore_eq_some (x := toAgree v) ?_
      simp [CMRA.pcore]
    simp only [ghost_map_elem]
    exact persistently_intro

/-! ## Element Validity Helpers -/

/-- Extract DFrac validity from step-0 fragment validity. -/
private theorem gm_frag_valid0_dfrac {k : Positive} {dq : DFrac F}
    {v : V} (hval : CMRA.ValidN 0
      (gm_frag (GF := GF) (M := M) (F := F) k dq (toAgree v))) :
    DFrac.valid dq := by
  -- View frag validity: ∃ a, HeapR 0 a (point k (some (dq, toAgree v)))
  have hfrag := (View.frag_validN_iff (R := HeapR F Positive (Agree V) M)).mp hval
  obtain ⟨a, hrel⟩ := hfrag
  -- Decode via point_get_iff
  have hpoint := (HeapR.point_get_iff (n := 0) (m := a) (k := k)
    (dq := dq) (v := toAgree v)).mp hrel
  obtain ⟨v', dq', _, hvalid, hinc⟩ := hpoint
  -- From inclusion and validity, extract dq validity
  have hvalid_inc : CMRA.ValidN 0
      (some (dq, toAgree v) : Option (DFrac F × Agree V)) :=
    CMRA.validN_of_incN hinc hvalid
  simp [CMRA.ValidN, optionValidN] at hvalid_inc
  exact (CMRA.discrete_valid hvalid_inc.1 : CMRA.Valid dq)

/-- Extract combined DFrac validity and value agreement from step-0
    fragment op validity. -/
private theorem gm_frag_op_valid0 {k : Positive}
    {dq1 dq2 : DFrac F} {v1 v2 : V}
    (hval : CMRA.ValidN 0
      (gm_frag (GF := GF) (M := M) (F := F) k dq1 (toAgree v1) •
       gm_frag (GF := GF) (M := M) (F := F) k dq2 (toAgree v2))) :
    DFrac.valid (DFrac.op dq1 dq2) ∧ v1 = v2 := by
  -- The op of two frags at the same key
  have heqv : gm_frag (GF := GF) (M := M) (F := F)
        k dq1 (toAgree v1) •
      gm_frag (GF := GF) (M := M) (F := F)
        k dq2 (toAgree v2) ≡
      gm_frag (GF := GF) (M := M) (F := F)
        k (dq1 • dq2) (toAgree v1 • toAgree v2) :=
    (HeapView.frag_op_equiv (H := M)).symm
  have hval' : CMRA.ValidN 0
      (gm_frag (GF := GF) (M := M) (F := F)
        k (dq1 • dq2) (toAgree v1 • toAgree v2)) :=
    CMRA.validN_of_eqv heqv hval
  -- Extract validity from the combined frag
  have hfrag := (View.frag_validN_iff
    (R := HeapR F Positive (Agree V) M)).mp hval'
  obtain ⟨a, hrel⟩ := hfrag
  have hpoint := (HeapR.point_get_iff (n := 0) (m := a) (k := k)
    (dq := dq1 • dq2) (v := toAgree v1 • toAgree v2)).mp hrel
  obtain ⟨v', dq', _, hvalid, hinc⟩ := hpoint
  have hvalid_inc : CMRA.ValidN 0
      (some (dq1 • dq2, toAgree v1 • toAgree v2) :
        Option (DFrac F × Agree V)) :=
    CMRA.validN_of_incN hinc hvalid
  simp [CMRA.ValidN, optionValidN] at hvalid_inc
  constructor
  · exact (CMRA.discrete_valid hvalid_inc.1 : CMRA.Valid (dq1 • dq2))
  · -- From validity of toAgree v1 • toAgree v2, extract agreement
    have hagree := Agree.toAgree_op_validN_iff_dist.mp hvalid_inc.2
    exact OFE.Leibniz.eq_of_eqv (OFE.Discrete.discrete hagree)

/-! ## Element Lemmas -/

/-- An element carries a valid discardable fraction.

    Coq: `ghost_map_elem_valid` -/
theorem ghost_map_elem_valid (γ : GName) (k : Positive) (dq : DFrac F)
    (v : V) :
    ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq v
      ⊢ BIBase.pure (DFrac.valid dq) := by
  refine (iOwn_cmraValid (GF := GF)
    (F := GhostMapF GF M F V) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  exact BI.pure_mono gm_frag_valid0_dfrac

/-- Two elements at the same key have a valid combined fraction and
    equal values.

    Coq: `ghost_map_elem_valid_2` -/
theorem ghost_map_elem_valid_2 (γ : GName) (k : Positive)
    (dq1 dq2 : DFrac F) (v1 v2 : V) :
    BIBase.sep
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq1 v1)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq2 v2)
      ⊢ BIBase.pure (DFrac.valid (DFrac.op dq1 dq2) ∧ v1 = v2) := by
  refine (iOwn_cmraValid_op (GF := GF)
    (F := GhostMapF GF M F V) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  exact BI.pure_mono gm_frag_op_valid0

/-- Two elements at the same key agree on the value.

    Coq: `ghost_map_elem_agree` -/
theorem ghost_map_elem_agree (γ : GName) (k : Positive)
    (dq1 dq2 : DFrac F) (v1 v2 : V) :
    BIBase.sep
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq1 v1)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq2 v2)
      ⊢ BIBase.pure (v1 = v2) := by
  refine (ghost_map_elem_valid_2 γ k dq1 dq2 v1 v2).trans ?_
  exact BI.pure_mono And.right

/-- Make an element read-only (persistent).

    Coq: `ghost_map_elem_persist` -/
theorem ghost_map_elem_persist (γ : GName) (k : Positive)
    (dq : DFrac F) (v : V) :
    ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq v
      ⊢ BUpd.bupd
          (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k .discard v) := by
  simp only [ghost_map_elem]
  exact iOwn_update (GF := GF) (F := GhostMapF GF M F V) (γ := γ)
    (HeapView.update_frag_discard (H := M))

/-! ## Auth Instances -/

-- Timeless instances omitted: requires `ownM_timeless` infrastructure
-- (see TODO in `Instances/UPred/Instance.lean`)

/-! ## Auth Lemmas -/

/-- Authoritative element carries a valid fraction.

    Coq: `ghost_map_auth_valid` -/
theorem ghost_map_auth_valid (γ : GName) (q : F) (m : M V) :
    ghost_map_auth (GF := GF) (F := F) γ q m
      ⊢ BIBase.pure (Fraction.Proper q) := by
  simp only [ghost_map_auth]
  refine (iOwn_cmraValid (GF := GF)
    (F := GhostMapF GF M F V) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  refine BI.pure_mono ?_
  intro hval
  have := (HeapView.auth_validN_iff (H := M)).mp hval
  simp only [CMRA.Valid, DFrac.valid] at this
  exact this

/-- Two auths at the same name have a valid combined fraction and
    equal maps.

    Coq: `ghost_map_auth_valid_2` -/
theorem ghost_map_auth_valid_2 (γ : GName) (q1 q2 : F)
    (m1 m2 : M V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ q1 m1)
      (ghost_map_auth (GF := GF) (F := F) γ q2 m2)
      ⊢ BIBase.pure (Fraction.Proper (q1 + q2) ∧ m1 = m2) := by
  simp only [ghost_map_auth]
  refine (iOwn_cmraValid_op (GF := GF)
    (F := GhostMapF GF M F V) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  refine BI.pure_mono ?_
  intro hval
  have hvalid := (HeapView.auth_op_auth_validN_iff (H := M)).mp hval
  obtain ⟨hdq, hdist⟩ := hvalid
  constructor
  · have : CMRA.Valid (DFrac.own q1 • DFrac.own q2 : DFrac F) :=
      CMRA.discrete_valid hdq
    simp [CMRA.op, DFrac.op, CMRA.Valid, DFrac.valid] at this
    exact this
  · -- From agree_map m1 ≡{0}≡ agree_map m2, derive m1 = m2
    -- The heap OFE gives pointwise dist on Store.get
    apply FiniteMapLaws.ext
    intro k
    classical
    -- Extract pointwise from heap dist
    have hk : Store.get (agree_map m1) k ≡{0}≡
        Store.get (agree_map m2) k := hdist k
    rw [← HeapFiniteMap.get?_eq_get, ← HeapFiniteMap.get?_eq_get] at hk
    simp only [agree_map, FiniteMapLaws.get?_map] at hk
    -- hk : (get? m1 k).map toAgree ≡{0}≡ (get? m2 k).map toAgree
    cases h1 : FiniteMap.get? m1 k with
    | none =>
      cases h2 : FiniteMap.get? m2 k with
      | none => rfl
      | some w2 => simp [h1, h2, OFE.Dist, Option.Forall₂] at hk
    | some w1 =>
      cases h2 : FiniteMap.get? m2 k with
      | none => simp [h1, h2, OFE.Dist, Option.Forall₂] at hk
      | some w2 =>
        simp [h1, h2, OFE.Dist, Option.Forall₂] at hk
        -- hk : toAgree w1 ≡{0}≡ toAgree w2
        congr 1
        exact OFE.Leibniz.eq_of_eqv
          (OFE.Discrete.discrete (Agree.toAgree_injN hk))

/-- Two auths at the same name agree on the map.

    Coq: `ghost_map_auth_agree` -/
theorem ghost_map_auth_agree (γ : GName) (q1 q2 : F)
    (m1 m2 : M V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ q1 m1)
      (ghost_map_auth (GF := GF) (F := F) γ q2 m2)
      ⊢ BIBase.pure (m1 = m2) := by
  refine (ghost_map_auth_valid_2 γ q1 q2 m1 m2).trans ?_
  exact BI.pure_mono And.right

/-! ## Auth-Element Interaction -/

/-- Helper: decode auth+frag validity into map lookup. -/
private theorem gm_auth_frag_lookup {n : Nat}
    {q : F} {m : M V} {k : Positive} {dq : DFrac F} {v : V}
    (hval : CMRA.ValidN n
      (gm_auth (GF := GF) (M := M) (F := F) (V := V) (.own q) (agree_map m) •
       gm_frag (GF := GF) (M := M) (F := F) k dq (toAgree v))) :
    FiniteMap.get? m k = some v := by
  have hvalid := (HeapView.auth_op_frag_validN_iff (H := M)).mp hval
  obtain ⟨v', dq', hdp, hlookup, hvalid', hinc⟩ := hvalid
  -- hlookup : Store.get (agree_map m) k = some v'
  -- Translate to FiniteMap.get?
  classical
  have hget : FiniteMap.get? (agree_map m) k = some v' := by
    simpa [HeapFiniteMap.get?_eq_get] using hlookup
  have hget' : (FiniteMap.get? m k).map toAgree = some v' := by
    simpa [agree_map, FiniteMapLaws.get?_map] using hget
  cases hm : FiniteMap.get? m k with
  | none => simp [hm] at hget'
  | some w =>
    simp [hm] at hget'
    -- v' = toAgree w
    -- From inclusion: some (dq, toAgree v) ≼{n} some (dq', toAgree w)
    have hinc' : some (dq, toAgree v) ≼{n} some (dq', toAgree w) := by
      rwa [← hget'] at hinc
    -- Extract agreement from validity + inclusion
    have hvalid'' : CMRA.ValidN n (dq', toAgree w) := by
      rwa [← hget'] at hvalid'
    -- toAgree v ≼{n} toAgree w (from option inclusion, second component)
    have hdist : v ≡{n}≡ w := by
      have hinc_opt := hinc'
      rcases hinc_opt with ⟨z, hz⟩
      cases z with
      | none =>
        exact (Agree.toAgree_injN (OFE.dist_snd hz)).symm
      | some zz =>
        have : toAgree v ≼{n} toAgree w :=
          ⟨zz.snd, OFE.dist_snd hz⟩
        exact Agree.toAgree_injN
          (Agree.valid_includedN hvalid''.2 this)
    have heq : v = w :=
      OFE.Leibniz.eq_of_eqv
        (OFE.Discrete.discrete (hdist.le (Nat.zero_le n)))
    exact heq ▸ rfl

/-- Looking up an element: if the auth has map `m` and there is a
    fragment for key `k` with value `v`, then `m !! k = some v`.

    Coq: `ghost_map_lookup` -/
theorem ghost_map_lookup (γ : GName) (q : F) (m : M V)
    (k : Positive) (dq : DFrac F) (v : V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ q m)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k dq v)
      ⊢ BIBase.pure (FiniteMap.get? m k = some v) := by
  simp only [ghost_map_auth, ghost_map_elem]
  refine (iOwn_cmraValid_op (GF := GF)
    (F := GhostMapF GF M F V) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  exact BI.pure_mono gm_auth_frag_lookup

/-! ## Map Helpers -/

/-- `agree_map` preserves absence of keys. -/
private theorem agree_map_get_none {m : M V} {k : Positive}
    (h : FiniteMap.get? m k = none) :
    Store.get (agree_map (M := M) m) k = none := by
  classical
  have h' : FiniteMap.get? (agree_map m) k = none := by
    simp [agree_map, FiniteMapLaws.get?_map, h]
  simpa [HeapFiniteMap.get?_eq_get] using h'

/-- `agree_map` distributes over insert as Store.set. -/
private theorem agree_map_insert (m : M V) (k : Positive) (v : V) :
    agree_map (M := M) (FiniteMap.insert m k v) =
      Store.set (agree_map m) k (some (toAgree v)) := by
  classical
  apply FiniteMapLaws.ext
  intro j
  by_cases hjk : j = k
  · subst j
    have hL : FiniteMap.get? (agree_map (FiniteMap.insert m k v)) k =
        some (toAgree v) := by
      simp [agree_map, FiniteMapLaws.get?_map,
        FiniteMapLaws.get?_insert_same]
    have hR : FiniteMap.get? (Store.set (agree_map m) k
        (some (toAgree v))) k = some (toAgree v) := by
      simp [HeapFiniteMap.get?_eq_get, Store.get_set_eq]
    exact hL.trans hR.symm
  · have hne : k ≠ j := Ne.symm hjk
    have hL : FiniteMap.get? (agree_map (FiniteMap.insert m k v)) j =
        FiniteMap.get? (agree_map m) j := by
      simp [agree_map, FiniteMapLaws.get?_map,
        FiniteMapLaws.get?_insert_ne _ _ _ _ hne]
    have hR : FiniteMap.get? (Store.set (agree_map m) k
        (some (toAgree v))) j =
        FiniteMap.get? (agree_map m) j := by
      simp [HeapFiniteMap.get?_eq_get, Store.get_set_ne hne]
    exact hL.trans hR.symm

/-- `agree_map` distributes over delete. -/
private theorem agree_map_delete (m : M V) (k : Positive) :
    agree_map (M := M) (FiniteMap.delete m k) =
      Store.set (agree_map m) k none := by
  classical
  apply FiniteMapLaws.ext
  intro j
  by_cases hjk : j = k
  · subst j
    have hL : FiniteMap.get? (agree_map (FiniteMap.delete m k)) k =
        none := by
      simp [agree_map, FiniteMapLaws.get?_map,
        FiniteMapLaws.get?_delete_same]
    have hR : FiniteMap.get? (Store.set (agree_map m) k none) k =
        none := by
      simp [HeapFiniteMap.get?_eq_get, Store.get_set_eq]
    exact hL.trans hR.symm
  · have hne : k ≠ j := Ne.symm hjk
    have hL : FiniteMap.get? (agree_map (FiniteMap.delete m k)) j =
        FiniteMap.get? (agree_map m) j := by
      simp [agree_map, FiniteMapLaws.get?_map,
        FiniteMapLaws.get?_delete_ne _ _ _ hne]
    have hR : FiniteMap.get? (Store.set (agree_map m) k none) j =
        FiniteMap.get? (agree_map m) j := by
      simp [HeapFiniteMap.get?_eq_get, Store.get_set_ne hne]
    exact hL.trans hR.symm

/-! ## Update Lemmas -/

/-- Insert a fresh element into the ghost map.

    Coq: `ghost_map_insert` -/
theorem ghost_map_insert (γ : GName) (m : M V) (k : Positive)
    (v : V) (hfresh : FiniteMap.get? m k = none) :
    ghost_map_auth (GF := GF) (F := F) γ 1 m
      ⊢ BUpd.bupd (BIBase.sep
          (ghost_map_auth (GF := GF) (F := F) γ 1 (insert m k v))
          (ghost_map_elem (GF := GF) (M := M) (F := F)
            ∅ γ k (.own 1) v)) := by
  simp only [ghost_map_auth, ghost_map_elem, agree_map_insert m k v]
  have hget : Store.get (agree_map (M := M) m) k = none :=
    agree_map_get_none hfresh
  have hdq : CMRA.Valid (DFrac.own (1 : F)) := DFrac.valid_own_one
  have hval : CMRA.Valid (toAgree v : Agree V) := by
    simp [Agree.valid_def, Agree.valid, Agree.validN_iff, toAgree]
  have hupd := HeapView.update_one_alloc (H := M)
    (m1 := agree_map m) (k := k)
    (dq := DFrac.own (1 : F)) (v1 := toAgree v)
    hget hdq hval
  refine (iOwn_update (GF := GF) (F := GhostMapF GF M F V) (γ := γ)
    hupd).trans ?_
  refine BIUpdate.mono ?_
  exact (iOwn_op (GF := GF) (F := GhostMapF GF M F V) (γ := γ)).mp

/-- Insert a fresh element as persistent (read-only).

    Coq: `ghost_map_insert_persist` -/
theorem ghost_map_insert_persist (γ : GName) (m : M V)
    (k : Positive) (v : V)
    (hfresh : FiniteMap.get? m k = none) :
    ghost_map_auth (GF := GF) (F := F) γ 1 m
      ⊢ BUpd.bupd (BIBase.sep
          (ghost_map_auth (GF := GF) (F := F) γ 1 (insert m k v))
          (ghost_map_elem (GF := GF) (M := M) (F := F)
            ∅ γ k .discard v)) := by
  refine (ghost_map_insert γ m k v hfresh).trans ?_
  refine (BIUpdate.mono ?_).trans BIUpdate.trans
  refine (sep_mono_r (ghost_map_elem_persist γ k (.own (1 : F)) v)).trans ?_
  exact (sep_mono_l BIUpdate.intro).trans bupd_sep

/-- Delete an element from the ghost map.

    Coq: `ghost_map_delete` -/
theorem ghost_map_delete (γ : GName) (m : M V) (k : Positive)
    (v : V) :
    BIBase.sep
      (ghost_map_auth (GF := GF) (F := F) γ 1 m)
      (ghost_map_elem (GF := GF) (M := M) (F := F) ∅ γ k (.own 1) v)
      ⊢ BUpd.bupd
          (ghost_map_auth (GF := GF) (F := F) γ 1 (delete m k)) := by
  simp only [ghost_map_auth, ghost_map_elem, gm_auth, agree_map_delete m k]
  refine (iOwn_op (GF := GF) (F := GhostMapF GF M F V) (γ := γ)).mpr.trans ?_
  have hupd := HeapView.update_one_delete (F := F) (H := M)
    (m1 := agree_map m) (k := k) (v1 := toAgree v)
  simp only [Heap.delete] at hupd
  exact iOwn_update (GF := GF) (F := GhostMapF GF M F V) (γ := γ) hupd

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
            ∅ γ k (.own 1) w)) := by
  simp only [ghost_map_auth, ghost_map_elem, gm_auth, agree_map_insert m k w]
  refine (iOwn_op (GF := GF) (F := GhostMapF GF M F V) (γ := γ)).mpr.trans ?_
  have hval : CMRA.Valid (toAgree w : Agree V) := by
    simp [Agree.valid_def, Agree.valid, Agree.validN_iff, toAgree]
  have hupd := HeapView.update_replace (F := F) (H := M)
    (m1 := agree_map m) (k := k) (v1 := toAgree v) (v2 := toAgree w)
    hval
  refine (iOwn_update (GF := GF) (F := GhostMapF GF M F V) (γ := γ)
    hupd).trans ?_
  refine BIUpdate.mono ?_
  exact (iOwn_op (GF := GF) (F := GhostMapF GF M F V) (γ := γ)).mp

/-! ## Allocation -/

/-- Allocate an empty ghost map.

    Coq: `ghost_map_alloc_empty` -/
theorem ghost_map_alloc_empty :
    (BIBase.emp : IProp GF)
      ⊢ BUpd.bupd (BIBase.«exists» fun (γ : GName) =>
          ghost_map_auth (GF := GF) (F := F) γ 1
            (∅ : M V)) := by
  simp only [ghost_map_auth]
  have hval : CMRA.Valid
      (gm_auth (GF := GF) (M := M) (F := F) (V := V)
        (.own (1 : F)) (agree_map (∅ : M V))) := by
    simpa [gm_auth] using
      HeapView.auth_one_valid (F := F) (H := M)
        (m1 := agree_map (∅ : M V))
  exact iOwn_alloc _ hval

/-- Allocate a ghost map with contents `m`, returning auth and all
    elements. Proven by induction on the finite map using
    `ghost_map_alloc_empty` and `ghost_map_insert`.

    Coq: `ghost_map_alloc` -/
theorem ghost_map_alloc (m : M V) :
    (BIBase.emp : IProp GF)
      ⊢ BUpd.bupd (BIBase.«exists» fun (γ : GName) =>
          BIBase.sep
            (ghost_map_auth (GF := GF) (F := F) γ 1 m)
            (big_sepM (fun k v =>
              ghost_map_elem (GF := GF) (M := M) (F := F)
                ∅ γ k (.own 1) v) m)) := by
  apply FiniteMapLaws.induction_on (m := m)
  · -- Base case: empty map
    simp only [big_sepM_empty]
    refine (ghost_map_alloc_empty (GF := GF) (M := M) (F := F)
      (V := V)).trans (BIUpdate.mono ?_)
    exact BI.exists_mono fun γ => sep_emp.mpr
  · -- Inductive step: insert i x m'
    intro i x m' hfresh ih
    classical
    refine ih.trans ?_
    refine (BIUpdate.mono ?_).trans BIUpdate.trans
    refine (BI.exists_mono (PROP := IProp GF) fun γ => ?_).trans bupd_exist
    refine (sep_mono_l (ghost_map_insert (GF := GF) (M := M) (F := F)
      γ m' i x hfresh)).trans ?_
    refine ((sep_mono_r BIUpdate.intro).trans bupd_sep).trans ?_
    refine BIUpdate.mono ?_
    refine sep_assoc.mp.trans ?_
    exact sep_mono_r
      (big_sepM_insert (M' := M) (fun k v =>
        ghost_map_elem (GF := GF) (M := M) (F := F)
          ∅ γ k (.own 1) v) m' i x hfresh).mpr

end Iris.BaseLogic
