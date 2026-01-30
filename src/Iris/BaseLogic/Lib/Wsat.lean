/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Instances.IProp.Instance
import Iris.Algebra.CoPset
import Iris.BI.BigOp
import Iris.ProofMode.Tactics

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

open Iris Iris.Algebra Iris.Std Iris.BI Iris.ProofMode COFE CMRA One

/-! ## Finite Map + Heap Compatibility -/

/-- Compatibility between `FiniteMap.get?` and `Store.get` for heaps. -/
class HeapFiniteMap (K : Type _) (M : Type _ → Type _)
    [FiniteMap K M] : Type _ where
  /-- Heap structure for all value types. -/
  heap : ∀ V, Heap (M V) K V
  /-- Compatibility between `FiniteMap.get?` and `Store.get`. -/
  get?_eq_get : ∀ {V} (m : M V) (k : K), (FiniteMap.get? m k) = Store.get m k

instance (K : Type _) (M : Type _ → Type _) [FiniteMap K M] [h : HeapFiniteMap K M] (V) :
    Heap (M V) K V :=
  h.heap V

instance (K : Type _) (M : Type _ → Type _) [FiniteMap K M] [h : HeapFiniteMap K M] :
    (∀ V, Heap (M V) K V) := by
  intro V
  exact h.heap V

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

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [DecidableEq Positive]
variable [FiniteMapLaws Positive M]
variable [HeapFiniteMap Positive M]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

/-- Invariant bodies (no universe lift now that the registry is `IProp`-valued). -/
abbrev IPropU (GF : BundledGFunctors) : Type _ := IProp GF

/-- Equality on `IProp` as a `UPred` (fixes the underlying resource type). -/
abbrev IPropEq (GF : BundledGFunctors) (P Q : IProp GF) : IProp GF :=
  UPred.eq (M := IResUR GF) P Q

/-- Heap instance for the invariant map values. -/
private def heapM : ∀ V, Heap (M V) Positive V := fun V =>
  (HeapFiniteMap.heap (K := Positive) (M := M) V)

/-- Invariant registry view (gmap_view) specialized to `HeapView`. -/
abbrev InvView (GF : BundledGFunctors) (M : Type _ → Type _) (F : Type _)
    [UFraction F] [FiniteMap Positive M] [HeapFiniteMap Positive M] :=
  @HeapView F Positive (Agree (IPropU GF)) M _ heapM _

/-- Functor for the invariant registry ghost state. -/
abbrev InvF (GF : BundledGFunctors) (M : Type _ → Type _) (F : Type _)
    [UFraction F] [FiniteMap Positive M] [HeapFiniteMap Positive M] : OFunctorPre :=
  COFE.constOF (InvView (GF := GF) (M := M) (F := F))

variable [ElemG GF (InvF GF M F)]

variable (W : WsatGS GF)

-- Keep IProp entailments opaque for proof mode (avoid unfolding to `holds`).
private structure IPropEntails (P Q : IProp GF) : Prop where
  toEntails : P ⊢ Q

private def wrapEntails {P Q : IProp GF} (h : P ⊢ Q) :
    IPropEntails (GF := GF) P Q :=
  ⟨h⟩

local instance asEmpValid_IPropEntails (d : Iris.ProofMode.AsEmpValid.Direction)
    (P Q : IProp GF) :
    Iris.ProofMode.AsEmpValid d (IPropEntails (GF := GF) P Q) iprop(P -∗ Q) := by
  have hEntails :
      Iris.ProofMode.AsEmpValid d (P ⊢ Q) iprop(P -∗ Q) := inferInstance
  refine ⟨?_, ?_⟩
  · intro hd h
    exact (hEntails.as_emp_valid.1 hd) h.toEntails
  · intro hd h
    exact ⟨(hEntails.as_emp_valid.2 hd) h⟩

/-! ## Ownership Connectives -/

/-- Unfold an invariant body (no OFE-level `Later` at the moment). -/
noncomputable def invariant_unfold (P : IProp GF) : IProp GF :=
  -- TODO: switch to OFE `Later` once universe-polymorphic constOF is in place
  P

/-- Map invariant bodies into the agreement CMRA. -/
noncomputable def inv_map (I : M (IPropU GF)) : M (Agree (IPropU GF)) :=
  -- pointwise map: P ↦ toAgree P
  FiniteMap.map (fun P => toAgree P) I

/-- Authoritative element for the invariant registry. -/
abbrev gmap_view_auth (dq : DFrac F) (m : M (Agree (IPropU GF))) : InvView GF M F :=
  @HeapView.Auth F Positive (Agree (IPropU GF)) M _ heapM _ dq m

/-- Fragment element for a single invariant name. -/
abbrev gmap_view_frag (i : Positive) (dq : DFrac F) (v : Agree (IPropU GF)) :
    InvView GF M F :=
  @HeapView.Frag F Positive (Agree (IPropU GF)) M _ heapM _ i dq v

/-- Invariant ownership: `ownI i P` asserts that invariant `i` is registered
    with content `P`. This is persistent — once registered, an invariant
    exists forever. -/
noncomputable def ownI (_W : WsatGS GF) (i : Positive) (P : IProp GF) : IProp GF :=
  -- store the invariant body under key `i` as a discarded fragment
  iOwn (GF := GF) (F := InvF GF M F) _W.invariant_name <|
    gmap_view_frag (GF := GF) (M := M) (F := F) i .discard (toAgree (invariant_unfold (GF := GF) P))

/-- Enabled mask ownership: `ownE E` asserts the caller holds the right to
    open invariants in the set `E`. Implemented via the `CoPsetDisj` CMRA. -/
noncomputable def ownE (_W : WsatGS GF) (E : CoPset) : IProp GF :=
  -- use a constant ghost functor over `CoPsetDisj`
  iOwn (GF := GF) (F := COFE.constOF CoPsetDisj) _W.enabled_name <| CoPsetDisj.coPset E

/-- Disabled token ownership: `ownD E` asserts the caller holds disabled
    tokens for invariants in `E`. Implemented via the `GSetDisj` CMRA. -/
noncomputable def ownD (_W : WsatGS GF) (E : GSet) : IProp GF :=
  -- use a constant ghost functor over `GSetDisj`
  iOwn (GF := GF) (F := COFE.constOF GSetDisj) _W.disabled_name <| GSetDisj.gset E

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
noncomputable def wsat (_W : WsatGS GF) : IProp GF :=
  -- registry + big sep over all invariants
  BIBase.exists fun I : M (IPropU GF) =>
    BIBase.sep
      (iOwn (GF := GF) (F := InvF GF M F) _W.invariant_name <|
        gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I))
      (big_sepM (PROP := IProp GF)
        (fun i Q =>
          BIBase.or
            (BIBase.sep (BIBase.later Q) (ownD _W (GSet.singleton i)))
            (ownE _W (CoPset.singleton i))) I)

instance intoExists_wsat (W : WsatGS GF) :
    IntoExists (PROP := IProp GF)
      (wsat (GF := GF) (M := M) (F := F) W)
      (fun I : M (IPropU GF) =>
        BIBase.sep
          (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name <|
            gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I))
          (big_sepM (PROP := IProp GF)
            (fun i Q =>
              BIBase.or
                (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
                (ownE W (CoPset.singleton i)))
            I)) := by
  refine ⟨by simp [wsat]⟩

instance fromExists_wsat (W : WsatGS GF) :
    FromExists (PROP := IProp GF)
      (wsat (GF := GF) (M := M) (F := F) W)
      (fun I : M (IPropU GF) =>
        BIBase.sep
          (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name <|
            gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I))
          (big_sepM (PROP := IProp GF)
            (fun i Q =>
              BIBase.or
                (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
                (ownE W (CoPset.singleton i)))
            I)) := by
  refine ⟨by simp [wsat]⟩

/-! ## Enabled Mask Properties -/

omit [DecidableEq Positive] [ElemG GF (COFE.constOF GSetDisj)] in
/-- Allocate an empty enabled mask. -/
theorem ownE_empty : (BIBase.emp : IProp GF) ⊢ BUpd.bupd (ownE W ∅) := by
  -- `CoPsetDisj.coPset ∅` is definitionally the unit
  haveI : IsUnit (CoPsetDisj.coPset (∅ : CoPset)) := by
    simpa using (inferInstance : IsUnit (UCMRA.unit : CoPsetDisj))
  simpa [ownE] using
    (iOwn_unit (GF := GF) (F := COFE.constOF CoPsetDisj) (γ := W.enabled_name))

omit [DecidableEq Positive] [ElemG GF (COFE.constOF GSetDisj)] in
/-- Disjoint union of enabled masks splits into separating conjunction. -/
theorem ownE_op (E₁ E₂ : CoPset) (h : E₁.Disjoint E₂) :
    ownE W (E₁.union E₂) ⊣⊢ BIBase.sep (ownE W E₁) (ownE W E₂) := by
  have h' :
      CoPsetDisj.coPset (E₁.union E₂) =
        (CoPsetDisj.coPset E₁ : CoPsetDisj) • CoPsetDisj.coPset E₂ :=
    (coPset_disj_union h).symm
  simpa [ownE, h'] using
    (iOwn_op (GF := GF) (F := COFE.constOF CoPsetDisj) (γ := W.enabled_name)
      (a1 := CoPsetDisj.coPset E₁) (a2 := CoPsetDisj.coPset E₂))

omit [DecidableEq Positive] [ElemG GF (COFE.constOF GSetDisj)] in
/-- Enabled masks in separating conjunction must be disjoint. -/
theorem ownE_disjoint (E₁ E₂ : CoPset) :
    BIBase.sep (ownE W E₁) (ownE W E₂) ⊢
      BIBase.pure (E₁.Disjoint E₂) := by
  refine (iOwn_cmraValid_op (GF := GF) (F := COFE.constOF CoPsetDisj)
      (γ := W.enabled_name) (a1 := CoPsetDisj.coPset E₁)
      (a2 := CoPsetDisj.coPset E₂)).trans ?_
  refine (UPred.cmraValid_elim
      (a := (CoPsetDisj.coPset E₁ : CoPsetDisj) • CoPsetDisj.coPset E₂)).trans ?_
  refine BI.pure_mono ?_
  intro hvalid0
  have hvalid :
      ✓ ((CoPsetDisj.coPset E₁ : CoPsetDisj) • CoPsetDisj.coPset E₂) :=
    CMRA.discrete_valid hvalid0
  exact (coPset_disj_valid_op).1 hvalid

omit [DecidableEq Positive] [ElemG GF (COFE.constOF GSetDisj)] in
/-- Cannot own the same singleton enabled token twice. -/
theorem ownE_singleton_twice (i : Positive) :
    BIBase.sep (ownE W (CoPset.singleton i)) (ownE W (CoPset.singleton i)) ⊢
      (BIBase.pure False : IProp GF) := by
  refine (ownE_disjoint (W := W)
      (E₁ := CoPset.singleton i) (E₂ := CoPset.singleton i)).trans ?_
  refine BI.pure_mono ?_
  intro hdisj
  have hmem : (CoPset.singleton i).mem i := by
    rfl
  exact (hdisj i) ⟨hmem, hmem⟩

/-! ## Disabled Token Properties -/

omit [DecidableEq Positive] [ElemG GF (COFE.constOF CoPsetDisj)] in
/-- Allocate empty disabled tokens. -/
theorem ownD_empty : (BIBase.emp : IProp GF) ⊢ BUpd.bupd (ownD W ∅) := by
  -- allocate the unit for the `GSetDisj` ghost cell
  haveI : IsUnit (GSetDisj.gset (∅ : GSet)) := by
    simpa using (inferInstance : IsUnit (UCMRA.unit : GSetDisj))
  simpa [ownD] using
    (iOwn_unit (GF := GF) (F := COFE.constOF GSetDisj) (γ := W.disabled_name))

omit [DecidableEq Positive] [ElemG GF (COFE.constOF CoPsetDisj)] in
private theorem ownD_emptyE :
    IPropEntails (GF := GF) (BIBase.emp : IProp GF) (BUpd.bupd (ownD W ∅)) := by
  exact ⟨ownD_empty (W := W)⟩

omit [DecidableEq Positive] [ElemG GF (COFE.constOF CoPsetDisj)] in
/-- Disjoint union of disabled tokens splits into separating conjunction. -/
theorem ownD_op (E₁ E₂ : GSet) (h : E₁.Disjoint E₂) :
    ownD W (E₁.union E₂) ⊣⊢ BIBase.sep (ownD W E₁) (ownD W E₂) := by
  have h' :
      GSetDisj.gset (E₁.union E₂) =
        (GSetDisj.gset E₁ : GSetDisj) • GSetDisj.gset E₂ :=
    (gset_disj_union h).symm
  simpa [ownD, h'] using
    (iOwn_op (GF := GF) (F := COFE.constOF GSetDisj) (γ := W.disabled_name)
      (a1 := GSetDisj.gset E₁) (a2 := GSetDisj.gset E₂))

omit [DecidableEq Positive] [ElemG GF (COFE.constOF CoPsetDisj)] in
/-- Disabled tokens in separating conjunction must be disjoint. -/
theorem ownD_disjoint (E₁ E₂ : GSet) :
    BIBase.sep (ownD W E₁) (ownD W E₂) ⊢
      BIBase.pure (E₁.Disjoint E₂) := by
  refine (iOwn_cmraValid_op (GF := GF) (F := COFE.constOF GSetDisj)
      (γ := W.disabled_name) (a1 := GSetDisj.gset E₁)
      (a2 := GSetDisj.gset E₂)).trans ?_
  refine (UPred.cmraValid_elim
      (a := (GSetDisj.gset E₁ : GSetDisj) • GSetDisj.gset E₂)).trans ?_
  refine BI.pure_mono ?_
  intro hvalid0
  have hvalid :
      ✓ ((GSetDisj.gset E₁ : GSetDisj) • GSetDisj.gset E₂) :=
    CMRA.discrete_valid hvalid0
  exact (gset_disj_valid_op).1 hvalid

omit [DecidableEq Positive] [ElemG GF (COFE.constOF CoPsetDisj)] in
/-- Cannot own the same singleton disabled token twice. -/
theorem ownD_singleton_twice (i : Positive) :
    BIBase.sep (ownD W (GSet.singleton i)) (ownD W (GSet.singleton i)) ⊢
      (BIBase.pure False : IProp GF) := by
  refine (ownD_disjoint (W := W)
      (E₁ := GSet.singleton i) (E₂ := GSet.singleton i)).trans ?_
  refine BI.pure_mono ?_
  intro hdisj
  have hmem : (GSet.singleton i).mem i := by
    rfl
  exact (hdisj i) ⟨hmem, hmem⟩

/-! ## Invariant Properties -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M]
    [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
/-- `ownI` is persistent. -/
theorem ownI_persistent (i : Positive) (P : IProp GF) :
    ownI (GF := GF) (M := M) (F := F) W i P ⊢
      BIBase.persistently (ownI (GF := GF) (M := M) (F := F) W i P) := by
  classical
  -- `discard` and `toAgree` have trivial cores, so the fragment is core-id
  haveI : CMRA.CoreId (DFrac.discard (F := F)) := by
    refine CMRA.CoreId.of_pcore_eq_some (x := DFrac.discard (F := F)) ?_
    simp [CMRA.pcore, DFrac.pcore]
  haveI : CMRA.CoreId (toAgree (invariant_unfold (GF := GF) P)) := by
    refine CMRA.CoreId.of_pcore_eq_some (x := toAgree (invariant_unfold (GF := GF) P)) ?_
    simp [CMRA.pcore]
  simpa [ownI] using
    (persistently_intro (P := iOwn (GF := GF) (F := InvF GF M F) W.invariant_name <|
      gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
        (toAgree (invariant_unfold (GF := GF) P))))

/-! ## Invariant Lookup Helper -/

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem inv_map_lookup {I : M (IPropU GF)} {i : Positive} {v : Agree (IPropU GF)}
    (hget : Store.get (inv_map (GF := GF) I) i = some v) :
    ∃ Q, FiniteMap.get? I i = some Q ∧
      v = toAgree Q := by
  classical
  have hget' : FiniteMap.get? (inv_map (GF := GF) I) i = some v := by
    simpa [HeapFiniteMap.get?_eq_get] using hget
  have hget'' : (FiniteMap.get? I i).map (fun P => toAgree P) = some v := by
    simpa [inv_map, FiniteMapLaws.get?_map] using hget'
  cases hI : FiniteMap.get? I i with
  | none =>
      simp [hI] at hget''
  | some Q =>
      refine ⟨Q, rfl, ?_⟩
      have hv : some (toAgree Q) = some v := by
        simpa [hI] using hget''
      exact (Option.some.inj hv).symm

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem invariant_lookup (I : M (IPropU GF)) (i : Positive) (P : IProp GF) :
    BIBase.sep
      (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name
        (gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I)))
      (ownI (GF := GF) (M := M) (F := F) W i P) ⊢
      BIBase.sep
        (BIBase.exists (fun Q =>
          BIBase.sep (BIBase.pure (FiniteMap.get? I i = some Q))
            (BIBase.later (IPropEq (GF := GF) Q P))))
        (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name
          (gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I))) := by
  intro n x hvalid hsep
  -- get validity of auth • frag from ownership
  have hvalid :
      ✓{n} (gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
              (inv_map (GF := GF) I) •
            gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
              (toAgree (invariant_unfold (GF := GF) P))) :=
    by
      have hvalid' :
          (UPred.cmraValid
              (gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
                (inv_map (GF := GF) I) •
              gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
                (toAgree (invariant_unfold (GF := GF) P))) : IProp GF).holds n x := by
        have hsep' :
            (BIBase.sep
                (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name
                  (gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
                    (inv_map (GF := GF) I)))
                (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name
                  (gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
                    (toAgree (invariant_unfold (GF := GF) P))))) n x := by
          simpa [ownI] using hsep
        exact (iOwn_cmraValid_op (GF := GF) (F := InvF GF M F)
          (γ := W.invariant_name)
          (a1 := gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
            (inv_map (GF := GF) I))
          (a2 := gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
            (toAgree (invariant_unfold (GF := GF) P)))) n x hvalid hsep'
      simpa [UPred.cmraValid] using hvalid'
  -- decode validity via HeapView
  obtain ⟨v', dq', _Hdp, hlookup, hval, hinc⟩ :=
    (HeapView.auth_op_frag_validN_iff (F := F) (K := Positive)
        (V := Agree (IPropU GF)) (H := M)).1 hvalid
  obtain ⟨Q, hI, hv'⟩ := inv_map_lookup (I := I) (i := i) (v := v') hlookup
  -- normalize the inclusion/validity facts with the discovered entry
  have hinc' :
      some (DFrac.discard, toAgree (invariant_unfold (GF := GF) P)) ≼{n}
        some (dq', toAgree Q) := by
    simpa [hv'] using hinc
  have hval' : ✓{n} (dq', toAgree Q) := by
    simpa [hv'] using hval
  -- derive agreement of invariant bodies
  have hvdist :
        toAgree (invariant_unfold (GF := GF) P) ≡{n}≡
          toAgree Q := by
    have hinc'' := (Option.some_incN_some_iff).1 hinc'
    cases hinc'' with
    | inl hEq =>
        exact OFE.dist_snd hEq
    | inr hInc =>
        obtain ⟨c, hc⟩ := hInc
        have hvinc :
            toAgree (invariant_unfold (GF := GF) P) ≼{n}
              toAgree Q := by
          exact ⟨c.snd, OFE.dist_snd hc⟩
        have hvvalid : ✓{n} (toAgree Q) :=
          hval'.2
        exact (Agree.valid_includedN (x := toAgree (invariant_unfold (GF := GF) P))
          (y := toAgree Q) hvvalid hvinc)
  have hdist : invariant_unfold (GF := GF) P ≡{n}≡ Q :=
    Agree.toAgree_injN hvdist
  -- build the later equality proof (resource-independent)
  have hLaterEq : ∀ x, BIBase.later (IPropEq (GF := GF) Q P) n x := by
    intro x
    cases n with
    | zero =>
        simp [BIBase.later, UPred.later]
    | succ n' =>
        have hPQ : P ≡{n'}≡ Q := by
          exact OFE.Dist.lt hdist (Nat.lt_succ_self _)
        -- UPred.eq Q P at step n' is Q ≡{n'}≡ P
        simpa [BIBase.later, UPred.later, IPropEq, UPred.eq] using hPQ.symm
  -- split the resources to keep the auth part
  rcases hsep with ⟨x1, x2, hx, hAuth, _hFrag⟩
  -- show the existential holds on the fragment side
  have hExists :
      (BIBase.exists (fun Q =>
        BIBase.sep (BIBase.pure (FiniteMap.get? I i = some Q))
          (BIBase.later (IPropEq (GF := GF) Q P)))) n x2 := by
    refine ⟨
        BIBase.sep (BIBase.pure (FiniteMap.get? I i = some Q))
          (BIBase.later (IPropEq (GF := GF) Q P)), ?_, ?_⟩
    · exact ⟨Q, rfl⟩
    · refine ⟨x2, (UCMRA.unit : IResUR GF),
        (CMRA.unit_right_id_dist (α := IResUR GF) x2).symm, ?_, ?_⟩
      · exact hI
      · simpa using hLaterEq x2
  -- assemble the separating conjunction with the auth ownership
  refine ⟨x2, x1, ?_, hExists, hAuth⟩
  exact hx.trans (CMRA.op_commN (x := x1) (y := x2))

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem invariant_lookupE (I : M (IPropU GF)) (i : Positive) (P : IProp GF) :
    IPropEntails (GF := GF)
      (BIBase.sep
        (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name
          (gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I)))
        (ownI (GF := GF) (M := M) (F := F) W i P))
      (BIBase.sep
        (BIBase.exists (fun Q =>
          BIBase.sep (BIBase.pure (FiniteMap.get? I i = some Q))
            (BIBase.later (IPropEq (GF := GF) Q P))))
        (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name
          (gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I)))) := by
  exact ⟨invariant_lookup (W := W) (I := I) (i := i) (P := P)⟩

/-! ## Later Equality Helpers -/

omit [DecidableEq Positive] [ElemG GF (COFE.constOF CoPsetDisj)]
    [ElemG GF (COFE.constOF GSetDisj)] in
private theorem later_eq_symm (P Q : IProp GF) :
    BIBase.later (IPropEq (GF := GF) Q P) ⊢ BIBase.later (IPropEq (GF := GF) P Q) := by
  -- `UPred.eq` is symmetric at each step index
  intro n x _ hEq
  cases n with
  | zero =>
      simp [BIBase.later, UPred.later]
  | succ n' =>
      simpa [BIBase.later, UPred.later, IPropEq, UPred.eq] using hEq.symm

omit [DecidableEq Positive] [ElemG GF (COFE.constOF CoPsetDisj)]
    [ElemG GF (COFE.constOF GSetDisj)] in
private theorem later_eq_elim (P Q : IProp GF) :
    BIBase.sep (BIBase.later P) (BIBase.later (IPropEq (GF := GF) P Q)) ⊢ BIBase.later Q := by
  -- use the internal equality to rewrite the later'd proposition
  intro n x Hv hsep
  rcases hsep with ⟨x1, x2, hx, hP, hEq⟩
  cases n with
  | zero =>
      simp [BIBase.later, UPred.later]
  | succ n' =>
      -- lift `P` to the full resource and rewrite along equality
      have hx' : x1 ≼{n'} x := by
        -- extend by the right frame then transport along the split equality
        have hinc : x1 • x2 ≼{n'} x := by
          exact CMRA.incN_of_incN_succ (OFE.Dist.to_incN hx.symm)
        exact CMRA.incN_trans (CMRA.incN_op_left n' x1 x2) hinc
      have hP' : P n' x := P.mono hP hx' (Nat.le_refl _)
      have hPQ : P ≡{n'}≡ Q := by
        simpa [BIBase.later, UPred.later, IPropEq, UPred.eq] using hEq
      have hQ : Q n' x :=
        uPred_holds_ne (P := Q) (Q := P) hPQ.symm (Nat.le_refl _)
          (CMRA.validN_of_le (Nat.le_succ _) Hv) hP'
      simpa [BIBase.later, UPred.later] using hQ

/-! ## GSet Disjoint Allocation Helper -/

omit [DecidableEq Positive] in
private theorem gset_disj_alloc_empty_updateP_strong' (P : Positive → Prop)
    (Hfresh : ∀ E : GSet, ∃ i, ¬E.mem i ∧ P i) :
    (GSetDisj.gset (∅ : GSet) : GSetDisj) ~~>:
      fun Y => ∃ i, Y = GSetDisj.gset (GSet.singleton i) ∧ P i := by
  -- reduce to discrete updateP and pick a fresh singleton
  refine (UpdateP.discrete (x := (GSetDisj.gset (∅ : GSet) : GSetDisj))
    (P := fun Y => ∃ i, Y = GSetDisj.gset (GSet.singleton i) ∧ P i)).mpr ?_
  intro mz hvalid
  cases mz with
  | none =>
      -- empty frame: any fresh singleton is valid
      obtain ⟨i, _, hiP⟩ := Hfresh ∅
      refine ⟨GSetDisj.gset (GSet.singleton i), ⟨i, rfl, hiP⟩, ?_⟩
      simp [CMRA.op?, CMRA.Valid]
  | some z =>
      cases z with
      | invalid =>
          -- invalid frame contradicts validity
          cases hvalid
      | gset X =>
          -- choose a singleton disjoint from the frame
          obtain ⟨i, hiX, hiP⟩ := Hfresh X
          refine ⟨GSetDisj.gset (GSet.singleton i), ⟨i, rfl, hiP⟩, ?_⟩
          have hdisj : GSet.Disjoint (GSet.singleton i) X := by
            intro n hn
            have hn' : n = i := by simpa using hn.1
            subst hn'
            exact hiX hn.2
          simp [CMRA.op?, gset_disj_valid_op, hdisj]

/-! ## Map/Heap Helpers -/

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem inv_map_get_none {I : M (IPropU GF)} {i : Positive}
    (hI : FiniteMap.get? I i = none) :
    Store.get (inv_map (GF := GF) I) i = none := by
  -- translate `get?` through `inv_map` and the heap lookup
  classical
  have h' : FiniteMap.get? (inv_map (GF := GF) I) i = none := by
    simp [inv_map, FiniteMapLaws.get?_map, hI]
  simpa [HeapFiniteMap.get?_eq_get] using h'

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem inv_map_insert (I : M (IPropU GF)) (i : Positive) (P : IProp GF) :
    inv_map (GF := GF) (FiniteMap.insert I i P) =
      Store.set (inv_map (GF := GF) I) i
        (some (toAgree (invariant_unfold (GF := GF) P))) := by
  -- extensionality by `get?`, computed via map and heap lookup
  classical
  apply FiniteMapLaws.ext
  intro k
  by_cases hki : k = i
  · subst k
    have hL :
        FiniteMap.get? (inv_map (GF := GF) (FiniteMap.insert I i P)) i =
          some (toAgree (invariant_unfold (GF := GF) P)) := by
      simp [inv_map, FiniteMapLaws.get?_map, FiniteMapLaws.get?_insert_same, invariant_unfold]
    have hR :
        FiniteMap.get? (Store.set (inv_map (GF := GF) I) i
          (some (toAgree (invariant_unfold (GF := GF) P)))) i =
          some (toAgree (invariant_unfold (GF := GF) P)) := by
      simp [HeapFiniteMap.get?_eq_get, Store.get_set_eq, invariant_unfold]
    exact hL.trans hR.symm
  · have hne : i ≠ k := Ne.symm hki
    have hL :
        FiniteMap.get? (inv_map (GF := GF) (FiniteMap.insert I i P)) k =
          FiniteMap.get? (inv_map (GF := GF) I) k := by
      simp [inv_map, FiniteMapLaws.get?_map, FiniteMapLaws.get?_insert_ne _ _ _ _ hne]
    have hR :
        FiniteMap.get? (Store.set (inv_map (GF := GF) I) i
          (some (toAgree (invariant_unfold (GF := GF) P)))) k =
          FiniteMap.get? (inv_map (GF := GF) I) k := by
      simp [HeapFiniteMap.get?_eq_get, Store.get_set_ne hne]
    exact hL.trans hR.symm

omit [ElemG GF (InvF GF M F)] [ElemG GF (COFE.constOF CoPsetDisj)]
    [ElemG GF (COFE.constOF GSetDisj)] in
private theorem inv_auth_alloc (I : M (IPropU GF)) (i : Positive) (P : IProp GF)
    (hI : FiniteMap.get? I i = none) :
    gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I) ~~>
      gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
        (inv_map (GF := GF) (FiniteMap.insert I i P)) •
      gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
        (toAgree (invariant_unfold (GF := GF) P)) := by
  have hget : Store.get (inv_map (GF := GF) I) i = none :=
    inv_map_get_none (I := I) (i := i) hI
  have hdq : ✓ (DFrac.discard (F := F)) := by
    simpa using (DFrac.valid_discard (F := F))
  have hval : ✓ (toAgree (invariant_unfold (GF := GF) P)) := by
    simp [Agree.valid_def, Agree.valid, Agree.validN_iff, toAgree, invariant_unfold]
  simpa [inv_map_insert] using
    (HeapView.update_one_alloc (H := M) (k := i)
      (m1 := inv_map (GF := GF) I)
      (dq := DFrac.discard) (v1 := toAgree (invariant_unfold (GF := GF) P))
      hget hdq hval)

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
    BIBase.sep
      (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
        (ownI (GF := GF) (M := M) (F := F) W i P))
      (ownE W (CoPset.singleton i)) ⊢
      BIBase.sep
        (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W) (BIBase.later P))
        (ownD W (GSet.singleton i)) := by
  classical
  iintro H
  icases H with ⟨Hsep, HownE⟩
  icases Hsep with ⟨Hwsat, HownI⟩
  icases Hwsat with ⟨%I, Hwsat⟩
  icases Hwsat with ⟨Hauth, Hbig⟩
  -- lookup the invariant body
  ihave Hlookup := (invariant_lookupE (GF := GF) (M := M) (F := F) (W := W)
      (I := I) (i := i) (P := P))
  ispecialize Hlookup $$ [Hauth, HownI]
  · isplitl [Hauth]
    · iexact Hauth
    · iexact HownI
  icases Hlookup with ⟨Hlookup, Hauth⟩
  icases Hlookup with ⟨%Q, %hI, HlaterEq⟩
  -- peel off the map entry for `i`
  ihave Hbig' := (wrapEntails (GF := GF) (big_sepM_delete
      (Φ := fun i Q =>
        BIBase.or
          (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
          (ownE W (CoPset.singleton i)))
      (m := I) (i := i) (x := Q) hI).mp) $$ Hbig
  icases Hbig' with ⟨Hentry, Hrest⟩
  icases Hentry with (Hclosed | Hopen)
  · -- closed case: swap tokens, extract ▷P
    icases Hclosed with ⟨HlaterQ, HownD⟩
    ihave HlaterP := (wrapEntails (GF := GF) (later_eq_elim (P := Q) (Q := P))) $$ [HlaterQ, HlaterEq]
    · isplitl [HlaterQ]
      · iexact HlaterQ
      · iexact HlaterEq
    -- build wsat with the entry opened via `ownE`
    isplitr [HownD]
    · isplitr [HlaterP]
      · iexists I
        isplitl [Hauth]
        · iexact Hauth
        · iapply (wrapEntails (GF := GF) (big_sepM_delete
            (Φ := fun i Q =>
              BIBase.or
                (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
                (ownE W (CoPset.singleton i)))
            (m := I) (i := i) (x := Q) hI).mpr)
          isplitl [HownE]
          · iright; iexact HownE
          · iexact Hrest
      · iexact HlaterP
    · iexact HownD
  · -- open case: duplicate enabled token is impossible
    iexfalso
    iapply (wrapEntails (GF := GF) (ownE_singleton_twice (W := W) i))
    isplitl [HownE]
    · iexact HownE
    · iexact Hopen

/-- Close an invariant: given world satisfaction, invariant ownership,
    the later'd content, and the disabled token, return the enabled token.

    Proof strategy: dual of `ownI_open` — put the content back into the big sep,
    swap disabled for enabled. -/
theorem ownI_close (i : Positive) (P : IProp GF) :
    BIBase.sep
      (BIBase.sep
        (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
          (ownI (GF := GF) (M := M) (F := F) W i P))
        (BIBase.later P))
      (ownD W (GSet.singleton i)) ⊢
      BIBase.sep (wsat (GF := GF) (M := M) (F := F) W) (ownE W (CoPset.singleton i)) := by
  classical
  iintro H
  icases H with ⟨Hsep, HownD⟩
  icases Hsep with ⟨Hsep, HlaterP⟩
  icases Hsep with ⟨Hwsat, HownI⟩
  icases Hwsat with ⟨%I, Hwsat⟩
  icases Hwsat with ⟨Hauth, Hbig⟩
  -- lookup the invariant body
  ihave Hlookup := (invariant_lookupE (GF := GF) (M := M) (F := F) (W := W)
      (I := I) (i := i) (P := P))
  ispecialize Hlookup $$ [Hauth, HownI]
  · isplitl [Hauth]
    · iexact Hauth
    · iexact HownI
  icases Hlookup with ⟨Hlookup, Hauth⟩
  icases Hlookup with ⟨%Q, %hI, HlaterEq⟩
  -- peel off the map entry for `i`
  ihave Hbig' := (wrapEntails (GF := GF) (big_sepM_delete
      (Φ := fun i Q =>
        BIBase.or
          (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
          (ownE W (CoPset.singleton i)))
      (m := I) (i := i) (x := Q) hI).mp) $$ Hbig
  icases Hbig' with ⟨Hentry, Hrest⟩
  icases Hentry with (Hclosed | Hopen)
  · -- closed case: duplicate disabled token
    iexfalso
    iapply (wrapEntails (GF := GF) (ownD_singleton_twice (W := W) i))
    isplitl [HownD]
    · iexact HownD
    · icases Hclosed with ⟨_, HownD'⟩
      iexact HownD'
  · -- open case: close with ▷P and ownD, return ownE
    -- rewrite ▷P to ▷Q using the later equality
    ihave HlaterEq' := (wrapEntails (GF := GF) (later_eq_symm (P := P) (Q := Q))) $$ HlaterEq
    ihave HlaterQ := (wrapEntails (GF := GF) (later_eq_elim (P := P) (Q := Q))) $$ [HlaterP, HlaterEq']
    · isplitl [HlaterP]
      · iexact HlaterP
      · iexact HlaterEq'
    -- build wsat with the entry closed
    isplitr [Hopen]
    · iexists I
      isplitl [Hauth]
      · iexact Hauth
      · iapply (wrapEntails (GF := GF) (big_sepM_delete
          (Φ := fun i Q =>
            BIBase.or
              (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
              (ownE W (CoPset.singleton i)))
          (m := I) (i := i) (x := Q) hI).mpr)
        isplitl [HlaterQ HownD]
        · ileft
          isplitl [HlaterQ]
          · iexact HlaterQ
          · iexact HownD
        · iexact Hrest
    · iexact Hopen

/-! ## Allocation -/

set_option linter.unnecessarySimpa false in
/-- Allocate a fresh invariant name satisfying predicate `φ`.
    Given world satisfaction and `▷ P`, produces a fresh name `i` with
    `φ i`, updated world satisfaction, and `ownI i P`. -/
theorem ownI_alloc (φ : Positive → Prop) (P : IProp GF)
    (hfresh : ∀ E : GSet, ∃ i, ¬E.mem i ∧ φ i) :
    BIBase.sep (wsat (GF := GF) (M := M) (F := F) W) (BIBase.later P) ⊢
      BUpd.bupd (BIBase.exists fun i =>
        BIBase.sep (BIBase.pure (φ i))
          (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
            (ownI (GF := GF) (M := M) (F := F) W i P))) := by
  classical
  iintro H
  icases H with ⟨Hwsat, HlaterP⟩
  -- unwrap `wsat` as an existential via `IntoExists`
  ihave Hwsat' := (wrapEntails (GF := GF)
      (into_exists (PROP := IProp GF)
        (P := wsat (GF := GF) (M := M) (F := F) W)
        (Φ := fun I : M (IPropU GF) =>
          BIBase.sep
            (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name <|
              gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I))
            (big_sepM (PROP := IProp GF)
              (fun i Q =>
                BIBase.or
                  (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
                  (ownE W (CoPset.singleton i)))
              I)))) $$ Hwsat
  icases Hwsat' with ⟨%I, Hwsat⟩
  icases Hwsat with ⟨Hauth, Hbig⟩

  -- prepare the fresh allocation predicate
  have Hfresh' : ∀ E : GSet, ∃ i, ¬E.mem i ∧ (FiniteMap.get? I i = none ∧ φ i) := by
    intro E
    let domI : GSet := ⟨fun k => (FiniteMap.get? I k).isSome⟩
    obtain ⟨i, hi, hiφ⟩ := hfresh (E ∪ domI)
    refine ⟨i, ?_, ?_⟩
    · intro hmem
      exact hi (Or.inl hmem)
    · have hnotDom : ¬ domI.mem i := by
        intro hmem
        exact hi (Or.inr hmem)
      have hnone : FiniteMap.get? I i = none := by
        cases hget : FiniteMap.get? I i with
        | none => rfl
        | some v =>
            have : domI.mem i := by simp [domI, hget]
            exact (hnotDom this).elim
      exact ⟨hnone, hiφ⟩

  -- allow two extra nested bupds (for updateP and auth update)
  iapply BIUpdate.trans
  iapply BIUpdate.trans

  -- first bupd: allocate the disabled token cell
  iapply (wrapEntails (GF := GF) (bupd_wand_l (P := ownD W (∅ : GSet))))
  isplitr []
  · iintro HownD0
    -- second bupd: update empty disabled tokens to a fresh singleton
    let updP : IProp GF :=
      BIBase.exists fun Y : GSetDisj =>
        BIBase.sep
          (BIBase.pure (∃ i, Y = GSetDisj.gset (GSet.singleton i) ∧
            (FiniteMap.get? I i = none ∧ φ i)))
          (iOwn (GF := GF) (F := COFE.constOF GSetDisj) (γ := W.disabled_name) Y)
    iapply (wrapEntails (GF := GF) (bupd_wand_l (P := updP)))
    isplitr [HownD0]
    · iintro HupdRes
      icases HupdRes with ⟨%Y, HupdRes⟩
      icases HupdRes with ⟨%hY, HownDY⟩
      rcases hY with ⟨i, hYeq, hIφ⟩
      subst hYeq
      have hnone : FiniteMap.get? I i = none := hIφ.1
      have hφ : φ i := hIφ.2
      -- third bupd: update the invariant registry auth to insert the new entry
      iapply bupd_wand_l
      isplitr [Hauth]
      · iintro Hauth'
        -- split auth and fragment
        icases (wrapEntails (GF := GF) (iOwn_op (GF := GF) (F := InvF GF M F) (γ := W.invariant_name)
            (a1 := gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
              (inv_map (GF := GF) (FiniteMap.insert I i P)))
            (a2 := gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
              (toAgree (invariant_unfold (GF := GF) P)))).mp) $$ Hauth' with ⟨Hauth1, Hfrag⟩
        -- assemble the result
        iexists i
        isplit
        · ipure_intro; exact hφ
        · -- wsat ∗ ownI
          isplitl [Hauth1 Hbig HownDY HlaterP]
          · -- wsat
            iexists (FiniteMap.insert I i P)
            isplitl [Hauth1]
            · iexact Hauth1
            · iapply (wrapEntails (GF := GF) (big_sepM_insert
                (Φ := fun i Q =>
                  BIBase.or
                    (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
                    (ownE W (CoPset.singleton i)))
                (m := I) (i := i) (x := P) hnone).mpr)
              isplitl [HlaterP HownDY]
              · ileft
                isplitl [HlaterP]
                · iexact HlaterP
                · simpa [ownD] using HownDY
              · iexact Hbig
          · -- ownI
            simpa [ownI] using Hfrag
      · -- build the update on the auth map
        iapply (wrapEntails (GF := GF) (iOwn_update (GF := GF) (F := InvF GF M F) (γ := W.invariant_name)
          (a := gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
            (inv_map (GF := GF) I))
          (a' := gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
              (inv_map (GF := GF) (FiniteMap.insert I i P)) •
            gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
              (toAgree (invariant_unfold (GF := GF) P)))
          (inv_auth_alloc (I := I) (i := i) (P := P) hnone)))
        iexact Hauth
    · -- update the disabled tokens
      iapply (wrapEntails (GF := GF) (iOwn_updateP (GF := GF) (F := COFE.constOF GSetDisj) (γ := W.disabled_name)
        (a := GSetDisj.gset (∅ : GSet))
        (P := fun Y => ∃ i, Y = GSetDisj.gset (GSet.singleton i) ∧
          (FiniteMap.get? I i = none ∧ φ i))
        (gset_disj_alloc_empty_updateP_strong'
          (P := fun i => FiniteMap.get? I i = none ∧ φ i) Hfresh')))
      simpa [ownD] using HownD0
  · iapply (ownD_emptyE (W := W))
    iemp_intro

set_option linter.unnecessarySimpa false in
/-- Allocate a fresh invariant and immediately open it.
    Returns the fresh name, a closing wand, `ownI`, and `ownD`. -/
theorem ownI_alloc_open (φ : Positive → Prop) (P : IProp GF)
    (hfresh : ∀ E : GSet, ∃ i, ¬E.mem i ∧ φ i) :
    BUpd.bupd (wsat (GF := GF) (M := M) (F := F) W) ⊢
      BUpd.bupd (BIBase.exists fun i =>
        BIBase.sep (BIBase.pure (φ i))
          (BIBase.sep
            (BIBase.wand (ownE W (CoPset.singleton i))
              (wsat (GF := GF) (M := M) (F := F) W))
            (BIBase.sep
              (ownI (GF := GF) (M := M) (F := F) W i P)
              (ownD W (GSet.singleton i))))) := by
  classical
  -- reduce to a single bupd on the inside
  refine (BIUpdate.mono ?_).trans BIUpdate.trans
  iintro Hwsat
  ihave Hwsat' := (wrapEntails (GF := GF)
      (into_exists (PROP := IProp GF)
        (P := wsat (GF := GF) (M := M) (F := F) W)
        (Φ := fun I : M (IPropU GF) =>
          BIBase.sep
            (iOwn (GF := GF) (F := InvF GF M F) W.invariant_name <|
              gmap_view_auth (GF := GF) (M := M) (F := F) (.own one) (inv_map (GF := GF) I))
            (big_sepM (PROP := IProp GF)
              (fun i Q =>
                BIBase.or
                  (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
                  (ownE W (CoPset.singleton i)))
              I)))) $$ Hwsat
  icases Hwsat' with ⟨%I, Hwsat⟩
  icases Hwsat with ⟨Hauth, Hbig⟩

  have Hfresh' : ∀ E : GSet, ∃ i, ¬E.mem i ∧ (FiniteMap.get? I i = none ∧ φ i) := by
    intro E
    let domI : GSet := ⟨fun k => (FiniteMap.get? I k).isSome⟩
    obtain ⟨i, hi, hiφ⟩ := hfresh (E ∪ domI)
    refine ⟨i, ?_, ?_⟩
    · intro hmem
      exact hi (Or.inl hmem)
    · have hnotDom : ¬ domI.mem i := by
        intro hmem
        exact hi (Or.inr hmem)
      have hnone : FiniteMap.get? I i = none := by
        cases hget : FiniteMap.get? I i with
        | none => rfl
        | some v =>
            have : domI.mem i := by simp [domI, hget]
            exact (hnotDom this).elim
      exact ⟨hnone, hiφ⟩

  -- allow two extra nested bupds (for updateP and auth update)
  iapply BIUpdate.trans
  iapply BIUpdate.trans

  -- first bupd: allocate the disabled token cell
  iapply (wrapEntails (GF := GF) (bupd_wand_l (P := ownD W (∅ : GSet))))
  isplitr []
  · iintro HownD0
    -- second bupd: update empty disabled tokens to a fresh singleton
    let updP : IProp GF :=
      BIBase.exists fun Y : GSetDisj =>
        BIBase.sep
          (BIBase.pure (∃ i, Y = GSetDisj.gset (GSet.singleton i) ∧
            (FiniteMap.get? I i = none ∧ φ i)))
          (iOwn (GF := GF) (F := COFE.constOF GSetDisj) (γ := W.disabled_name) Y)
    iapply (wrapEntails (GF := GF) (bupd_wand_l (P := updP)))
    isplitr [HownD0]
    · iintro HupdRes
      icases HupdRes with ⟨%Y, HupdRes⟩
      icases HupdRes with ⟨%hY, HownDY⟩
      rcases hY with ⟨i, hYeq, hIφ⟩
      subst hYeq
      have hnone : FiniteMap.get? I i = none := hIφ.1
      have hφ : φ i := hIφ.2
      -- third bupd: update the invariant registry auth to insert the new entry
      iapply bupd_wand_l
      isplitr [Hauth]
      · iintro Hauth'
        icases (wrapEntails (GF := GF) (iOwn_op (GF := GF) (F := InvF GF M F) (γ := W.invariant_name)
            (a1 := gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
              (inv_map (GF := GF) (FiniteMap.insert I i P)))
            (a2 := gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
              (toAgree (invariant_unfold (GF := GF) P)))).mp) $$ Hauth' with ⟨Hauth1, Hfrag⟩
        iexists i
        isplit
        · ipure_intro; exact hφ
        · isplitr [Hfrag HownDY]
          · -- wand for closing
            iintro HownE
            iexists (FiniteMap.insert I i P)
            isplitl [Hauth1]
            · iexact Hauth1
            · iapply (wrapEntails (GF := GF) (big_sepM_insert
                (Φ := fun i Q =>
                  BIBase.or
                    (BIBase.sep (BIBase.later Q) (ownD W (GSet.singleton i)))
                    (ownE W (CoPset.singleton i)))
                (m := I) (i := i) (x := P) hnone).mpr)
              isplitl [HownE]
              · iright; iexact HownE
              · iexact Hbig
          · -- ownI ∗ ownD
            isplitl [Hfrag]
            · simpa [ownI] using Hfrag
            · simpa [ownD] using HownDY
      · -- build the update on the auth map
        iapply (wrapEntails (GF := GF) (iOwn_update (GF := GF) (F := InvF GF M F) (γ := W.invariant_name)
          (a := gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
            (inv_map (GF := GF) I))
          (a' := gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
              (inv_map (GF := GF) (FiniteMap.insert I i P)) •
            gmap_view_frag (GF := GF) (M := M) (F := F) i .discard
              (toAgree (invariant_unfold (GF := GF) P)))
          (inv_auth_alloc (I := I) (i := i) (P := P) hnone)))
        iexact Hauth
    · -- update the disabled tokens
      iapply (wrapEntails (GF := GF) (iOwn_updateP (GF := GF) (F := COFE.constOF GSetDisj) (γ := W.disabled_name)
        (a := GSetDisj.gset (∅ : GSet))
        (P := fun Y => ∃ i, Y = GSetDisj.gset (GSet.singleton i) ∧
          (FiniteMap.get? I i = none ∧ φ i))
        (gset_disj_alloc_empty_updateP_strong'
          (P := fun i => FiniteMap.get? I i = none ∧ φ i) Hfresh')))
      simpa [ownD] using HownD0
  · iapply (ownD_emptyE (W := W))
    iemp_intro

/-! ## Initial World -/

/-- Allocate the initial world satisfaction and top-level enabled mask.
    This is the entry point: from nothing, produce `wsat ∗ ownE ⊤`. -/
theorem wsat_alloc :
    (BIBase.emp : IProp GF) ⊢
      BUpd.bupd (BIBase.exists fun W' : WsatGS GF =>
        BIBase.sep (wsat (GF := GF) (M := M) (F := F) W') (ownE W' CoPset.top)) := by
  classical
  -- allocate the three ghost cells
  let aI :=
    gmap_view_auth (GF := GF) (M := M) (F := F) (.own one)
      (inv_map (GF := GF) (∅ : M (IPropU GF)))
  let aE : CoPsetDisj := CoPsetDisj.coPset CoPset.top
  let aD : GSetDisj := GSetDisj.gset (∅ : GSet)
  have hI : ✓ aI := by
    simpa [aI, gmap_view_auth] using
      (HeapView.auth_one_valid (F := F) (H := M)
        (m1 := inv_map (GF := GF) (∅ : M (IPropU GF))))
  have hE : ✓ aE := by
    simp [aE, CMRA.Valid]
  have hD : ✓ aD := by
    simp [aD, CMRA.Valid]

  refine emp_sep.mpr.trans <|
    (sep_mono (iOwn_alloc (GF := GF) (F := COFE.constOF GSetDisj) aD hD) .rfl).trans ?_
  refine emp_sep.mpr.trans <|
    (sep_mono (iOwn_alloc (GF := GF) (F := COFE.constOF CoPsetDisj) aE hE) .rfl).trans ?_
  refine emp_sep.mpr.trans <|
    (sep_mono (iOwn_alloc (GF := GF) (F := InvF GF M F) aI hI) .rfl).trans ?_

  -- combine the bupds
  refine ((@sep_mono (PROP := IProp GF)) .rfl (sep_assoc (PROP := IProp GF)).2).trans ?_
  refine ((@sep_mono (PROP := IProp GF)) .rfl sep_emp.mp).trans ?_
  refine ((@sep_mono (PROP := IProp GF)) .rfl bupd_sep).trans ?_
  refine (bupd_sep (PROP := IProp GF)).trans ?_

  refine (BIUpdate.mono (PROP := IProp GF) ?_)
  istart
  iintro Halloc
  icases Halloc with ⟨HγI, Hrest⟩
  icases HγI with ⟨%γI, HγI⟩
  icases Hrest with ⟨HγE, HγD⟩
  icases HγE with ⟨%γE, HγE⟩
  icases HγD with ⟨%γD, HγD⟩
  haveI : CMRA.CoreId aD := by
    refine ⟨by rfl⟩
  icases HγD with #HγD
  let W' : WsatGS GF := { invariant_name := γI, enabled_name := γE, disabled_name := γD }
  iexists W'
  isplitr [HγE]
  · -- wsat for the empty map
    iexists (∅ : M (IPropU GF))
    isplitl [HγI]
    · iexact HγI
    · simp [big_sepM_empty]
      iemp_intro
  · -- enabled mask at top
    simp [ownE]
    iexact HγE

end Iris.BaseLogic
