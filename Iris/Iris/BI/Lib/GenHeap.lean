module
public import Iris.Algebra
public import Iris.Algebra.ReservationMap
public import Iris.BI.Lib.Fractional
public import Iris.Instances.Lib.GhostMap
public import Iris.Instances.IProp
public import Iris.Std.HeapInstances
public import Iris.Std.Namespaces

@[expose] public section

namespace Iris

open Std Iris.Algebra CMRA BI ProofMode

/-! This file provides a generic mechanism for a language-level points-to
connective `l ↦{dq} v` reflecting the physical heap.  This library is designed
to be used as a singleton (i.e., with only a single instance existing in any
proof), with the `genHeapGS` typeclass providing the ghost names of that
unique instance.  That way, `pointsTo` does not need an explicit `gname`
parameter.  This mechanism can be plugged into a language and related to the
physical heap by using `genHeapInterp σ` in the state interpretation of the
weakest precondition.  See heap-lang for an example.

In addition to the points-to connective, this library also provides a way to
attach "meta" or "ghost" data to locations via `metaToken l E` and
`metaInfo l N x`.  See the original Rocq `gen_heap.v` for the full design
rationale.  To implement the meta machinery we use two extra pieces of ghost
state in addition to the value map:

- a `ghost_map L gname`, which associates a ghost name with each location;
- for each such ghost name, a `ReservationMap (Agree (LeibnizO Pos))` storing
  the actual meta data.  The indirection is required so that `meta_set` is a
  frame-preserving update that does not need to inspect `genHeapInterp`. -/

/-- Underlying partial-map type used inside the per-location reservation map.
Following the convention from `WSat`, we fix the representation to extensional
tree maps over positives. -/
abbrev MetaResMap (x : Type) : Type := Std.ExtTreeMap Pos x compare

/-- The CMRA used to store the meta-data attached to a single location. -/
abbrev MetaUR : Type := ReservationMap (Agree (LeibnizO Pos)) MetaResMap

variable (F : outParam (Type _)) [UFraction F]

@[rocq_alias gen_heapGpreS]
class genHeapPreS (L V : Type _) (GF : BundledGFunctors) (H : outParam <| Type _ → Type _)
    [Std.LawfulFiniteMap H L] where
  heap : GhostMapG GF F L V H
  «meta» : GhostMapG GF F L GName H
  metaData : ElemG GF (constOF MetaUR)

attribute [reducible, instance] genHeapPreS.heap
attribute [reducible, instance] genHeapPreS.«meta»
attribute [reducible, instance] genHeapPreS.metaData
attribute [instance] GhostMapG.elem

@[rocq_alias gen_heapGS]
class genHeapGS (L V : outParam <| Type _) (GF : outParam <| BundledGFunctors)
    (H : outParam <| Type _ → Type _) [Std.LawfulFiniteMap H L]
    extends genHeapPreS F L V GF H where
  heapName : GName
  metaName : GName

#rocq_ignore «gen_heapΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore «subG_gen_heapGpreS» "Subsumed by BundledGFunctors typeclass synthesis"

section definitions

variable {GF : BundledGFunctors} {L V : Type _}
variable {H : outParam <| Type _ → Type _} [Std.LawfulFiniteMap H L]
variable {F : outParam (Type _)} [UFraction F]
variable [genHeapGS F L V GF H]

open Std.FiniteMap Std.PartialMap genHeapGS

/-- State interpretation for the generalized heap.  Owns the value map `σ`
together with an existentially quantified map of ghost names whose domain is
contained in that of `σ`; the latter is used as the indirection table for the
meta data. -/
@[rocq_alias gen_heap_interp]
def genHeapInterp (σ : H V) : IProp GF := iprop(
  ∃ m : H GName,
    ⌜∀ k, dom m k → dom σ k⌝ ∗
    (heapName ↪●MAP σ) ∗
    (metaName ↪●MAP m))

@[rocq_alias pointsto]
def pointsTo (l : L) (dq : DFrac F) (v : V) : IProp GF := heapName ↪◯MAP[l]{dq} v

notation l " ↦{" dq "} " v => pointsTo l dq v
notation l " ↦ " v => pointsTo l (DFrac.own 1) v

/-- The token witnessing that no meta data has been associated with the
namespace mask `E` at location `l`. -/
@[rocq_alias meta_token]
def metaToken (l : L) (E : CoPset) : IProp GF := iprop(
  ∃ γm, (metaName ↪◯MAP[l]{.discard} γm) ∗
    iOwn (E := genHeapPreS.metaData (L := L) (V := V)) γm (ReservationMap.mkToken E))

/-- Persistent assertion that the meta-data `x : A` has been associated with
namespace `N` to the location `l`.  The type `A` must be `Pos.Countable`.

The Rocq name is `meta`, but that token is reserved in Lean, so the Lean
identifier is `metaInfo`. -/
@[rocq_alias «meta»]
def metaInfo {A : Type _} [Pos.Countable A] (l : L) (N : Namespace) (x : A) : IProp GF := iprop(
  ∃ γm, (metaName ↪◯MAP[l]{.discard} γm) ∗
    iOwn (E := genHeapPreS.metaData (L := L) (V := V)) γm
      (ReservationMap.singleton (CoPset.pick (↑N))
        (toAgree ⟨Pos.Countable.encode x⟩ : Agree (LeibnizO Pos))))

end definitions

section lemmas

variable {F : outParam (Type _)} [UFraction F] {GF : BundledGFunctors}
variable {L V : Type _} {H : outParam <| Type _ → Type _} [Std.LawfulFiniteMap H L]
variable [genHeapGS F L V GF H]

open genHeapGS Std.PartialMap Std.FiniteMap

/-! ### General properties of `pointsTo` -/

@[rocq_alias pointsto_timeless]
instance instTimelessPointsTo : BI.Timeless (l ↦{dq} v) :=
  inferInstanceAs (BI.Timeless (heapName ↪◯MAP[l]{dq} v))

@[rocq_alias pointsto_fractional]
instance instFractionalPointsTo : Fractional (l ↦{.own ·} v) :=
  inferInstanceAs (Fractional (heapName ↪◯MAP[l]{.own ·} v))

@[rocq_alias pointsto_as_fractional]
instance instAsFractionalPointsTo : AsFractional (l ↦{.own q} v) (l ↦{.own ·} v) q :=
  inferInstanceAs (AsFractional (heapName ↪◯MAP[l]{.own q} v) (heapName ↪◯MAP[l]{.own ·} v) q)

@[rocq_alias pointsto_valid]
theorem pointsTo_cmraValid : (l ↦{dq} v) ⊢@{IProp GF} internalCmraValid dq := by
  simp [pointsTo, ghost_map_elem_valid]

@[rocq_alias pointsto_valid_2]
theorem pointsTo_op_cmraValid :
    (l ↦{dq₁} v₁) ∗ (l ↦{dq₂} v₂) ⊢@{IProp GF} internalCmraValid (dq₁ • dq₂) ∧ ⌜v₁ = v₂⌝ := by
  unfold pointsTo
  iapply ghost_map_elem_valid_2

@[rocq_alias pointsto_agree]
theorem pointsTo_agree : (l ↦{dq₁} v₁) ∗ (l ↦{dq₂} v₂) ⊢@{IProp GF} ⌜v₁ = v₂⌝ := by
  unfold pointsTo
  iapply ghost_map_elem_agree

/-! ### General properties of `metaInfo` and `metaToken` -/

@[rocq_alias meta_token_timeless]
instance instTimelessMetaToken (l : L) (E : CoPset) :
    BI.Timeless (PROP := IProp GF) (metaToken l E) := by
  unfold metaToken
  refine @BI.exists_timeless _ _ _ _ ?_
  intro γm
  infer_instance

@[rocq_alias meta_timeless]
instance instTimelessMeta {A : Type _} [Pos.Countable A] (l : L) (N : Namespace) (x : A) :
    BI.Timeless (PROP := IProp GF) (metaInfo l N x) := by
  unfold metaInfo
  refine @BI.exists_timeless _ _ _ _ ?_
  intro γm
  infer_instance

@[rocq_alias meta_persistent]
instance instPersistentMeta {A : Type _} [Pos.Countable A] (l : L) (N : Namespace) (x : A) :
    BI.Persistent (PROP := IProp GF) (metaInfo l N x) := by
  unfold metaInfo
  refine @BI.exists_persistent _ _ _ _ ?_
  intro γm
  infer_instance

@[rocq_alias meta_token_union_1]
theorem metaToken_union_1 {l : L} {E1 E2 : CoPset} (he : E1 ## E2) :
    metaToken (GF := GF) l (E1 ∪ E2) ⊢ metaToken l E1 ∗ metaToken l E2 := by
  unfold metaToken
  iintro ⟨%γm, #Hγm, Hm⟩
  ihave ⟨Hm1, Hm2⟩ : iprop(
      iOwn (E := genHeapPreS.metaData (L := L) (V := V)) γm (ReservationMap.mkToken E1) ∗
      iOwn (E := genHeapPreS.metaData (L := L) (V := V)) γm (ReservationMap.mkToken E2)) $$ [Hm]
  · iapply iOwn_op.mp
    iapply (BI.equiv_iff.mp (iOwn_ne.eqv (ReservationMap.token_union he))).mp
    iexact Hm
  isplitl [Hm1]
  · iexists γm
    iframe Hγm Hm1
  · iexists γm
    iframe Hγm Hm2

@[rocq_alias meta_token_union_2]
theorem metaToken_union_2 {l : L} {E1 E2 : CoPset} :
    metaToken (GF := GF) l E1 -∗ metaToken l E2 -∗ metaToken l (E1 ∪ E2) := by
  unfold metaToken
  iintro ⟨%γm1, #Hγm1, Hm1⟩ ⟨%γm2, #Hγm2, Hm2⟩
  icombine Hγm1 Hγm2 gives ⟨%_, %Heq⟩
  subst Heq
  icombine Hm1 Hm2 gives %Hvalid
  have hdisj : E1 ## E2 := ReservationMap.valid_token_op_iff_disj.mp Hvalid
  iexists γm1
  iframe Hγm1
  iapply (BI.equiv_iff.mp (iOwn_ne.eqv (ReservationMap.token_union hdisj))).mpr
  iapply iOwn_op.mpr
  iframe

@[rocq_alias meta_token_union]
theorem metaToken_union {l : L} {E1 E2 : CoPset} (he : E1 ## E2) :
    metaToken (GF := GF) l (E1 ∪ E2) ⊣⊢ metaToken l E1 ∗ metaToken l E2 := by
  refine ⟨metaToken_union_1 he, ?_⟩
  iintro ⟨H1, H2⟩
  iapply metaToken_union_2 $$ H1 H2

@[rocq_alias meta_token_valid_2]
theorem metaToken_valid_2 {l : L} {E1 E2 : CoPset} :
    metaToken (GF := GF) l E1 -∗ metaToken l E2 -∗ ⌜E1 ## E2⌝ := by
  unfold metaToken
  iintro ⟨%γm1, #Hγm1, Hm1⟩ ⟨%γm2, #Hγm2, Hm2⟩
  icombine Hγm1 Hγm2 gives ⟨%_, %Heq⟩
  subst Heq
  icombine Hm1 Hm2 gives %Hvalid
  ipureintro
  exact ReservationMap.valid_token_op_iff_disj.mp Hvalid

@[rocq_alias meta_token_combine_as]
instance instCombineSepGivesMetaToken (l : L) (E1 E2 : CoPset) :
    CombineSepGives (PROP := IProp GF) (metaToken l E1) (metaToken l E2) iprop(⌜E1 ## E2⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases metaToken_valid_2 $$ H1 H2 with %H
    itrivial

@[rocq_alias meta_token_difference]
theorem metaToken_difference {l : L} {E1 E2 : CoPset} (he : E1 ⊆ E2) :
    metaToken (GF := GF) l E2 ⊣⊢ metaToken l E1 ∗ metaToken l (E2 \ E1) := by
  have heq : E1 ∪ (E2 \ E1) = E2 := Iris.Std.LawfulSet.subset_union_diff he
  refine .trans (.of_eq ?_) (metaToken_union (l := l) Iris.Std.LawfulSet.disjoint_diff_right)
  rw [heq]

@[rocq_alias meta_agree]
theorem meta_agree {A : Type _} [Pos.Countable A] {l : L} {N : Namespace} {x1 x2 : A} :
    metaInfo (GF := GF) l N x1 -∗ metaInfo l N x2 -∗ ⌜x1 = x2⌝ := by
  unfold metaInfo
  iintro ⟨%γm1, #Hγm1, Hm1⟩ ⟨%γm2, #Hγm2, Hm2⟩
  icombine Hγm1 Hγm2 gives ⟨%_, %Heq⟩
  subst Heq
  icombine Hm1 Hm2 gives %Hvalid
  ipureintro
  have hop : ✓ ReservationMap.singleton (H := MetaResMap) (CoPset.pick (↑N))
      ((toAgree ⟨Pos.Countable.encode x1⟩ : Agree (LeibnizO Pos)) •
        (toAgree ⟨Pos.Countable.encode x2⟩ : Agree (LeibnizO Pos))) :=
    (OFE.Equiv.valid (ReservationMap.singleton_op _ _ _)).mpr Hvalid
  rw [ReservationMap.valid_singleton] at hop
  have hag : (⟨Pos.Countable.encode x1⟩ : LeibnizO Pos) = ⟨Pos.Countable.encode x2⟩ :=
    toAgree_op_valid_iff_eq.mp hop
  exact Pos.encode_inj (congrArg LeibnizO.car hag)

@[rocq_alias meta_set]
theorem meta_set {A : Type _} [Pos.Countable A] {l : L} {E : CoPset} {N : Namespace} (x : A)
    (he : (↑N : CoPset) ⊆ E) : metaToken (GF := GF) l E ==∗ metaInfo l N x := by
  unfold metaToken metaInfo
  iintro ⟨%γm, #Hγm, Hm⟩
  imod iOwn_update (ReservationMap.alloc (a := toAgree (⟨Pos.Countable.encode x⟩ : LeibnizO Pos))
    (he _ (coPpick_nclose N)) Agree.toAgree_valid) $$ Hm with Hm
  imodintro
  iexists γm
  iframe Hγm Hm

/-! ### Update lemmas -/

section updateLemmas

@[rocq_alias gen_heap_alloc]
theorem genHeap_alloc {σ : H V} {l : L} {v : V} (Hσl : get? σ l = .none) :
    genHeapInterp σ ⊢ |==> (genHeapInterp (insert σ l v) ∗ (l ↦ v) ∗ metaToken l ⊤) := by
  unfold genHeapInterp pointsTo metaToken
  iintro ⟨%m, %Hdom, Hσ, Hm⟩
  imod ghost_map_insert l v Hσl $$ Hσ with ⟨Hσ, Hl⟩
  imod (iOwn_alloc (E := genHeapPreS.metaData (L := L) (V := V))
    (ReservationMap.mkToken ⊤) ReservationMap.valid_token) with ⟨%γm, Hγm⟩
  have Hml : get? m l = .none := by
    rcases h : get? m l with _ | _
    · rfl
    · exfalso
      have : dom m l := by simp [dom, h]
      have := Hdom l this
      simp [dom, Hσl] at this
  imod ghost_map_insert_persist l γm Hml $$ Hm with ⟨Hm, Hlm⟩
  imodintro
  isplitl [Hσ Hm]
  · iexists (insert m l γm)
    isplitr
    · ipureintro
      intro k hk
      simp only [dom] at hk ⊢
      by_cases hkl : k = l
      · subst hkl
        rw [LawfulPartialMap.get?_insert_eq rfl]
        rfl
      · rw [LawfulPartialMap.get?_insert_ne (Ne.symm hkl)] at hk
        rw [LawfulPartialMap.get?_insert_ne (Ne.symm hkl)]
        exact Hdom k hk
    · iframe
  · isplitl [Hl]
    · iframe
    · iexists γm
      iframe Hlm Hγm

@[rocq_alias gen_heap_valid]
theorem genHeap_valid {σ : H V} {l : L} {dq : DFrac F} {v : V} :
    (genHeapInterp σ ∗ l ↦{dq} v) ==∗ ⌜get? σ l = .some v⌝ := by
  unfold genHeapInterp pointsTo
  iintro ⟨⟨%m, -, Hσ, -⟩, Hl⟩
  iapply ghost_map_lookup $$ Hσ Hl

@[rocq_alias gen_heap_update]
theorem genHeap_update {σ : H V} {l : L} {v₁ v₂ : V} :
    (genHeapInterp σ ∗ l ↦ v₁) ==∗ (genHeapInterp (insert σ l v₂) ∗ l ↦ v₂) := by
  unfold genHeapInterp pointsTo
  iintro ⟨⟨%m, %Hdom, Hσ, Hm⟩, Hl⟩
  imod ghost_map_update l v₁ v₂ $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  isplitl [Hσ Hm]
  · iexists m
    isplitr
    · ipureintro
      intro k hk
      simp only [dom] at hk ⊢
      by_cases hkl : k = l
      · subst hkl
        rw [LawfulPartialMap.get?_insert_eq rfl]
        rfl
      · rw [LawfulPartialMap.get?_insert_ne (Ne.symm hkl)]
        exact Hdom k hk
    · iframe
  · iframe

end updateLemmas

end lemmas

end Iris
