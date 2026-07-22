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
- for each such ghost name, a `ReservationMap (Agree (DiscreteO Pos))` storing
  the actual meta data.  The indirection is required so that `meta_set` is a
  frame-preserving update that does not need to inspect `genHeapInterp`. -/

/-- Underlying partial-map type used inside the per-location reservation map.
Following the convention from `WSat`, we fix the representation to extensional
tree maps over positives. -/
abbrev MetaResMap (x : Sort _) : Sort _ := Std.ExtTreeMap Pos x compare

/-- The CMRA used to store the meta-data attached to a single location. -/
abbrev MetaUR : Sort _ := ReservationMap (Agree (DiscreteO Pos)) MetaResMap

@[rocq_alias gen_heapGpreS]
class genHeapPreS (L V : Type _) (GF : BundledGFunctors) (H : outParam <| Type _ → Type _)
    [Std.LawfulFiniteMap H L] where
  heap : GhostMapG GF L V H
  metaInfo : GhostMapG GF L GName H
  metaData : ElemG GF (constOF MetaUR)

attribute [reducible, instance] genHeapPreS.heap
attribute [reducible, instance] genHeapPreS.metaInfo
attribute [reducible, instance] genHeapPreS.metaData
attribute [instance] GhostMapG.elem

@[rocq_alias gen_heapGS]
class genHeapGS (L V : outParam <| Type _) (GF : outParam <| BundledGFunctors)
    (H : outParam <| Type _ → Type _) [Std.LawfulFiniteMap H L]
    extends genHeapPreS L V GF H where
  heapName : GName
  metaName : GName

#rocq_ignore «gen_heapΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore «subG_gen_heapGpreS» "Subsumed by BundledGFunctors typeclass synthesis"

section definitions

variable {GF : BundledGFunctors} {L V : Type _}
variable {H : outParam <| Type _ → Type _} [Std.LawfulFiniteMap H L]
variable [G : genHeapGS L V GF H]

open Std.FiniteMap Std.PartialMap genHeapGS

/-- State interpretation for the generalized heap.  Owns the value map `σ`
together with an existentially quantified map of ghost names whose domain is
contained in that of `σ`; the latter is used as the indirection table for the
meta data. -/
@[rocq_alias gen_heap_interp]
def genHeapInterp (σ : H V) : IProp GF := iprop%
  ∃ m : H GName, ⌜∀ k, dom m k → dom σ k⌝ ∗ (heapName ↪●MAP σ) ∗ (metaName ↪●MAP m)

@[rocq_alias pointsto]
def pointsTo (l : L) (dq : DFrac) (v : V) : IProp GF := heapName ↪◯MAP[l]{dq} v

notation:50 l:50 " ↦{" dq "} " v:50 => pointsTo l dq v
notation:50 l:50 " ↦ " v:50 => pointsTo l (DFrac.own 1) v

/-- The token witnessing that no meta data has been associated with the
namespace mask `E` at location `l`. -/
@[rocq_alias meta_token]
def metaToken (l : L) (E : CoPset) : IProp GF := iprop%
  ∃ γm, (metaName ↪◯MAP[l]{.discard} γm) ∗
    iOwn (E := genHeapPreS.metaData (L := L) (V := V)) γm (ReservationMap.mkToken E)

/-- Persistent assertion that the meta-data `x : A` has been associated with
namespace `N` to the location `l`.  The type `A` must be `Pos.Countable`. -/
@[rocq_alias «meta»]
def metaInfo [Pos.Countable A] (l : L) (N : Namespace) (x : A) : IProp GF := iprop%
  ∃ γm, (metaName ↪◯MAP[l]{.discard} γm) ∗
    iOwn (E := genHeapPreS.metaData (L := L) (V := V)) γm
      (.singleton (CoPset.pick (↑N)) (toAgree ⟨Pos.Countable.encode x⟩))

end definitions

section lemmas

variable {GF : BundledGFunctors}
variable {L V : Type _} {H : outParam <| Type _ → Type _} [Std.LawfulFiniteMap H L]
variable [genHeapGS L V GF H]

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
  inferInstanceAs
    (AsFractional (heapName ↪◯MAP[l]{.own q} v) (heapName ↪◯MAP[l]{.own ·} v) q)

@[rocq_alias pointsto_valid]
theorem pointsTo_cmraValid : l ↦{dq} v ⊢@{IProp GF} ⌜✓ dq⌝ := by
  unfold pointsTo
  iintro H
  ihave %_ := ghost_map_elem_valid $$ H
  itrivial

@[rocq_alias pointsto_valid_2]
theorem pointsTo_op_cmraValid :
    l ↦{dq₁} v₁ ∗ l ↦{dq₂} v₂ ⊢@{IProp GF} ⌜✓ (dq₁ • dq₂)⌝ ∧ ⌜v₁ = v₂⌝ := by
  unfold pointsTo
  iintro H
  ihave %_ := ghost_map_elem_valid_2 $$ H
  itrivial

@[rocq_alias pointsto_agree]
theorem pointsTo_agree : l ↦{dq₁} v₁ ∗ l ↦{dq₂} v₂ ⊢@{IProp GF} ⌜v₁ = v₂⌝ := by
  unfold pointsTo
  iapply ghost_map_elem_agree

@[rocq_alias pointsto_combine]
theorem pointsTo_combine :
    l ↦{dq₁} v₁ ∗ l ↦{dq₂} v₂ ⊢@{IProp GF} l ↦{dq₁ • dq₂} v₁ ∗ ⌜v₁ = v₂⌝ := by
  unfold pointsTo
  iintro ⟨H₁, H₂⟩
  iapply ghost_map_elem_combine $$ H₁ H₂

@[rocq_alias pointsto_frac_ne]
theorem pointsTo_frac_ne {l₁ l₂ : L} {dq₁ dq₂ : DFrac} {v₁ v₂ : V}
    (Hk : ¬ ✓ (dq₁ • dq₂)) :
    ⊢@{IProp GF} l₁ ↦{dq₁} v₁ -∗ l₂ ↦{dq₂} v₂ -∗ ⌜l₁ ≠ l₂⌝ := by
  unfold pointsTo
  iapply ghost_map_elem_frac_ne (Hk := Hk)

@[rocq_alias pointsto_ne]
theorem pointsTo_ne {l₁ l₂ : L} {dq₂ : DFrac} {v₁ v₂ : V} :
    ⊢@{IProp GF} l₁ ↦ v₁ -∗ l₂ ↦{dq₂} v₂ -∗ ⌜l₁ ≠ l₂⌝ := by
  unfold pointsTo
  iapply ghost_map_elem_ne

/-- Permanently turn any points-to predicate into a persistent points-to. -/
@[rocq_alias pointsto_persist]
theorem pointsTo_persist {l : L} {dq : DFrac} {v : V} :
    ⊢@{IProp GF} l ↦{dq} v ==∗ l ↦{.discard} v := by
  unfold pointsTo
  iapply ghost_map_elem_persist

/-- Recover fractional ownership of a read-only element. -/
@[rocq_alias pointsto_unpersist]
theorem pointsTo_unpersist {l : L} {v : V} :
    ⊢@{IProp GF} l ↦{.discard} v ==∗ ∃ q, l ↦{.own q} v := by
  unfold pointsTo
  iapply ghost_map_elem_unpersist

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
  -- TODO: why do we need to destruct in a second step?
  icases (iOwn_ne.eqv (ReservationMap.token_union he).symm) $$ Hm with Hm
  icases Hm with ⟨Hm1, Hm2⟩
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
  iapply (equiv_iff.mp (iOwn_ne.eqv (ReservationMap.token_union hdisj))).mpr
  iapply iOwn_op
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

@[rocq_alias meta_token_ne]
theorem metaToken_ne {l₁ l₂ : L} {E : CoPset} (HE : E ≠ ∅) :
    metaToken (GF := GF) l₁ ⊤ -∗ metaToken l₂ E -∗ ⌜l₁ ≠ l₂⌝ := by
  iintro H1 H2
  iintro %heq; subst heq
  icases metaToken_valid_2 $$ H1 H2 with %Hdisj
  ipureintro
  refine HE ?_
  ext p
  exact ⟨fun hp => (Hdisj p ⟨CoPset.mem_full, hp⟩).elim, fun hp => (CoPset.mem_empty hp).elim⟩

@[rocq_alias meta_token_difference]
theorem metaToken_difference {l : L} {E1 E2 : CoPset} (he : E1 ⊆ E2) :
    metaToken (GF := GF) l E2 ⊣⊢ metaToken l E1 ∗ metaToken l (E2 \ E1) := by
  have heq : E1 ∪ (E2 \ E1) = E2 := LawfulSet.subset_union_diff he
  refine .trans (.of_eq ?_) (metaToken_union (l := l) LawfulSet.disjoint_diff_right)
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
  rw [valid_iff (ReservationMap.singleton_op _ _ _).symm
    , ReservationMap.valid_singleton, toAgree_op_valid_iff_eq] at Hvalid
  exact Pos.encode_inj (DiscreteO.eqv_inj Hvalid)

@[rocq_alias meta_set]
theorem meta_set {A : Type _} [Pos.Countable A] {l : L} {E : CoPset} {N : Namespace} (x : A)
    (he : (↑N : CoPset) ⊆ E) : metaToken (GF := GF) l E ==∗ metaInfo l N x := by
  unfold metaToken metaInfo
  iintro ⟨%γm, #Hγm, Hm⟩
  imod iOwn_update (ReservationMap.alloc (a := toAgree (⟨Pos.Countable.encode x⟩ : DiscreteO Pos))
    (he _ (coPpick_nclose N)) Agree.toAgree_valid) $$ Hm with Hm
  imodintro
  iexists γm
  iframe Hγm Hm

@[rocq_alias meta_meta_token_valid]
theorem meta_metaToken_valid {A : Type _} [Pos.Countable A] {l : L} {N : Namespace} {x : A}
    {E : CoPset} :
    metaInfo (GF := GF) l N x -∗ metaToken l E -∗ ⌜¬ (↑N : CoPset) ⊆ E⌝ := by
  unfold metaInfo metaToken
  iintro ⟨%γm1, #Hγm1, Hm1⟩ ⟨%γm2, #Hγm2, Hm2⟩
  icombine Hγm1 Hγm2 gives ⟨%_, %heq⟩
  subst heq
  icombine Hm1 Hm2 gives %Hvalid
  ipureintro
  intro hsub
  cases ReservationMap.disj_of_valid_data_op_token _ E Hvalid (CoPset.pick (↑N)) with
  | inl hnone =>
    rw [LawfulPartialMap.get?_singleton_eq rfl] at hnone
    cases hnone
  | inr hnin => exact hnin (hsub _ (coPpick_nclose N))

@[rocq_alias meta_meta_token_valid']
theorem meta_metaToken_valid' {A : Type _} [Pos.Countable A] {l : L} {N : Namespace} {x : A}
    {E : CoPset} (he : (↑N : CoPset) ⊆ E) :
    metaInfo (GF := GF) l N x -∗ metaToken l E -∗ False := by
  iintro H1 H2
  icases meta_metaToken_valid $$ H1 H2 with %hnot
  exact (hnot he).elim

@[rocq_alias combine_sep_gives_meta_meta_token_1]
instance instCombineSepGivesMetaMetaToken1 {A : Type _} [Pos.Countable A]
    (l : L) (N : Namespace) (x : A) (E : CoPset) :
    CombineSepGives (PROP := IProp GF) (metaInfo l N x) (metaToken l E)
      iprop(⌜¬ (↑N : CoPset) ⊆ E⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases meta_metaToken_valid $$ H1 H2 with %H
    itrivial

@[rocq_alias combine_sep_gives_meta_meta_token_2]
instance instCombineSepGivesMetaMetaToken2 {A : Type _} [Pos.Countable A]
    (l : L) (N : Namespace) (x : A) (E : CoPset) :
    CombineSepGives (PROP := IProp GF) (metaToken l E) (metaInfo l N x)
      iprop(⌜¬ (↑N : CoPset) ⊆ E⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases meta_metaToken_valid $$ H2 H1 with %H
    itrivial

/-! ### Update lemmas -/

section updateLemmas

/-- The state interpretation transports along a pointwise equivalence of
the value heap. -/
theorem genHeapInterp_eqv {σ₁ σ₂ : H V} (h : σ₁ ≡ₘ σ₂) :
    genHeapInterp (GF := GF) σ₁ ⊢ genHeapInterp σ₂ := equiv_iff_eq.mp h ▸ .rfl

@[rocq_alias gen_heap_alloc]
theorem genHeap_alloc [DecidableEq L] {σ : H V} {l : L} {v : V} (Hσl : get? σ l = .none) :
    genHeapInterp σ ⊢ |==> (genHeapInterp (insert σ l v) ∗ l ↦ v ∗ metaToken l ⊤) := by
  unfold genHeapInterp pointsTo metaToken
  iintro ⟨%m, %Hdom, Hσ, Hm⟩
  have Hml : get? m l = .none := by
    rcases h : get? m l with _ | _
    · rfl
    · exact absurd (Hdom l (by simp [dom, h])) (by simp [dom, Hσl])
  imod ghost_map_insert l v Hσl $$ Hσ with ⟨Hσ, Hl⟩
  imod (iOwn_alloc (E := genHeapPreS.metaData L V)
    (ReservationMap.mkToken ⊤) ReservationMap.valid_token) with ⟨%γm, Hγm⟩
  imod ghost_map_insert_persist l γm Hml $$ Hm with ⟨Hm, Hlm⟩
  imodintro
  iframe Hl
  isplitl [Hσ Hm]
  · iexists (insert m l γm)
    iframe
    ipureintro
    exact fun k hk =>
      LawfulPartialMap.dom_insert_iff.mpr <|
        (LawfulPartialMap.dom_insert_iff.mp hk).imp_right (Hdom k)
  iexists γm; iframe Hlm Hγm

@[rocq_alias gen_heap_alloc_big]
theorem genHeap_alloc_big [DecidableEq L] (σ' σ : H V) (Hdisj : σ' ##ₘ σ) :
    genHeapInterp σ ⊢ |==>
      (genHeapInterp (σ' ∪ σ) ∗ ([∗map] l↦v ∈ σ', l ↦ v) ∗
        ([∗map] l↦_v ∈ σ', metaToken l ⊤)) := by
  revert σ Hdisj
  induction σ' using LawfulFiniteMap.induction_on with
  | hemp =>
    intro σ _
    iintro Hσ
    imodintro
    isplitl [Hσ]
    · iapply genHeapInterp_eqv (equiv_iff_eq.mpr LawfulPartialMap.union_empty_left.symm) $$ Hσ
    isplit <;> (iapply BigSepM.bigSepM_empty; itrivial)
  | hins l v σ'' Hl IH =>
    intro σ Hdisj
    obtain ⟨Hσl, Hdisj'⟩ := (LawfulPartialMap.disjoint_insert_left_iff Hl).mp Hdisj
    have Hunion_l : get? (σ'' ∪ σ) l = .none :=
      LawfulPartialMap.get?_union_none.mpr ⟨Hl, Hσl⟩
    iintro Hσ
    imod IH σ Hdisj' $$ Hσ with ⟨Hint, Hpts, Htok⟩
    imod genHeap_alloc Hunion_l $$ Hint with ⟨Hint', Hl_pts, Hl_tok⟩
    imodintro
    isplitl [Hint']
    · iapply genHeapInterp_eqv (equiv_iff_eq.mpr LawfulPartialMap.union_insert_left) $$ Hint'
    isplitl [Hl_pts Hpts]
    · iapply (BigSepM.bigSepM_insert Hl) $$ [$Hpts $Hl_pts]
    iapply (BigSepM.bigSepM_insert (Φ := fun l _ => iprop(metaToken l ⊤)) Hl) $$ [$Hl_tok $Htok]

@[rocq_alias gen_heap_valid]
theorem genHeap_valid {σ : H V} {l : L} {dq : DFrac} {v : V} :
    genHeapInterp σ ∗ l ↦{dq} v ==∗ ⌜get? σ l = .some v⌝ := by
  unfold genHeapInterp pointsTo
  iintro ⟨⟨%m, -, Hσ, -⟩, Hl⟩
  iapply ghost_map_lookup $$ Hσ Hl

@[rocq_alias gen_heap_update]
theorem genHeap_update [DecidableEq L] {σ : H V} {l : L} {v₁ v₂ : V} :
    genHeapInterp σ ∗ l ↦ v₁ ==∗ genHeapInterp (insert σ l v₂) ∗ l ↦ v₂ := by
  unfold genHeapInterp pointsTo
  iintro ⟨⟨%m, %Hdom, Hσ, Hm⟩, Hl⟩
  imod ghost_map_update v₂ $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  iframe Hl
  iexists m
  iframe
  ipureintro
  exact fun k hk => LawfulPartialMap.dom_insert_iff.mpr (.inr (Hdom k hk))

end updateLemmas

end lemmas

/-! ### Initialization lemmas

These build a fresh `genHeapGS` from a `genHeapPreS` and an initial heap.
-/

section init

variable {GF : BundledGFunctors}
variable {L V : Type _} {H : Type _ → Type _} [Std.LawfulFiniteMap H L]

open Std.PartialMap Std.FiniteMap

/-- Initialize `genHeapGS` with explicit ghost names.  The names of the heap
and the meta-data tables are exposed in the conclusion. -/
@[rocq_alias gen_heap_init_names]
theorem genHeap_init_names [DecidableEq L] [genHeapPreS L V GF H] (σ : H V) :
    ⊢ |==> ∃ γh γm : GName,
      genHeapInterp (G := (⟨γh, γm⟩ : genHeapGS L V GF H)) σ ∗
      ([∗map] l ↦ v ∈ σ,
        pointsTo (G := (⟨γh, γm⟩ : genHeapGS L V GF H)) l (.own 1) v) ∗
      ([∗map] l ↦ _v ∈ σ,
        metaToken (G := (⟨γh, γm⟩ : genHeapGS L V GF H)) l ⊤) := by
  imod (ghost_map_alloc_empty (K := L) (V := V)) with ⟨%γh, Hh⟩
  imod (ghost_map_alloc_empty (K := L) (V := GName)) with ⟨%γm, Hm⟩
  letI G : genHeapGS L V GF H := ⟨γh, γm⟩
  ihave Hinterp0 : genHeapInterp (G := G) ∅ $$ [Hh Hm]
  · unfold genHeapInterp
    iexists (∅ : H GName)
    isplitr
    · ipureintro
      intro k hk
      simp [dom, LawfulPartialMap.get?_empty] at hk
    iframe Hh Hm
  imod genHeap_alloc_big σ ∅ (LawfulPartialMap.disjoint_empty_right _) $$ Hinterp0
    with ⟨Hinterp, Hpts, Htok⟩
  imodintro
  iexists γh, γm
  iframe Hpts Htok
  iapply genHeapInterp_eqv (equiv_iff_eq.mpr LawfulPartialMap.union_empty_right) $$ Hinterp

/-- Initialize `genHeapGS` from a `genHeapPreS`, hiding the freshly allocated
ghost names. -/
@[rocq_alias gen_heap_init]
theorem genHeap_init [DecidableEq L] [genHeapPreS L V GF H] (σ : H V) :
    ⊢ |==> ∃ G : genHeapGS L V GF H,
      genHeapInterp (G := G) σ ∗
      ([∗map] l ↦ v ∈ σ, pointsTo (G := G) l (.own 1) v) ∗
      ([∗map] l ↦ _v ∈ σ, metaToken (G := G) l ⊤) := by
  imod genHeap_init_names σ with ⟨%γh, %γm, H⟩
  imodintro
  iexists (⟨γh, γm⟩ : genHeapGS L V GF H)
  iexact H

end init

end Iris
