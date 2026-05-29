module
public import Iris.Algebra
public import Iris.BI.Lib.Fractional
public import Iris.Instances.Lib.GhostMap
public import Iris.Instances.IProp


public section

namespace Iris

/-! (TODO: Adapt to Iris Lean implementation)

This file provides a generic mechanism for a language-level point-to
connective `l ↦{dq} v` reflecting the physical heap.  This library is designed to
be used as a singleton (i.e., with only a single instance existing in any
proof), with the `gen_heapGS` typeclass providing the ghost names of that unique
instance.  That way, `pointsto` does not need an explicit `gname` parameter.
This mechanism can be plugged into a language and related to the physical heap
by using `gen_heap_interp σ` in the state interpretation of the weakest
precondition. See heap-lang for an example.

If you are looking for a library providing "ghost heaps" independent of the
physical state, you will likely want explicit ghost names to disambiguate
multiple heaps and are thus better off using `ghost_map`, or (if you need more
flexibility), directly using the underlying `algebra.lib.gmap_view`.

This library is generic in the types `L` for locations and `V` for values and
supports fractional permissions.  Next to the point-to connective `l ↦{dq} v`,
which keeps track of the value `v` of a location `l`, this library also provides
a way to attach "meta" or "ghost" data to locations. This is done as follows:

- When one allocates a location, in addition to the point-to connective `l ↦ v`,
  one also obtains the token `meta_token l ⊤`. This token is an exclusive
  resource that denotes that no meta data has been associated with the
  namespaces in the mask `⊤` for the location `l`.

- Meta data tokens can be split w.r.t. namespace masks, i.e.
  `meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2` if `E1 ## E2`.

- Meta data can be set using the update `meta_token l E ==∗ meta l N x` provided
  `↑N ⊆ E`, and `x : A` for any countable `A`. The `meta l N x` connective is
  persistent and denotes the knowledge that the meta data `x` has been
  associated with namespace `N` to the location `l`.

To make the mechanism as flexible as possible, the `x : A` in `meta l N x` can
be of any countable type `A`. This means that you can associate e.g. single
ghost names, but also tuples of ghost names, etc.

To further increase flexibility, the `meta l N x` and `meta_token l E`
connectives are annotated with a namespace `N` and mask `E`. That way, one can
assign a map of meta information to a location. This is particularly useful when
building abstractions, then one can gradually assign more ghost information to a
location instead of having to do all of this at once. We use namespaces so that
these can be matched up with the invariant namespaces.

To implement this mechanism, we use three pieces of ghost state:

- A `ghost_map L V`, which keeps track of the values of locations.
- A `ghost_map L gname`, which keeps track of the meta information of
  locations. More specifically, this RA introduces an indirection: it keeps
  track of a ghost name for each location.
- The ghost names in the aforementioned authoritative RA refer to namespace maps
  `reservation_map (agree positive)`, which store the actual meta information.
  This indirection is needed because we cannot perform frame preserving updates
  in an authoritative fragment without owning the full authoritative element
  (in other words, without the indirection `meta_set` would need `gen_heap_interp`
  as a premise).
-/

/-
  NOTE:

  This file is based on an old version of `gen_heap.v`, which does not depend on a
  `reservation_map`. In particular, the API offered here is much more restricted,
  and mostly mirrors that of `GhostMap`. In the future, we'd need to port the
  `reservation_map`s and port the rest of the lemmas.

-/

variable (F: outParam (Type _)) [UFraction F]

class gen_HeapGPreS (L V : Type _) (GF : BundledGFunctors) (H : outParam <| Type _ → Type _)[Std.LawfulFiniteMap H L] where
  heap : GhostMapG GF F L V H
  -- TODO: `meta` field blocked by `reservation_mapR`
  -- TODO: `metaData` field blocked by `reservation_mapR`

instance gen_HeapGPreS.instGhostMapG [Std.LawfulFiniteMap H L][ι : gen_HeapGPreS F L V GF H] : GhostMapG GF F L V H := ι.heap

class gen_HeapGS (L V : Type _) (GF : BundledGFunctors) (H : outParam <| Type _ → Type _)[Std.LawfulFiniteMap H L]
    extends gen_HeapGPreS F L V GF H where
  heapName : GName
  -- TODO: Metadata not supported yet
  -- metaName : GName

#rocq_concept base_logic "gen_heapΣ" missing "We don't yet have definitions of BundledGFunctors"
#rocq_concept base_logic "subG_gen_heapGpreS" missing "We don't yet have SubG"

section definitions

variable {GF : BundledGFunctors} {L V : Type _}
variable {H : outParam <| Type _ → Type _} [Std.LawfulFiniteMap H L]
variable {F: outParam (Type _)} [UFraction F]
variable [ι : gen_HeapGS F L V GF H]

open Std.FiniteMap

def gen_heap_interp (σ : H V) : IProp GF := iprop(ι.heapName ↪●MAP σ)
-- def gen_heap_interp (σ : GMap V) : IProp GF := iprop%
--   ∃ m : GMap GName,
--   ⌜ ∀ x : L, dom m x → dom σ x ⌝ ∗
--   (ι.heapName ↪●MAP σ) ∗
--   (ι.metaName ↪●MAP m)

def pointsTo (l : L) (dq : DFrac F)(v : V) : IProp GF := iprop((ι.heapName) ↪◯MAP[l]{dq} v)

notation l " ↦{" dq "} " v => pointsTo l dq v
notation l " ↦ " v => pointsTo l (DFrac.own 1) v

end definitions

section lemmas

variable {F: outParam (Type _)} [UFraction F]
variable {L V : Type _} {GF : BundledGFunctors}
variable {H : outParam <| Type _ → Type _} [Std.LawfulFiniteMap H L]
variable [ι : gen_HeapGS F L V GF H]

variable (l : L) (dq dq₁ dq₂ : DFrac F) (v v₁ v₂ : V) (σ : H V)

instance : BI.Timeless (PROP := IProp GF) (l ↦{dq} v) :=
  inferInstanceAs (BI.Timeless (ι.heapName ↪◯MAP[l]{dq} v))

instance : Fractional (PROP := IProp GF) (l ↦{.own ·} v) :=
  inferInstanceAs (Fractional (ι.heapName ↪◯MAP[l]{.own ·} v))

instance : AsFractional (PROP := IProp GF) (l ↦{.own q} v) (l ↦{.own ·} v) q :=
  inferInstanceAs
    (AsFractional (PROP := IProp GF) (ι.heapName ↪◯MAP[l]{.own q} v) (ι.heapName ↪◯MAP[l]{.own ·} v) q)

theorem pointsTo_cmraValid : (l ↦{dq} v)  ⊢@{IProp GF} internalCmraValid dq := by
  simp only [pointsTo, ghost_map_elem_valid]

theorem pointsTo_op_cmraValid : (l ↦{dq₁} v₁) ∗ (l ↦{dq₂} v₂) ⊢@{IProp GF} internalCmraValid (dq₁ • dq₂) ∧ ⌜ v₁ = v₂ ⌝ := by
  simp only [pointsTo]
  iapply ghost_map_elem_valid_2

theorem pointsTo_agree : (l ↦{dq₁} v₁) ∗ (l ↦{dq₂} v₂) ⊢@{IProp GF} ⌜ v₁ = v₂ ⌝ := by
  simp only [pointsTo]
  iapply ghost_map_elem_agree

open Std.PartialMap

section updateLemmas

theorem gen_heap_alloc (Hσl : get? σ l = .none) :
    (gen_heap_interp (GF := GF) σ) ⊢ |==> (gen_heap_interp (insert σ l v) ∗ (l ↦ v)) := by
  simp only [gen_heap_interp, pointsTo]
  iapply ghost_map_insert (γ := ι.heapName) _ v Hσl

theorem gen_heap_dealloc : (gen_heap_interp (GF := GF) σ ∗ l ↦ v) ==∗ gen_heap_interp (delete σ l) := by
  simp only [gen_heap_interp, pointsTo]
  iintro ⟨H₁,H₂⟩
  iapply ghost_map_delete (γ := ι.heapName) _ v $$ H₁ H₂

theorem gen_heap_valid : (gen_heap_interp (GF := GF) σ ∗ l ↦ v) ==∗ ⌜ get? σ l = .some v ⌝ := by
  simp only [gen_heap_interp, pointsTo]
  iintro ⟨H₁,H₂⟩
  iapply ghost_map_lookup $$ H₁ H₂

theorem gen_heap_update : (gen_heap_interp (GF := GF) σ ∗ l ↦ v₁) ==∗ (gen_heap_interp (GF := GF) (insert σ l v₂) ∗ l ↦ v₂) := by
  simp only [gen_heap_interp, pointsTo]
  iintro ⟨H₁,H₂⟩
  iapply ghost_map_update (γ := ι.heapName) _ _ v₂ $$ H₁ H₂

end updateLemmas

end lemmas
