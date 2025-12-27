/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

/-! ## Abstract Finite Map Interface

This file defines an abstract interface for finite maps, inspired by stdpp's `gmap`.
Unlike Rocq's Iris which uses concrete `gmap K A`, we define an abstract typeclass
that allows flexibility to swap implementations (HashMap, RBMap, etc.).

### Main Definitions

* `FiniteMap` - The main typeclass for finite maps with core operations
* `FiniteMapLaws` - Typeclass providing the required laws for finite maps

### Notation

* `m[k]?` or `m.get? k` - Lookup, returns `Option V`
* `m.insert k v` - Insert/update a key-value pair
* `m.erase k` - Remove a key
* `∅` - Empty map
* `{[k := v]}` - Singleton map
* `m₁ ∪ m₂` - Union (left-biased)
* `m.keys` - Domain/keys as a set
* `m₁ ##ₘ m₂` - Disjoint domains
* `m₂ ⊆ m₁` - Submap relation
-/

namespace Iris.Std

/-- Abstract finite map interface.
The type `M` represents a finite map from keys of type `K` to values of type `V`. -/
class FiniteMap (M : Type u) (K : outParam (Type v)) (V : outParam (Type w)) where
  /-- Lookup a key in the map, returning `none` if not present. -/
  get? : M → K → Option V
  /-- Insert or update a key-value pair. -/
  insert : M → K → V → M
  /-- Remove a key from the map. -/
  erase : M → K → M
  /-- The empty map. -/
  empty : M
  /-- Convert the map to a list of key-value pairs. -/
  toList : M → List (K × V)
  /-- Construct a map from a list of key-value pairs. -/
  ofList : List (K × V) → M

export FiniteMap (get? insert erase toList ofList)

namespace FiniteMap

variable {M : Type u} {K : Type v} {V : Type w} [FiniteMap M K V]

/-- Empty map instance for `∅` notation. -/
instance : EmptyCollection M := ⟨empty⟩

/-- Singleton map containing exactly one key-value pair. -/
def singleton (k : K) (v : V) : M := insert ∅ k v

/-- Union of two maps (left-biased: values from `m₁` take precedence). -/
def union (m₁ m₂ : M) : M :=
  (toList m₁).foldl (fun acc (k, v) => insert acc k v) m₂

instance : Union M := ⟨union⟩

/-- The domain of a map as a predicate on keys. -/
def dom (m : M) : K → Prop := fun k => (get? m k).isSome

/-- The domain of a map as a decidable predicate (requires decidable equality on Option V). -/
def domDec (m : M) [DecidableEq V] : K → Bool := fun k => (get? m k).isSome

/-- Two maps have disjoint domains. -/
def Disjoint (m₁ m₂ : M) : Prop := ∀ k, ¬((get? m₁ k).isSome ∧ (get? m₂ k).isSome)

/-- Submap relation: `m₁` is a submap of `m₂` if every key-value pair in `m₁` is also in `m₂`. -/
def Submap (m₁ m₂ : M) : Prop := ∀ k v, get? m₁ k = some v → get? m₂ k = some v

instance : HasSubset M := ⟨Submap⟩

/-- Map a function over all values in the map. -/
def map (f : V → V') [FiniteMap M' K V'] : M → M' :=
  fun m => ofList ((toList m).map (fun (k, v) => (k, f v)))

/-- Filter and map: apply a function that can optionally drop entries. -/
def filterMap (f : V → Option V) : M → M :=
  fun m => ofList ((toList m).filterMap (fun (k, v) => (f v).map (k, ·)))

/-- Filter entries by a predicate on key-value pairs. -/
def filter (φ : K → V → Bool) : M → M :=
  fun m => ofList ((toList m).filter (fun (k, v) => φ k v))

/-- Zip two maps: combine values at matching keys. -/
def zip [FiniteMap M' K V'] [FiniteMap M'' K (V × V')] (m₁ : M) (m₂ : M') : M'' :=
  ofList ((toList m₁).filterMap (fun (k, v) =>
    match get? m₂ k with
    | some v' => some (k, (v, v'))
    | none => none))

/-- Membership: a key is in the map if it has a value. -/
def Mem (m : M) (k : K) : Prop := (get? m k).isSome

/-- Difference: remove all keys in `m₂` from `m₁`.
    `m₁ ∖ m₂` contains entries `(k, v)` where `k ∈ m₁` but `k ∉ m₂`. -/
def difference (m₁ m₂ : M) : M :=
  ofList ((toList m₁).filter (fun (k, _) => (get? m₂ k).isNone))

instance : SDiff M := ⟨difference⟩

end FiniteMap

/-- Membership instance for finite maps: `k ∈ m` means the key `k` is in the map `m`. -/
instance {M : Type u} {K : Type v} {V : Type w} [inst : FiniteMap M K V] : Membership K M :=
  ⟨fun (m : M) (k : K) => (inst.get? m k).isSome⟩

/-- Laws that a finite map implementation must satisfy. -/
class FiniteMapLaws (M : Type u) (K : Type v) (V : Type w)
    [DecidableEq K] [FiniteMap M K V] where
  /-- Looking up in an empty map returns `none`. -/
  get?_empty : ∀ k, get? (∅ : M) k = none
  /-- Looking up the key just inserted returns that value. -/
  get?_insert_eq : ∀ (m : M) k v, get? (insert m k v) k = some v
  /-- Looking up a different key after insert returns the original value. -/
  get?_insert_ne : ∀ (m : M) k k' v, k ≠ k' → get? (insert m k v) k' = get? m k'
  /-- Erasing a key makes lookup return `none`. -/
  get?_erase_eq : ∀ (m : M) k, get? (erase m k) k = none
  /-- Erasing a different key doesn't affect lookup. -/
  get?_erase_ne : ∀ (m : M) k k', k ≠ k' → get? (erase m k) k' = get? m k'
  /-- `toList` and `ofList` are inverses (up to permutation and deduplication). -/
  get?_ofList : ∀ (l : List (K × V)) k,
    get? (ofList l : M) k = l.reverse.lookup k
  /-- Empty map has empty toList. -/
  toList_empty : toList (∅ : M) = []
  /-- toList of insert (when key not present) is cons. -/
  toList_insert : ∀ (m : M) k v, get? m k = none →
    (toList (insert m k v)).Perm ((k, v) :: toList m)
  /-- toList lookup agrees with get?. -/
  toList_get? : ∀ (m : M) k v, get? m k = some v ↔ (k, v) ∈ toList m
  /-- toList has no duplicate keys. -/
  toList_nodup : ∀ (m : M), (toList m).map Prod.fst |>.Nodup
  /-- toList of erase (when key is present) removes the key-value pair.
      For `m !! k = some v`, `toList (erase m k)` is a permutation of `toList m` with `(k, v)` removed. -/
  toList_erase : ∀ (m : M) k v, get? m k = some v →
    (toList m).Perm ((k, v) :: toList (erase m k))
  /-- `toList` and `ofList` roundtrip is a permutation (when keys are unique).
      Corresponds to Rocq's `map_to_list_to_map`. -/
  toList_ofList : ∀ (l : List (K × V)), (l.map Prod.fst).Nodup →
    (toList (ofList l : M)).Perm l

/-- Extended laws for finite maps with value type transformations. -/
class FiniteMapLawsExt (M : Type u) (M' : Type u') (K : Type v) (V : Type w) (V' : Type w')
    [DecidableEq K] [FiniteMap M K V] [FiniteMap M' K V'] [FiniteMapLaws M K V] where
  /-- toList of map (fmap) is related to mapping over toList.
      `toList (map f m)` is a permutation of `(toList m).map (fun (k, v) => (k, f v))` -/
  toList_map : ∀ (m : M) (f : V → V'),
    (toList (FiniteMap.map (M := M) (M' := M') f m)).Perm
      ((toList m).map (fun kv => (kv.1, f kv.2)))

/-- Self-referential extended laws (for filterMap, filter on the same type). -/
class FiniteMapLawsSelf (M : Type u) (K : Type v) (V : Type w)
    [DecidableEq K] [FiniteMap M K V] [FiniteMapLaws M K V] where
  /-- toList of filterMap (omap) is related to filterMap over toList. -/
  toList_filterMap : ∀ (m : M) (f : V → Option V),
    (toList (FiniteMap.filterMap (M := M) f m)).Perm
      ((toList m).filterMap (fun kv => (f kv.2).map (kv.1, ·)))
  /-- toList of filter is related to filter over toList. -/
  toList_filter : ∀ (m : M) (φ : K → V → Bool),
    (toList (FiniteMap.filter (M := M) φ m)).Perm
      ((toList m).filter (fun kv => φ kv.1 kv.2))
  /-- toList of union for disjoint maps. -/
  toList_union_disjoint : ∀ (m₁ m₂ : M),
    FiniteMap.Disjoint m₁ m₂ →
    (toList (m₁ ∪ m₂)).Perm (toList m₁ ++ toList m₂)
  /-- toList of difference is related to filter over toList. -/
  toList_difference : ∀ (m₁ m₂ : M),
    (toList (m₁ \ m₂)).Perm
      ((toList m₁).filter (fun kv => (get? m₂ kv.1).isNone))

export FiniteMapLaws (get?_empty get?_insert_eq get?_insert_ne get?_erase_eq get?_erase_ne get?_ofList toList_empty toList_insert toList_get? toList_nodup toList_erase toList_ofList)
export FiniteMapLawsExt (toList_map)
export FiniteMapLawsSelf (toList_filterMap toList_filter toList_union_disjoint toList_difference)

namespace FiniteMapLaws

variable {M : Type u} {K : Type v} {V : Type w}
variable [DecidableEq K] [FiniteMap M K V] [FiniteMapLaws M K V]

/-- Alternative: lookup is insert then lookup for equal keys. -/
theorem get?_insert (m : M) (k k' : K) (v : V) :
    get? (insert m k v) k' = if k = k' then some v else get? m k' := by
  split
  · next h => rw [h, get?_insert_eq]
  · next h => exact get?_insert_ne m k k' v h

/-- Alternative: lookup after erase. -/
theorem get?_erase (m : M) (k k' : K) :
    get? (erase m k) k' = if k = k' then none else get? m k' := by
  split
  · next h => rw [h, get?_erase_eq]
  · next h => exact get?_erase_ne m k k' h

/-- Insert after erase has the same lookup behavior as direct insert. -/
theorem get?_insert_erase (m : M) (k k' : K) (v : V) :
    get? (insert (erase m k) k v) k' = get? (insert m k v) k' := by
  by_cases h : k = k'
  · simp [h, get?_insert_eq]
  · simp [get?_insert_ne _ _ _ _ h, get?_erase_ne _ _ _ h]

/-- Two maps with the same get? behavior have permutation-equivalent toLists.
    Uses the fact that:
    1. `toList_nodup` ensures no duplicate keys (hence no duplicate pairs)
    2. `toList_get?` + equal lookups implies same membership
    3. Two nodup lists with same membership are permutations

    TODO: Complete proof. Requires either:
    - Import Mathlib.Data.List.Nodup for `List.Nodup.of_map` and `List.perm_of_nodup_nodup_toFinset_eq`
    - Or manual induction proof using `List.Perm.cons` constructors -/
theorem toList_perm_eq_of_get?_eq {m₁ m₂ : M}
    (h : ∀ k, get? m₁ k = get? m₂ k) : (toList m₁).Perm (toList m₂) := by
  -- Key facts available:
  -- hnodup₁: ((toList m₁).map Prod.fst).Nodup (keys are unique)
  -- hnodup₂: ((toList m₂).map Prod.fst).Nodup
  -- hmem: ∀ kv, kv ∈ toList m₁ ↔ kv ∈ toList m₂ (same pairs)
  have _hnodup₁ := toList_nodup (M := M) (K := K) (V := V) m₁
  have _hnodup₂ := toList_nodup (M := M) (K := K) (V := V) m₂
  have _hmem : ∀ kv, kv ∈ toList m₁ ↔ kv ∈ toList m₂ := by
    intro kv
    simp only [← toList_get? (M := M) (K := K) (V := V), h]
  -- From nodup on keys, we get nodup on pairs.
  -- From nodup on pairs and same membership, we get permutation.
  sorry

/-- toList of insert and insert-after-erase are permutations of each other. -/
theorem toList_insert_erase_perm (m : M) (k : K) (v : V) :
    (toList (insert m k v)).Perm (toList (insert (erase m k) k v)) :=
  toList_perm_eq_of_get?_eq (fun k' => (get?_insert_erase m k k' v).symm)

/-- Singleton lookup for equal keys. -/
theorem get?_singleton_eq (k : K) (v : V) :
    get? (FiniteMap.singleton k v : M) k = some v := by
  simp [FiniteMap.singleton, get?_insert_eq]

/-- Singleton lookup for different keys. -/
theorem get?_singleton_ne (k k' : K) (v : V) (h : k ≠ k') :
    get? (FiniteMap.singleton k v : M) k' = none := by
  simp [FiniteMap.singleton, get?_insert_ne _ _ _ _ h, get?_empty]

/-- Singleton lookup general case. -/
theorem get?_singleton (k k' : K) (v : V) :
    get? (FiniteMap.singleton k v : M) k' = if k = k' then some v else none := by
  split
  · next h => rw [h, get?_singleton_eq]
  · next h => exact get?_singleton_ne k k' v h

/-- Insert is idempotent for the same key-value. -/
theorem insert_insert_eq (m : M) (k : K) (v v' : V) :
    get? (insert (insert m k v) k v') = get? (insert m k v' : M) := by
  funext k'
  by_cases h : k = k'
  · simp [h, get?_insert_eq]
  · simp [get?_insert_ne _ _ _ _ h]

/-- Erasing from empty is empty. -/
theorem erase_empty (k : K) :
    get? (erase (∅ : M) k) = get? (∅ : M) := by
  funext k'
  by_cases h : k = k'
  · simp [h, get?_erase_eq, get?_empty]
  · simp [get?_erase_ne _ _ _ h, get?_empty]

/-- The domain of an empty map is empty. -/
theorem dom_empty : FiniteMap.dom (∅ : M) = fun _ => False := by
  funext k
  simp [FiniteMap.dom, get?_empty]

/-- The domain after insert includes the inserted key. -/
theorem dom_insert (m : M) (k : K) (v : V) :
    FiniteMap.dom (insert m k v) k := by
  simp [FiniteMap.dom, get?_insert_eq]

/-- Empty is a submap of everything. -/
theorem empty_submap (m : M) : (∅ : M) ⊆ m := by
  intro k v h
  simp [get?_empty] at h

/-- Empty is disjoint from everything. -/
theorem disjoint_empty_left (m : M) : FiniteMap.Disjoint (∅ : M) m := by
  intro k ⟨h₁, _⟩
  simp [get?_empty] at h₁

end FiniteMapLaws

namespace FiniteMap

variable {M : Type u} {K : Type v} {V : Type w} [FiniteMap M K V]

/-- Submap is reflexive. -/
theorem submap_refl (m : M) : m ⊆ m := fun _ _ h => h

/-- Submap is transitive. -/
theorem submap_trans {m₁ m₂ m₃ : M} (h₁ : m₁ ⊆ m₂) (h₂ : m₂ ⊆ m₃) : m₁ ⊆ m₃ :=
  fun k v hm₁ => h₂ k v (h₁ k v hm₁)

/-- Disjointness is symmetric. -/
theorem disjoint_symm {m₁ m₂ : M} (h : Disjoint m₁ m₂) : Disjoint m₂ m₁ :=
  fun k ⟨h₂, h₁⟩ => h k ⟨h₁, h₂⟩

theorem disjoint_empty_right [DecidableEq K] [FiniteMapLaws M K V] (m : M) : Disjoint m (∅ : M) :=
  disjoint_symm (FiniteMapLaws.disjoint_empty_left m)

/-- `m₂` and `m₁ \ m₂` are disjoint.
    This is unconditional - the difference by definition removes all keys in m₂. -/
theorem disjoint_difference_r [DecidableEq K] [FiniteMapLaws M K V] [FiniteMapLawsSelf M K V]
    (m₁ m₂ : M) : Disjoint m₂ (m₁ \ m₂) := by
  intro k ⟨h_in_m2, h_in_diff⟩
  -- h_in_m2: (get? m₂ k).isSome
  -- h_in_diff: (get? (m₁ \ m₂) k).isSome
  -- But (m₁ \ m₂) only has keys not in m₂, so this is a contradiction
  -- We need to show that if k ∈ m₁ \ m₂, then k ∉ m₂
  -- The difference filters to entries where (get? m₂ k).isNone
  have hdiff := toList_difference (M := M) (K := K) (V := V) m₁ m₂
  -- From h_in_diff, get some value v at k in the diff
  obtain ⟨v, hget_diff⟩ := Option.isSome_iff_exists.mp h_in_diff
  -- (k, v) ∈ toList (m₁ \ m₂)
  have hmem_diff : (k, v) ∈ toList (m₁ \ m₂) := (toList_get? (m₁ \ m₂) k v).mp hget_diff
  -- By permutation, (k, v) ∈ filtered list
  have hmem_filter : (k, v) ∈ (toList m₁).filter (fun kv => (get? m₂ kv.1).isNone) :=
    hdiff.mem_iff.mp hmem_diff
  -- From filter membership, (get? m₂ k).isNone = true
  have hfilter : (get? m₂ k).isNone = true := (List.mem_filter.mp hmem_filter).2
  -- But h_in_m2 says (get? m₂ k).isSome - this is a contradiction
  simp only [Option.isNone_iff_eq_none] at hfilter
  simp only [hfilter, Option.isSome_none, Bool.false_eq_true] at h_in_m2

/-- toList of difference union: `toList (m₂ ∪ (m₁ \ m₂))` is a permutation of `toList m₁`
    when `m₂ ⊆ m₁`. This is the key lemma for `big_sepM_subseteq`. -/
theorem toList_difference_union [DecidableEq K] [FiniteMapLaws M K V] [FiniteMapLawsSelf M K V]
    (m₁ m₂ : M) (hsub : m₂ ⊆ m₁) :
    (toList (m₂ ∪ (m₁ \ m₂))).Perm (toList m₁) := by
  -- m₂ and m₁ \ m₂ are disjoint
  have hdisj : Disjoint m₂ (m₁ \ m₂) := disjoint_difference_r m₁ m₂
  -- toList (m₂ ∪ (m₁ \ m₂)) ~ toList m₂ ++ toList (m₁ \ m₂)
  have hunion := toList_union_disjoint m₂ (m₁ \ m₂) hdisj
  -- toList (m₁ \ m₂) ~ filter (toList m₁)
  have hdiff := toList_difference (M := M) (K := K) (V := V) m₁ m₂
  -- Need to show: toList m₂ ++ filter (toList m₁) ~ toList m₁
  -- Since m₂ ⊆ m₁, every entry in m₂ is also in m₁
  -- And filter removes exactly the entries in m₂
  -- So together they form all of m₁
  refine hunion.trans ?_
  -- Need: toList m₂ ++ toList (m₁ \ m₂) ~ toList m₁
  refine List.Perm.trans (List.Perm.append_left (toList m₂) hdiff) ?_
  -- Need: toList m₂ ++ filter (toList m₁) ~ toList m₁
  -- This is essentially saying that partitioning m₁ by "in m₂" gives m₂'s entries and the rest
  sorry

end FiniteMap

-- ============================================================================
-- Notations
-- ============================================================================

section Notation

/-- Notation for map disjointness: `m₁ ##ₘ m₂` -/
scoped infix:50 " ##ₘ " => FiniteMap.Disjoint

/-- Notation for singleton map: `{[k := v]}` -/
scoped syntax "{[" term " := " term "]}" : term

scoped macro_rules
  | `({[$k := $v]}) => `(FiniteMap.singleton $k $v)

end Notation

end Iris.Std
