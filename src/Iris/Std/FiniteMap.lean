/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

/-! ## Abstract Finite Map Interface

This file defines an abstract interface for finite maps, inspired by stdpp's `fin_maps`.

### Notation

* `m !! k` or `get? m k` - Lookup, returns `Option V`
* `insert m k v` - Insert/update a key-value pair
* `delete m k` - Remove a key (called `erase` internally)
* `∅` - Empty map
* `{[k := v]}` - Singleton map
* `m₁ ∪ m₂` - Union (left-biased)
* `m₁ ##ₘ m₂` - Disjoint domains
* `m₁ ⊆ m₂` - Submap relation
-/

namespace Iris.Std

/-- Abstract finite map interface.
The type `M` represents a finite map from keys of type `K` to values of type `V`.

This corresponds to Rocq's `FinMap` class from stdpp. -/
class FiniteMap (M : Type u) (K : outParam (Type v)) (V : outParam (Type w)) where
  /-- Lookup a key in the map, returning `none` if not present.
      Corresponds to Rocq's `lookup` (notation `!!`). -/
  get? : M → K → Option V
  /-- Insert or update a key-value pair.
      Corresponds to Rocq's `insert` (notation `<[i:=x]>`). -/
  insert : M → K → V → M
  /-- Remove a key from the map.
      Corresponds to Rocq's `delete`. -/
  delete : M → K → M
  /-- The empty map. -/
  empty : M
  /-- Convert the map to a list of key-value pairs.
      Corresponds to Rocq's `map_to_list`. -/
  toList : M → List (K × V)
  /-- Construct a map from a list of key-value pairs.
      Corresponds to Rocq's `list_to_map`. -/
  ofList : List (K × V) → M

export FiniteMap (get? insert delete toList ofList)

namespace FiniteMap

variable {M : Type u} {K : Type v} {V : Type w} [FiniteMap M K V]

/-- Empty map instance for `∅` notation. -/
instance : EmptyCollection M := ⟨empty⟩

/-- Singleton map containing exactly one key-value pair.
    Corresponds to Rocq's `{[ i := x ]}` notation. -/
def singleton (k : K) (v : V) : M := insert ∅ k v

/-- Union of two maps (left-biased: values from `m₁` take precedence).
    Corresponds to Rocq's `m₁ ∪ m₂`. -/
def union (m₁ m₂ : M) : M :=
  (toList m₁).foldl (fun acc (k, v) => insert acc k v) m₂

instance : Union M := ⟨union⟩

/-- The domain of a map as a predicate on keys. -/
def dom (m : M) : K → Prop := fun k => (get? m k).isSome

/-- The domain of a map as a decidable predicate (requires decidable equality on Option V). -/
def domDec (m : M) [DecidableEq V] : K → Bool := fun k => (get? m k).isSome

/-- Two maps have disjoint domains.
    Corresponds to Rocq's `map_disjoint` (notation `##ₘ`). -/
def Disjoint (m₁ m₂ : M) : Prop := ∀ k, ¬((get? m₁ k).isSome ∧ (get? m₂ k).isSome)

/-- Submap relation: `m₁` is a submap of `m₂` if every key-value pair in `m₁` is also in `m₂`.
    Corresponds to Rocq's `map_subseteq` (notation `⊆`).

    Rocq's `map_subseteq_spec` states:
    `m1 ⊆ m2 ↔ ∀ i x, m1 !! i = Some x → m2 !! i = Some x` -/
def Submap (m₁ m₂ : M) : Prop := ∀ k v, get? m₁ k = some v → get? m₂ k = some v

instance : HasSubset M := ⟨Submap⟩

/-- Map a function over all values in the map.
    Corresponds to Rocq's `fmap` (notation `f <$> m`). -/
def map (f : V → V') [FiniteMap M' K V'] : M → M' :=
  fun m => ofList ((toList m).map (fun (k, v) => (k, f v)))

/-- Filter and map: apply a function that can optionally drop entries.
    Corresponds to Rocq's `omap`. -/
def filterMap (f : V → Option V) : M → M :=
  fun m => ofList ((toList m).filterMap (fun (k, v) => (f v).map (k, ·)))

/-- Alias for `filterMap` to match Rocq's naming. -/
abbrev omap := @filterMap

/-- Filter entries by a predicate on key-value pairs.
    Corresponds to Rocq's `filter`. -/
def filter (φ : K → V → Bool) : M → M :=
  fun m => ofList ((toList m).filter (fun (k, v) => φ k v))

/-- Zip two maps: combine values at matching keys.
    Corresponds to Rocq's `map_zip_with`. -/
def zip [FiniteMap M' K V'] [FiniteMap M'' K (V × V')] (m₁ : M) (m₂ : M') : M'' :=
  ofList ((toList m₁).filterMap (fun (k, v) =>
    match get? m₂ k with
    | some v' => some (k, (v, v'))
    | none => none))

/-- Membership: a key is in the map if it has a value. -/
def Mem (m : M) (k : K) : Prop := (get? m k).isSome

/-- Difference: remove all keys in `m₂` from `m₁`.
    `m₁ ∖ m₂` contains entries `(k, v)` where `k ∈ m₁` but `k ∉ m₂`.
    Corresponds to Rocq's `map_difference` (notation `∖`). -/
def difference (m₁ m₂ : M) : M :=
  ofList ((toList m₁).filter (fun (k, _) => (get? m₂ k).isNone))

instance : SDiff M := ⟨difference⟩

/-- Transform keys of a map using an injective function.
    Given `f : K → K'`, `kmap f m` transforms a map with keys of type `K`
    into a map with keys of type `K'`.
    Corresponds to Rocq's `kmap`. -/
def kmap {M' : Type u'} {K' : Type v'} [FiniteMap M' K' V] (f : K → K') (m : M) : M' :=
  ofList ((toList m).map (fun (k, v) => (f k, v)))

/-- Convert a list to a map with sequential natural number keys starting from `start`.
    `map_seq start [v₀, v₁, v₂, ...]` creates a map `{start ↦ v₀, start+1 ↦ v₁, start+2 ↦ v₂, ...}`.
    Corresponds to Rocq's `map_seq`. -/
def map_seq [FiniteMap M Nat V] (start : Nat) (l : List V) : M :=
  ofList (l.mapIdx (fun i v => (start + i, v)))

end FiniteMap

/-- Membership instance for finite maps: `k ∈ m` means the key `k` is in the map `m`. -/
instance {M : Type u} {K : Type v} {V : Type w} [inst : FiniteMap M K V] : Membership K M :=
  ⟨fun (m : M) (k : K) => (inst.get? m k).isSome⟩

/-- Laws that a finite map implementation must satisfy.
    Corresponds to Rocq's `FinMap` class axioms. -/
class FiniteMapLaws (M : Type u) (K : Type v) (V : Type w)
    [DecidableEq K] [FiniteMap M K V] where
  /-- Map extensionality: two maps with the same lookups are equal.
      Corresponds to Rocq's `map_eq`. -/
  map_eq : ∀ (m₁ m₂ : M), (∀ i, get? m₁ i = get? m₂ i) → m₁ = m₂
  /-- Looking up in an empty map returns `none`.
      Corresponds to Rocq's `lookup_empty`. -/
  lookup_empty : ∀ k, get? (∅ : M) k = none
  /-- Looking up the key just inserted returns that value.
      Corresponds to Rocq's `lookup_insert_eq`. -/
  lookup_insert_eq : ∀ (m : M) k v, get? (insert m k v) k = some v
  /-- Looking up a different key after insert returns the original value.
      Corresponds to Rocq's `lookup_insert_ne`. -/
  lookup_insert_ne : ∀ (m : M) k k' v, k ≠ k' → get? (insert m k v) k' = get? m k'
  /-- Deleting a key makes lookup return `none`.
      Corresponds to Rocq's `lookup_delete_eq`. -/
  lookup_delete_eq : ∀ (m : M) k, get? (delete m k) k = none
  /-- Deleting a different key doesn't affect lookup.
      Corresponds to Rocq's `lookup_delete_ne`. -/
  lookup_delete_ne : ∀ (m : M) k k', k ≠ k' → get? (delete m k) k' = get? m k'
  /-- `toList` and `ofList` are inverses (up to permutation and deduplication).
      Corresponds to Rocq's `elem_of_list_to_map`. -/
  elem_of_list_to_map : ∀ (l : List (K × V)) k,
    get? (ofList l : M) k = l.reverse.lookup k
  /-- Empty map has empty toList.
      Corresponds to Rocq's `map_to_list_empty`. -/
  map_to_list_empty : toList (∅ : M) = []
  /-- toList of insert (when key not present) is cons.
      Corresponds to Rocq's `map_to_list_insert`. -/
  map_to_list_insert : ∀ (m : M) k v, get? m k = none →
    (toList (insert m k v)).Perm ((k, v) :: toList m)
  /-- toList lookup agrees with get?.
      Corresponds to Rocq's `elem_of_map_to_list`. -/
  elem_of_map_to_list : ∀ (m : M) k v, get? m k = some v ↔ (k, v) ∈ toList m
  /-- toList has no duplicate keys.
      Corresponds to Rocq's `NoDup_map_to_list`. -/
  NoDup_map_to_list : ∀ (m : M), (toList m).map Prod.fst |>.Nodup
  /-- toList of delete (when key is present) removes the key-value pair.
      For `m !! k = some v`, `toList (delete m k)` is a permutation of `toList m` with `(k, v)` removed.
      Corresponds to Rocq's `map_to_list_delete`. -/
  map_to_list_delete : ∀ (m : M) k v, get? m k = some v →
    (toList m).Perm ((k, v) :: toList (delete m k))
  /-- `toList` and `ofList` roundtrip is a permutation (when keys are unique).
      Corresponds to Rocq's `map_to_list_to_map`. -/
  map_to_list_to_map : ∀ (l : List (K × V)), (l.map Prod.fst).Nodup →
    (toList (ofList l : M)).Perm l
  /-- Lookup returns `none` iff the key is not in the domain.
      Corresponds to Rocq's `not_elem_of_dom`. -/
  lookup_None_dom : ∀ (m : M) k, get? m k = none ↔ ¬FiniteMap.dom m k
  /-- Lookup returns `some` iff the key is in the domain.
      Corresponds to Rocq's `elem_of_dom`. -/
  lookup_Some_dom : ∀ (m : M) k, (∃ v, get? m k = some v) ↔ FiniteMap.dom m k

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
  /-- Lookup in union: left-biased, m₁ takes precedence.
      Corresponds to Rocq's `lookup_union`. -/
  lookup_union : ∀ (m₁ m₂ : M) k,
    get? (m₁ ∪ m₂) k = (get? m₁ k).orElse (fun _ => get? m₂ k)
  /-- Lookup in difference: key must be in m₁ but not in m₂.
      Corresponds to Rocq's `lookup_difference`. -/
  lookup_difference : ∀ (m₁ m₂ : M) k,
    get? (m₁ \ m₂) k = if (get? m₂ k).isSome then none else get? m₁ k

/-- Laws for kmap operation (key transformation). -/
class FiniteMapKmapLaws (M : Type u) (M' : Type u') (K : Type v) (K' : Type v') (V : Type w)
    [DecidableEq K] [DecidableEq K'] [FiniteMap M K V] [FiniteMap M' K' V]
    [FiniteMapLaws M K V] [FiniteMapLaws M' K' V] where
  /-- toList of kmap is related to mapping over toList.
      For an injective function `f : K → K'`, `toList (kmap f m)` is a permutation of
      `(toList m).map (fun (k, v) => (f k, v))`.
      Corresponds to Rocq's `map_to_list_kmap`. -/
  toList_kmap : ∀ (f : K → K') (m : M),
    (∀ {x y}, f x = f y → x = y) →  -- f is injective
    (toList (FiniteMap.kmap (M' := M') f m)).Perm
      ((toList m).map (fun (k, v) => (f k, v)))

/-- Laws for map_seq operation (list to indexed map). -/
class FiniteMapSeqLaws (M : Type u) (V : Type w)
    [FiniteMap M Nat V] [FiniteMapLaws M Nat V] where
  /-- toList of map_seq is related to zip with sequence.
      `toList (map_seq start l)` is a permutation of `zip (seq start (length l)) l`.
      Corresponds to Rocq's `map_to_list_seq`. -/
  toList_map_seq : ∀ (start : Nat) (l : List V),
    (toList (FiniteMap.map_seq start l : M)).Perm
      ((List.range' start l.length).zip l)

/-! ### Map-Set Conversion Laws

Note: Due to Lean 4's type class resolution limitations with dependent parameters,
the FiniteMapSetLaws class has been moved to a separate file or defined inline where needed.

Key operations that connect FiniteMap and FiniteSet:
- `domSet m : S` - converts map domain to a finite set
  Implementation: `FiniteSet.ofList ((toList m).map Prod.fst)`
- `ofSet c X : M` - creates map from set with all keys mapping to constant c
  Implementation: `ofList ((FiniteSet.toList X).map (fun k => (k, c)))`

These are defined directly in files that need them (e.g., BigSepMap.lean).
-/

export FiniteMapLaws (map_eq lookup_empty lookup_insert_eq lookup_insert_ne lookup_delete_eq lookup_delete_ne elem_of_list_to_map map_to_list_empty map_to_list_insert elem_of_map_to_list NoDup_map_to_list map_to_list_delete map_to_list_to_map)

export FiniteMapLawsExt (toList_map)
export FiniteMapLawsSelf (toList_filterMap toList_filter toList_union_disjoint toList_difference lookup_union lookup_difference)
export FiniteMapKmapLaws (toList_kmap)
export FiniteMapSeqLaws (toList_map_seq)

namespace FiniteMapLaws

variable {M : Type u} {K : Type v} {V : Type w}
variable [DecidableEq K] [FiniteMap M K V] [FiniteMapLaws M K V]

/-- Alternative: lookup is insert then lookup for equal keys.
    Corresponds to Rocq's `lookup_insert`. -/
theorem lookup_insert (m : M) (k k' : K) (v : V) :
    get? (insert m k v) k' = if k = k' then some v else get? m k' := by
  split
  · next h => rw [h, lookup_insert_eq]
  · next h => exact lookup_insert_ne m k k' v h

/-- Alternative: lookup after delete.
    Corresponds to Rocq's `lookup_delete`. -/
theorem lookup_delete (m : M) (k k' : K) :
    get? (delete m k) k' = if k = k' then none else get? m k' := by
  split
  · next h => rw [h, lookup_delete_eq]
  · next h => exact lookup_delete_ne m k k' h

/-- Insert after delete has the same lookup behavior as direct insert.
    Corresponds to Rocq's `insert_delete_eq`. -/
theorem lookup_insert_delete (m : M) (k k' : K) (v : V) :
    get? (insert (delete m k) k v) k' = get? (insert m k v) k' := by
  by_cases h : k = k'
  · simp [h, lookup_insert_eq]
  · simp [lookup_insert_ne _ _ _ _ h, lookup_delete_ne _ _ _ h]

/-- If a list of pairs has no duplicate keys, then it has no duplicate pairs.
    This is because pairs with different keys are different, and there's at most one
    pair per key. -/
private theorem nodup_of_nodup_map_fst {α β : Type _} (l : List (α × β))
    (h : (l.map Prod.fst).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons]
    constructor
    · intro hx
      rw [List.map_cons, List.nodup_cons] at h
      have : x.1 ∈ xs.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hx
      exact h.1 this
    · rw [List.map_cons, List.nodup_cons] at h
      exact ih h.2

/-- For a Nodup list, erasing an element removes it completely. -/
private theorem not_mem_erase_self_of_nodup {α : Type _} [DecidableEq α] (x : α) (l : List α)
    (hnd : l.Nodup) : x ∉ l.erase x := by
  induction l with
  | nil => exact List.not_mem_nil
  | cons y ys ih =>
    simp only [List.erase_cons]
    rw [List.nodup_cons] at hnd
    split
    · next h =>
      have heq : y = x := eq_of_beq h
      rw [← heq]
      exact hnd.1
    · next h =>
      simp only [List.mem_cons]
      intro hor
      cases hor with
      | inl heq =>
        have : (y == x) = true := beq_iff_eq.mpr heq.symm
        exact absurd this h
      | inr hmem => exact ih hnd.2 hmem

/-- Two Nodup lists with the same membership are permutations of each other.
    This is the key lemma corresponding to Rocq's `NoDup_Permutation`. -/
private theorem perm_of_nodup_of_mem_iff {α : Type _} [DecidableEq α]
    {l₁ l₂ : List α} (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.refl []
    | cons y ys =>
      have : y ∈ ([] : List α) := (hmem y).mpr List.mem_cons_self
      exact absurd this List.not_mem_nil
  | cons x xs ih =>
    have hx_in_l₂ : x ∈ l₂ := (hmem x).mp List.mem_cons_self
    have hperm₂ : l₂.Perm (x :: l₂.erase x) := List.perm_cons_erase hx_in_l₂
    rw [List.nodup_cons] at hnd₁
    have hx_notin_xs : x ∉ xs := hnd₁.1
    have hnd_xs : xs.Nodup := hnd₁.2
    have hnd_erase : (l₂.erase x).Nodup := hnd₂.erase x
    have hmem_erase : ∀ y, y ∈ xs ↔ y ∈ l₂.erase x := by
      intro y
      constructor
      · intro hy
        have hne : y ≠ x := fun heq => hx_notin_xs (heq ▸ hy)
        have hy_l₂ : y ∈ l₂ := (hmem y).mp (List.mem_cons_of_mem x hy)
        exact (List.mem_erase_of_ne hne).mpr hy_l₂
      · intro hy
        have hne : y ≠ x := by
          intro heq
          rw [heq] at hy
          exact not_mem_erase_self_of_nodup x l₂ hnd₂ hy
        have hy_l₂ : y ∈ l₂ := List.mem_of_mem_erase hy
        have hy_l₁ : y ∈ x :: xs := (hmem y).mpr hy_l₂
        cases List.mem_cons.mp hy_l₁ with
        | inl heq => exact absurd heq hne
        | inr h => exact h
    have hperm_xs : xs.Perm (l₂.erase x) := ih hnd_xs hnd_erase hmem_erase
    exact (List.Perm.cons x hperm_xs).trans hperm₂.symm

/-- Two maps with the same get? behavior have permutation-equivalent toLists.
    Uses the fact that:
    1. `NoDup_map_to_list` ensures no duplicate keys (hence no duplicate pairs)
    2. `elem_of_map_to_list` + equal lookups implies same membership
    3. Two nodup lists with same membership are permutations -/
theorem toList_perm_eq_of_get?_eq [DecidableEq V] {m₁ m₂ : M}
    (h : ∀ k, get? m₁ k = get? m₂ k) : (toList m₁).Perm (toList m₂) := by
  have hnodup₁ := nodup_of_nodup_map_fst _ (NoDup_map_to_list (M := M) (K := K) (V := V) m₁)
  have hnodup₂ := nodup_of_nodup_map_fst _ (NoDup_map_to_list (M := M) (K := K) (V := V) m₂)
  have hmem : ∀ kv, kv ∈ toList m₁ ↔ kv ∈ toList m₂ := by
    intro kv
    simp only [← elem_of_map_to_list (M := M) (K := K) (V := V), h]
  exact perm_of_nodup_of_mem_iff hnodup₁ hnodup₂ hmem

/-- toList of insert and insert-after-delete are permutations of each other. -/
theorem toList_insert_delete_perm [DecidableEq V] (m : M) (k : K) (v : V) :
    (toList (insert m k v)).Perm (toList (insert (delete m k) k v)) :=
  toList_perm_eq_of_get?_eq (fun k' => (lookup_insert_delete m k k' v).symm)

/-- Singleton lookup for equal keys.
    Corresponds to Rocq's `lookup_singleton_eq`. -/
theorem lookup_singleton_eq (k : K) (v : V) :
    get? (FiniteMap.singleton k v : M) k = some v := by
  simp [FiniteMap.singleton, lookup_insert_eq]

/-- Singleton lookup for different keys.
    Corresponds to Rocq's `lookup_singleton_ne`. -/
theorem lookup_singleton_ne (k k' : K) (v : V) (h : k ≠ k') :
    get? (FiniteMap.singleton k v : M) k' = none := by
  simp [FiniteMap.singleton, lookup_insert_ne _ _ _ _ h, lookup_empty]

/-- Singleton lookup general case.
    Corresponds to Rocq's `lookup_singleton`. -/
theorem lookup_singleton (k k' : K) (v : V) :
    get? (FiniteMap.singleton k v : M) k' = if k = k' then some v else none := by
  split
  · next h => rw [h, lookup_singleton_eq]
  · next h => exact lookup_singleton_ne k k' v h

/-- Insert is idempotent for the same key-value.
    Corresponds to Rocq's `insert_insert_eq`. -/
theorem insert_insert_eq (m : M) (k : K) (v v' : V) :
    get? (insert (insert m k v) k v') = get? (insert m k v' : M) := by
  funext k'
  by_cases h : k = k'
  · simp [h, lookup_insert_eq]
  · simp [lookup_insert_ne _ _ _ _ h]

/-- Deleting from empty is empty.
    Corresponds to Rocq's `delete_empty`. -/
theorem delete_empty (k : K) :
    get? (delete (∅ : M) k) = get? (∅ : M) := by
  funext k'
  by_cases h : k = k'
  · simp [h, lookup_delete_eq, lookup_empty]
  · simp [lookup_delete_ne _ _ _ h, lookup_empty]

/-- The domain of an empty map is empty. -/
theorem dom_empty : FiniteMap.dom (∅ : M) = fun _ => False := by
  funext k
  simp [FiniteMap.dom, lookup_empty]

/-- The domain after insert includes the inserted key. -/
theorem dom_insert (m : M) (k : K) (v : V) :
    FiniteMap.dom (insert m k v) k := by
  simp [FiniteMap.dom, lookup_insert_eq]

/-- Key is not in domain iff lookup returns none.
    Corresponds to Rocq's `not_elem_of_dom`. -/
theorem not_elem_of_dom (m : M) (k : K) :
    ¬FiniteMap.dom m k ↔ get? m k = none := by
  simp only [FiniteMap.dom, Option.not_isSome]
  apply (lookup_None_dom m k).symm

/-- Empty is a submap of everything.
    Corresponds to Rocq's `map_empty_subseteq`. -/
theorem map_empty_subseteq (m : M) : (∅ : M) ⊆ m := by
  intro k v h
  simp [lookup_empty] at h

/-- Empty is disjoint from everything.
    Corresponds to Rocq's `map_disjoint_empty_l`. -/
theorem map_disjoint_empty_l (m : M) : FiniteMap.Disjoint (∅ : M) m := by
  intro k ⟨h₁, _⟩
  simp [lookup_empty] at h₁

/-- Characterization of lookup after insert returning Some.
    Corresponds to Rocq's `lookup_insert_Some`. -/
theorem lookup_insert_Some (m : M) (i j : K) (x y : V) :
    get? (insert m i x) j = some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ get? m j = some y) := by
  rw [lookup_insert]
  split <;> simp_all

/-- Characterization of lookup after insert being Some.
    Corresponds to Rocq's `lookup_insert_is_Some`. -/
theorem lookup_insert_is_Some (m : M) (i j : K) (x : V) :
    (get? (insert m i x) j).isSome ↔ i = j ∨ (i ≠ j ∧ (get? m j).isSome) := by
  rw [lookup_insert]
  split <;> simp_all

/-- Characterization of lookup after insert returning None.
    Corresponds to Rocq's `lookup_insert_None`. -/
theorem lookup_insert_None (m : M) (i j : K) (x : V) :
    get? (insert m i x) j = none ↔ get? m j = none ∧ i ≠ j := by
  rw [lookup_insert]
  split <;> simp_all

/-- If insert returns Some, we can extract the value.
    Corresponds to Rocq's `lookup_insert_rev`. -/
theorem lookup_insert_rev (m : M) (i : K) (x y : V) :
    get? (insert m i x) i = some y → x = y := by
  simp [lookup_insert_eq]

/-- Insert is idempotent when the key already has that value.
    Corresponds to Rocq's `insert_id`. -/
theorem insert_id (m : M) (i : K) (x : V) :
    get? m i = some x → (∀ k, get? (insert m i x) k = get? m k) := by
  intro h k
  by_cases hk : i = k
  · subst hk; simp only [lookup_insert_eq, h]
  · simp [lookup_insert_ne _ _ _ _ hk]

/-- Characterization of lookup after delete returning Some.
    Corresponds to Rocq's `lookup_delete_Some`. -/
theorem lookup_delete_Some (m : M) (i j : K) (y : V) :
    get? (delete m i) j = some y ↔ i ≠ j ∧ get? m j = some y := by
  rw [lookup_delete]
  split <;> simp_all

/-- Characterization of lookup after delete being Some.
    Corresponds to Rocq's `lookup_delete_is_Some`. -/
theorem lookup_delete_is_Some (m : M) (i j : K) :
    (get? (delete m i) j).isSome ↔ i ≠ j ∧ (get? m j).isSome := by
  rw [lookup_delete]
  split <;> simp_all

/-- Characterization of lookup after delete returning None.
    Corresponds to Rocq's `lookup_delete_None`. -/
theorem lookup_delete_None (m : M) (i j : K) :
    get? (delete m i) j = none ↔ i = j ∨ get? m j = none := by
  rw [lookup_delete]
  split <;> simp_all

-- ============================================================================
-- Induction Principles
-- ============================================================================

/-- Insert then delete is identity when key wasn't present.
    Corresponds to Rocq's `insert_delete_id`. -/
theorem insert_delete_id (m : M) (i : K) (x : V) :
    get? m i = some x → insert (delete m i) i x = m := by
  intro h
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_insert_eq, h]
  · simp [lookup_insert_ne _ _ _ _ hij, lookup_delete_ne _ _ _ hij]

/-- Delete then insert is identity.
    Corresponds to Rocq's `delete_insert_id`. -/
theorem delete_insert_id (m : M) (i : K) (x : V) :
    get? m i = none → delete (insert m i x) i = m := by
  intro h
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_delete_eq, h]
  · simp [lookup_delete_ne _ _ _ hij, lookup_insert_ne _ _ _ _ hij]

/-- Empty map is characterized by all lookups returning none. -/
theorem eq_empty_iff (m : M) : m = ∅ ↔ ∀ k, get? m k = none := by
  constructor
  · intro h k
    rw [h, lookup_empty]
  · intro h
    apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
    intro k
    rw [h, lookup_empty]

/-- Well-founded induction on maps using the strict submap relation.
    This is the most basic induction principle.
    Corresponds to Rocq's `map_ind`. -/
theorem map_ind {P : M → Prop}
    (hemp : P ∅)
    (hins : ∀ i x m, get? m i = none → P m → P (insert m i x))
    (m : M) : P m := by
  -- We use well-founded induction on the length of toList
  generalize hn : (toList m).length = n
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    cases hn' : toList m with
    | nil =>
      -- If toList is empty, the map must behave like empty
      have h : ∀ k, get? m k = none := by
        intro k
        cases hget : get? m k with
        | none => rfl
        | some v =>
          have hmem := (elem_of_map_to_list m k v).mp hget
          rw [hn'] at hmem
          simp at hmem
      -- By extensionality, m = ∅
      have heq : m = ∅ := eq_empty_iff m |>.mpr h
      rw [heq]
      exact hemp
    | cons kv kvs =>
      -- m has at least one entry
      obtain ⟨k, v⟩ := kv
      -- delete k from m gives a smaller map
      have hdel : get? m k = some v := by
        have hmem : (k, v) ∈ (k, v) :: kvs := List.Mem.head _
        have hmem' : (k, v) ∈ toList m := hn' ▸ hmem
        exact (elem_of_map_to_list m k v).mpr hmem'
      -- toList (delete m k) has one fewer element
      have hperm := map_to_list_delete m k v hdel
      -- The deleted map has strictly smaller toList (by one element)
      have hlen : (toList (delete m k)).length < n := by
        have hperm_len := hperm.length_eq
        simp only [List.length_cons] at hperm_len
        omega
      -- Apply IH to get P (delete m k)
      have ih_del := ih (toList (delete m k)).length hlen (delete m k) rfl
      -- Since get? (delete m k) k = none, we can apply hins
      have hdel_none : get? (delete m k) k = none := lookup_delete_eq m k
      -- We get P (insert (delete m k) k v)
      have result := hins k v (delete m k) hdel_none ih_del
      -- By extensionality, insert (delete m k) k v = m
      have heq := insert_delete_id m k v hdel
      rw [← heq]
      exact result

-- ============================================================================
-- Insert and Delete Composition Lemmas
-- ============================================================================

/-- Delete is idempotent.
    Corresponds to Rocq's `delete_delete_eq`. -/
theorem delete_delete_eq (m : M) (i : K) :
    delete (delete m i) i = delete m i := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_delete_eq]
  · simp [lookup_delete_ne _ _ _ hij]

/-- Delete of different keys commutes.
    Corresponds to Rocq's `delete_delete`. -/
theorem delete_delete (m : M) (i j : K) :
    delete (delete m i) j = delete (delete m j) i := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k <;> simp [lookup_delete, *]

/-- Insert then delete of different keys commutes.
    Corresponds to Rocq's `delete_insert_ne`. -/
theorem delete_insert_ne (m : M) (i j : K) (x : V) :
    i ≠ j → delete (insert m i x) j = insert (delete m j) i x := by
  intro hij
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk; exact absurd rfl hij
  · subst hik; simp [lookup_insert, lookup_delete, hjk]
  · subst hjk; simp [lookup_insert, lookup_delete, hik]
  · simp [lookup_insert, lookup_delete, hik, hjk]

/-- Delete then insert of same key gives just insert.
    Corresponds to Rocq's `insert_delete_eq`. -/
theorem insert_delete_eq (m : M) (i : K) (x : V) :
    insert (delete m i) i x = insert m i x := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_insert_eq]
  · simp [lookup_insert_ne _ _ _ _ hij, lookup_delete_ne _ _ _ hij]

/-- Insert of different keys commutes.
    Corresponds to Rocq's `insert_insert`. -/
theorem insert_insert (m : M) (i j : K) (x y : V) :
    i ≠ j → insert (insert m i x) j y = insert (insert m j y) i x := by
  intro hij
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk; exact absurd rfl hij
  · subst hik; simp [lookup_insert, hjk]
  · subst hjk; simp [lookup_insert, hik]
  · simp [lookup_insert, hik, hjk]

/-- Insert of same key keeps later value.
    Corresponds to Rocq's `insert_insert_eq`. -/
theorem insert_insert_eq' (m : M) (i : K) (x y : V) :
    insert (insert m i x) i y = insert m i y := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_insert_eq]
  · simp [lookup_insert_ne _ _ _ _ hij]

/-- Deleting from empty is empty.
    Corresponds to Rocq's `delete_empty`. -/
theorem delete_empty' (i : K) :
    delete (∅ : M) i = ∅ := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  simp [lookup_delete, lookup_empty]

/-- Delete is identity when key not present.
    Corresponds to Rocq's `delete_id`. -/
theorem delete_id (m : M) (i : K) :
    get? m i = none → delete m i = m := by
  intro h
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_delete_eq, h]
  · simp [lookup_delete_ne _ _ _ hij]

/-- Insert is identity when key already has that value.
    Corresponds to Rocq's `insert_id`. -/
theorem insert_id' (m : M) (i : K) (x : V) :
    get? m i = some x → insert m i x = m := by
  intro h
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_insert_eq, h]
  · simp [lookup_insert_ne _ _ _ _ hij]

/-- Insert on empty gives singleton.
    Corresponds to Rocq's `insert_empty`. -/
theorem insert_empty [DecidableEq K] (i : K) (x : V) :
    insert (∅ : M) i x = FiniteMap.singleton i x := by
  rfl

/-- Inserted map is non-empty.
    Corresponds to Rocq's `insert_non_empty`. -/
theorem insert_non_empty (m : M) (i : K) (x : V) :
    insert m i x ≠ ∅ := by
  intro h
  have := eq_empty_iff (insert m i x) |>.mp h i
  simp [lookup_insert_eq] at this

-- ============================================================================
-- Submap Lemmas
-- ============================================================================

/-- Delete preserves submap.
    Corresponds to Rocq's `delete_subseteq`. -/
theorem delete_subseteq (m : M) (i : K) : delete m i ⊆ m := by
  intro k v h
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at h
  · simp [lookup_delete_ne _ _ _ hik] at h
    exact h

/-- Delete of present key is strict submap (submap but not equal).
    Corresponds to Rocq's `delete_subset`. -/
theorem delete_subset (m : M) (i : K) (v : V) :
    get? m i = some v → delete m i ⊆ m ∧ delete m i ≠ m := by
  intro hi
  constructor
  · exact delete_subseteq m i
  · intro heq
    have : get? (delete m i) i = get? m i := by rw [heq]
    simp [lookup_delete_eq, hi] at this

/-- Insert on non-present key gives superset.
    Corresponds to Rocq's `insert_subseteq`. -/
theorem insert_subseteq (m : M) (i : K) (x : V) :
    get? m i = none → m ⊆ insert m i x := by
  intro hi k v hk
  by_cases hik : i = k
  · subst hik
    simp [hi] at hk
  · simp [lookup_insert_ne _ _ _ _ hik, hk]

/-- Insert on non-present key gives strict superset (superset but not equal).
    Corresponds to Rocq's `insert_subset`. -/
theorem insert_subset (m : M) (i : K) (x : V) :
    get? m i = none → m ⊆ insert m i x ∧ m ≠ insert m i x := by
  intro hi
  constructor
  · exact insert_subseteq m i x hi
  · intro heq
    have h2 : get? (insert m i x) i = some x := lookup_insert_eq m i x
    rw [← heq] at h2
    rw [hi] at h2
    exact Option.noConfusion h2

/-- Delete is monotone with respect to submap.
    Corresponds to Rocq's `delete_mono`. -/
theorem delete_mono (m₁ m₂ : M) (i : K) :
    m₁ ⊆ m₂ → delete m₁ i ⊆ delete m₂ i := by
  intro hsub k v hk
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at hk
  · simp [lookup_delete_ne _ _ _ hik] at hk ⊢
    exact hsub k v hk

/-- Insert is monotone with respect to submap.
    Corresponds to Rocq's `insert_mono`. -/
theorem insert_mono (m₁ m₂ : M) (i : K) (x : V) :
    m₁ ⊆ m₂ → insert m₁ i x ⊆ insert m₂ i x := by
  intro hsub k v hk
  by_cases hik : i = k
  · subst hik
    simp [lookup_insert_eq] at hk ⊢
    exact hk
  · simp [lookup_insert_ne _ _ _ _ hik] at hk ⊢
    exact hsub k v hk

-- ============================================================================
-- Singleton Lemmas
-- ============================================================================

/-- Singleton is non-empty.
    Corresponds to Rocq's `map_non_empty_singleton`. -/
theorem singleton_non_empty (i : K) (x : V) :
    FiniteMap.singleton i x ≠ (∅ : M) := by
  exact insert_non_empty ∅ i x

/-- Delete from singleton of same key is empty.
    Corresponds to Rocq's `delete_singleton_eq`. -/
theorem delete_singleton_eq (i : K) (x : V) :
    delete (FiniteMap.singleton i x : M) i = ∅ := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  simp [FiniteMap.singleton, lookup_delete, lookup_insert, lookup_empty]

/-- Delete from singleton of different key is identity.
    Corresponds to Rocq's `delete_singleton_ne`. -/
theorem delete_singleton_ne (i j : K) (x : V) :
    i ≠ j → delete (FiniteMap.singleton j x : M) i = FiniteMap.singleton j x := by
  intro hij
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  simp [FiniteMap.singleton, lookup_delete, lookup_insert, lookup_empty]
  intro hik
  intro hjk
  subst hik hjk
  exact hij rfl

-- ============================================================================
-- map_Forall Predicate
-- ============================================================================

/-- A predicate holds for all key-value pairs in the map.
    Corresponds to Rocq's `map_Forall`. -/
def map_Forall (P : K → V → Prop) (m : M) : Prop :=
  ∀ k v, get? m k = some v → P k v

/-- map_Forall is equivalent to checking toList.
    Corresponds to Rocq's `map_Forall_to_list`. -/
theorem map_Forall_to_list (P : K → V → Prop) (m : M) :
    map_Forall P m ↔ ∀ kv ∈ toList m, P kv.1 kv.2 := by
  constructor
  · intro hfa kv hmem
    have := (elem_of_map_to_list m kv.1 kv.2).mpr hmem
    exact hfa kv.1 kv.2 this
  · intro hlist k v hget
    have := (elem_of_map_to_list m k v).mp hget
    exact hlist (k, v) this

/-- map_Forall holds vacuously on empty map.
    Corresponds to Rocq's `map_Forall_empty`. -/
theorem map_Forall_empty (P : K → V → Prop) : map_Forall P (∅ : M) := by
  intro k v h
  simp [lookup_empty] at h

/-- map_Forall is preserved by implication.
    Corresponds to Rocq's `map_Forall_impl`. -/
theorem map_Forall_impl (P Q : K → V → Prop) (m : M) :
    map_Forall P m → (∀ k v, P k v → Q k v) → map_Forall Q m := by
  intro hp himpl k v hget
  exact himpl k v (hp k v hget)

/-- map_Forall on insert implies P holds for the inserted value.
    Corresponds to Rocq's `map_Forall_insert_1_1`. -/
theorem map_Forall_insert_1_1 (P : K → V → Prop) (m : M) (i : K) (x : V) :
    map_Forall P (insert m i x) → P i x := by
  intro hfa
  exact hfa i x (lookup_insert_eq m i x)

/-- map_Forall on insert implies map_Forall on original (when key not present).
    Corresponds to Rocq's `map_Forall_insert_1_2`. -/
theorem map_Forall_insert_1_2 (P : K → V → Prop) (m : M) (i : K) (x : V) :
    get? m i = none → map_Forall P (insert m i x) → map_Forall P m := by
  intro hi hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [hi] at hget
  · have : get? (insert m i x) k = some v := by
      simp [lookup_insert_ne _ _ _ _ hik, hget]
    exact hfa k v this

/-- map_Forall is preserved by insert when P holds.
    Corresponds to Rocq's `map_Forall_insert_2`. -/
theorem map_Forall_insert_2 (P : K → V → Prop) (m : M) (i : K) (x : V) :
    P i x → map_Forall P m → map_Forall P (insert m i x) := by
  intro hpix hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [lookup_insert_eq] at hget
    rw [← hget]
    exact hpix
  · simp [lookup_insert_ne _ _ _ _ hik] at hget
    exact hfa k v hget

/-- map_Forall characterization for insert when key not present.
    Corresponds to Rocq's `map_Forall_insert`. -/
theorem map_Forall_insert (P : K → V → Prop) (m : M) (i : K) (x : V) :
    get? m i = none → (map_Forall P (insert m i x) ↔ P i x ∧ map_Forall P m) := by
  intro hi
  constructor
  · intro hfa
    exact ⟨map_Forall_insert_1_1 P m i x hfa, map_Forall_insert_1_2 P m i x hi hfa⟩
  · intro ⟨hpix, hfa⟩
    exact map_Forall_insert_2 P m i x hpix hfa

/-- map_Forall on singleton.
    Corresponds to Rocq's `map_Forall_singleton`. -/
theorem map_Forall_singleton (P : K → V → Prop) (i : K) (x : V) :
    map_Forall P (FiniteMap.singleton i x : M) ↔ P i x := by
  constructor
  · intro hfa
    exact hfa i x (lookup_singleton_eq i x)
  · intro hpix k v hget
    simp [lookup_singleton] at hget
    obtain ⟨rfl, rfl⟩ := hget
    exact hpix

/-- map_Forall is preserved by delete.
    Corresponds to Rocq's `map_Forall_delete`. -/
theorem map_Forall_delete (P : K → V → Prop) (m : M) (i : K) :
    map_Forall P m → map_Forall P (delete m i) := by
  intro hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at hget
  · simp [lookup_delete_ne _ _ _ hik] at hget
    exact hfa k v hget

-- ============================================================================
-- Disjoint Lemmas
-- ============================================================================

/-- Characterization of disjoint maps.
    Corresponds to Rocq's `map_disjoint_spec`. -/
theorem map_disjoint_spec (m₁ m₂ : M) :
    FiniteMap.Disjoint m₁ m₂ ↔ ∀ k, get? m₁ k = none ∨ get? m₂ k = none := by
  constructor
  · intro hdisj k
    by_cases h1 : (get? m₁ k).isSome
    · by_cases h2 : (get? m₂ k).isSome
      · exact absurd ⟨h1, h2⟩ (hdisj k)
      · simp only [Option.not_isSome_iff_eq_none] at h2
        exact Or.inr h2
    · simp only [Option.not_isSome_iff_eq_none] at h1
      exact Or.inl h1
  · intro h k ⟨hs1, hs2⟩
    cases h k with
    | inl h1 => simp [h1] at hs1
    | inr h2 => simp [h2] at hs2

/-- Insert preserves disjointness when key not in the other map.
    Corresponds to Rocq's `map_disjoint_insert_l`. -/
theorem map_disjoint_insert_l (m₁ m₂ : M) (i : K) (x : V) :
    get? m₂ i = none →
    FiniteMap.Disjoint m₁ m₂ →
    FiniteMap.Disjoint (insert m₁ i x) m₂ := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [lookup_insert_ne _ _ _ _ hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

/-- Insert preserves disjointness (right version).
    Corresponds to Rocq's `map_disjoint_insert_r`. -/
theorem map_disjoint_insert_r (m₁ m₂ : M) (i : K) (x : V) :
    get? m₁ i = none →
    FiniteMap.Disjoint m₁ m₂ →
    FiniteMap.Disjoint m₁ (insert m₂ i x) := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [lookup_insert_ne _ _ _ _ hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

/-- Delete preserves disjointness.
    Corresponds to Rocq's `map_disjoint_delete_l`. -/
theorem map_disjoint_delete_l (m₁ m₂ : M) (i : K) :
    FiniteMap.Disjoint m₁ m₂ → FiniteMap.Disjoint (delete m₁ i) m₂ := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at hs1
  · simp [lookup_delete_ne _ _ _ hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

/-- Delete preserves disjointness (right version).
    Corresponds to Rocq's `map_disjoint_delete_r`. -/
theorem map_disjoint_delete_r (m₁ m₂ : M) (i : K) :
    FiniteMap.Disjoint m₁ m₂ → FiniteMap.Disjoint m₁ (delete m₂ i) := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at hs2
  · simp [lookup_delete_ne _ _ _ hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

/-- Singleton is disjoint from map when key not present.
    Corresponds to Rocq's `map_disjoint_singleton_l`. -/
theorem map_disjoint_singleton_l (m : M) (i : K) (x : V) :
    get? m i = none → FiniteMap.Disjoint (FiniteMap.singleton i x) m := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [FiniteMap.singleton, lookup_insert_ne _ _ _ _ hik, lookup_empty] at hs1

/-- Singleton is disjoint from map when key not present (right version).
    Corresponds to Rocq's `map_disjoint_singleton_r`. -/
theorem map_disjoint_singleton_r (m : M) (i : K) (x : V) :
    get? m i = none → FiniteMap.Disjoint m (FiniteMap.singleton i x) := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [FiniteMap.singleton, lookup_insert_ne _ _ _ _ hik, lookup_empty] at hs2

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

theorem map_disjoint_empty_r [DecidableEq K] [FiniteMapLaws M K V] (m : M) : Disjoint m (∅ : M) :=
  disjoint_symm (FiniteMapLaws.map_disjoint_empty_l m)

/-- `m₂` and `m₁ \ m₂` are disjoint.
    This is unconditional - the difference by definition removes all keys in m₂. -/
theorem disjoint_difference_r [DecidableEq K] [FiniteMapLaws M K V] [FiniteMapLawsSelf M K V]
    (m₁ m₂ : M) : Disjoint m₂ (m₁ \ m₂) := by
  intro k ⟨h_in_m2, h_in_diff⟩
  -- h_in_m2: (get? m₂ k).isSome
  -- h_in_diff: (get? (m₁ \ m₂) k).isSome
  -- By lookup_difference, (m₁ \ m₂) !! k = if m₂ !! k is Some then none else m₁ !! k
  -- So if m₂ !! k is Some, then (m₁ \ m₂) !! k = none, contradiction with h_in_diff
  rw [lookup_difference] at h_in_diff
  simp only [h_in_m2, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at h_in_diff

/-- toList of difference union: `toList (m₂ ∪ (m₁ \ m₂))` is a permutation of `toList m₁`
    when `m₂ ⊆ m₁`. This is the key lemma for `big_sepM_subseteq`. -/
theorem toList_difference_union [DecidableEq K] [DecidableEq V] [FiniteMapLaws M K V] [FiniteMapLawsSelf M K V]
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
  -- Need: toList m₂ ++ filter (not in m₂) (toList m₁) ~ toList m₁
  -- Strategy: show toList m₂ ~ filter (in m₂) (toList m₁), then use filter_append_perm

  -- Helper: filter preserves Nodup
  have nodup_filter : ∀ {α : Type _} (p : α → Bool) (l : List α), l.Nodup → (l.filter p).Nodup := by
    intro α p l h
    induction l with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
      rw [List.nodup_cons] at h
      simp only [List.filter_cons]
      split
      · rw [List.nodup_cons]
        constructor
        · intro hx
          have := List.mem_filter.mp hx
          exact h.1 this.1
        · exact ih h.2
      · exact ih h.2

  -- Define the predicate for "key is in m₂"
  let p : K × V → Bool := fun kv => (get? m₂ kv.1).isSome

  -- Step 1: toList m₂ ~ filter p (toList m₁)
  -- Both are nodup and have the same membership
  have hperm_m2_filter : (toList m₂).Perm ((toList m₁).filter p) := by
    -- Use perm_of_nodup_of_mem_iff
    have hnd₁ : (toList m₂).Nodup :=
      FiniteMapLaws.nodup_of_nodup_map_fst _ (NoDup_map_to_list m₂)
    have hnd₂ : ((toList m₁).filter p).Nodup :=
      nodup_filter p _ (FiniteMapLaws.nodup_of_nodup_map_fst _ (NoDup_map_to_list m₁))
    apply FiniteMapLaws.perm_of_nodup_of_mem_iff hnd₁ hnd₂
    intro ⟨k, v⟩
    simp only [List.mem_filter, p]
    constructor
    · -- (k, v) ∈ toList m₂ → (k, v) ∈ toList m₁ ∧ (get? m₂ k).isSome
      intro hmem
      have hget : get? m₂ k = some v := (elem_of_map_to_list m₂ k v).mpr hmem
      constructor
      · -- (k, v) ∈ toList m₁
        have hget₁ : get? m₁ k = some v := hsub k v hget
        exact (elem_of_map_to_list m₁ k v).mp hget₁
      · -- (get? m₂ k).isSome
        simp [hget]
    · -- (k, v) ∈ toList m₁ ∧ (get? m₂ k).isSome → (k, v) ∈ toList m₂
      intro ⟨hmem₁, hisSome⟩
      have hget₁ : get? m₁ k = some v := (elem_of_map_to_list m₁ k v).mpr hmem₁
      obtain ⟨v', hget₂⟩ := Option.isSome_iff_exists.mp hisSome
      -- Since m₂ ⊆ m₁ and both have the same key, the values must match
      -- We need: v = v'
      have hget₁' : get? m₁ k = some v' := hsub k v' hget₂
      have : v = v' := Option.some.inj (hget₁.symm.trans hget₁')
      rw [this]
      exact (elem_of_map_to_list m₂ k v').mp hget₂

  -- Step 2: filter (not p) = filter (isNone ∘ get? m₂ ∘ fst)
  have hfilter_eq : (toList m₁).filter (fun x => !p x) =
                    (toList m₁).filter (fun kv => (get? m₂ kv.fst).isNone) := by
    congr 1
    funext kv
    simp only [p, Option.not_isSome]

  -- Step 3: Combine using filter_append_perm
  have hstep1 : (toList m₂ ++ (toList m₁).filter (fun kv => (get? m₂ kv.fst).isNone)) =
                (toList m₂ ++ (toList m₁).filter (fun x => !p x)) := by rw [hfilter_eq]
  have hstep2 : (toList m₂ ++ (toList m₁).filter (fun x => !p x)).Perm
                ((toList m₁).filter p ++ (toList m₁).filter (fun x => !p x)) :=
    List.Perm.append hperm_m2_filter (List.Perm.refl _)
  have hstep3 : ((toList m₁).filter p ++ (toList m₁).filter (fun x => !p x)).Perm (toList m₁) :=
    List.filter_append_perm p (toList m₁)
  exact (List.Perm.of_eq hstep1).trans (hstep2.trans hstep3)

/-- Key identity: `m₂ ∪ (m₁ \ m₂) = m₁` when `m₂ ⊆ m₁`.
    Corresponds to Rocq's `map_difference_union`.

    This is proved via `map_eq` using `lookup_union` and `lookup_difference`,
    without requiring `DecidableEq V`. -/
theorem map_difference_union [DecidableEq K] [FiniteMapLaws M K V] [FiniteMapLawsSelf M K V]
    (m₁ m₂ : M) (hsub : m₂ ⊆ m₁) : m₂ ∪ (m₁ \ m₂) = m₁ := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  rw [lookup_union, lookup_difference]
  -- Case split on whether k is in m₂
  cases hm2 : get? m₂ k with
  | none =>
    -- If k ∉ m₂, then (m₁ \ m₂) !! k = m₁ !! k
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
  | some v =>
    -- If k ∈ m₂ with value v, then m₂ !! k = some v
    -- and since m₂ ⊆ m₁, we have m₁ !! k = some v
    simp only [Option.isSome_some, ↓reduceIte, Option.orElse_some]
    exact (hsub k v hm2).symm

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
