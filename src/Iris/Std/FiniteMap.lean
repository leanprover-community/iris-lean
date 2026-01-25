/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

import Iris.Std.List

/-! ## Abstract Finite Map Interface

This file defines an abstract interface for finite maps, inspired by stdpp's `fin_maps`. -/

namespace Iris.Std

/-- The type `M` represents a finite map from keys of type `K` to values of type `V`. -/
class FiniteMap (K : outParam (Type u)) (M : Type u' → Type _) where
  /-- Lookup a key in the map, returning `none` if not present.
      Corresponds to Rocq's `lookup`. -/
  get? : M V → K → Option V
  /-- Insert or update a key-value pair.
      Corresponds to Rocq's `insert`. -/
  insert : M V → K → V → M V
  /-- Remove a key from the map.
      Corresponds to Rocq's `delete`. -/
  delete : M V → K → M V
  /-- The empty map. -/
  empty : M V
  /-- Convert the map to a list of key-value pairs.
      Corresponds to Rocq's `map_to_list`. -/
  toList : M V → List (K × V)
  /-- Construct a map from a list of key-value pairs.
      Corresponds to Rocq's `list_to_map`. -/
  ofList : List (K × V) → M V
  /-- Fold over all key-value pairs in the map.
      The order of folding depends on the internal representation.
      Corresponds to Rocq's `map_fold`. -/
  fold {A : Type u'} : (K → V → A → A) → A → M V → A

export FiniteMap (get? insert delete toList ofList fold)

namespace FiniteMap

variable {K : Type u} {V : Type u'} {M : Type u' → Type _} [FiniteMap K M]

/-- Empty map instance for `∅` notation. -/
instance : EmptyCollection (M V) := ⟨empty⟩

/-- Singleton map containing exactly one key-value pair.
    Corresponds to Rocq's `{[ i := x ]}` notation. -/
def singleton (k : K) (v : V) : M V := insert ∅ k v

/-- Union of two maps (left-biased: values from `m₁` take precedence).
    Corresponds to Rocq's `m₁ ∪ m₂`. -/
def union (m₁ m₂ : M V) : M V:=
  (toList m₁).foldl (fun acc (k, v) => insert acc k v) m₂

instance : Union (M V):= ⟨union⟩

/-- Two maps have disjoint domains.
    Corresponds to Rocq's `map_disjoint`. -/
def disjoint (m₁ m₂ : M V) : Prop := ∀ k, ¬((get? m₁ k).isSome ∧ (get? m₂ k).isSome)

/-- Submap relation: `m₁` is a submap of `m₂` if every key-value pair in `m₁` is also in `m₂`.
    Corresponds to Rocq's `map_subseteq`. -/
def submap (m₁ m₂ : M V) : Prop := ∀ k v, get? m₁ k = some v → get? m₂ k = some v

instance : HasSubset (M V) := ⟨submap⟩

/-- Map a function over all values in the map.
    Corresponds to Rocq's `fmap` (notation `f <$> m`). -/
def map (f : V → V') : M V → (M V') :=
  fun m => ofList ((toList m).map (fun (k, v) => (k, f v)))

/-- Filter and map: apply a function that can optionally drop entries.
    Corresponds to Rocq's `omap`. -/
def filterMap (f : V → Option V) : M V → M V :=
  fun m => ofList ((toList m).filterMap (fun (k, v) => (f v).map (k, ·)))

/-- Alias for `filterMap` to match Rocq's naming. -/
abbrev omap := @filterMap

/-- Filter entries by a predicate on key-value pairs.
    Corresponds to Rocq's `filter`. -/
def filter (φ : K → V → Bool) : M V → M V :=
  fun m => ofList ((toList m).filter (fun (k, v) => φ k v))

/-- Zip two maps with a combining function.
    Corresponds to Rocq's `map_zip_with`. -/
def zipWith {V' : Type _} {V'' : Type _} (f : V → V' → V'') (m₁ : M V) (m₂ : M V') : M V'' :=
  ofList ((toList m₁).filterMap (fun (k, v) =>
    match get? m₂ k with
    | some v' => some (k, f v v')
    | none => none))

/-- Zip two maps: combine values at matching keys into pairs.
    This is `zipWith Prod.mk`.
    Corresponds to Rocq's `map_zip`. -/
def zip (m₁ : M V) (m₂ : M V') : M (V × V') :=
  zipWith Prod.mk m₁ m₂

/-- Membership: a key is in the map if it has a value. -/
def mem (m : M V) (k : K) : Prop := (get? m k).isSome

/-- Difference: remove all keys in `m₂` from `m₁`.
    Corresponds to Rocq's `map_difference`. -/
def difference (m₁ m₂ : M V) : M V :=
  ofList ((toList m₁).filter (fun (k, _) => (get? m₂ k).isNone))

instance : SDiff (M V) := ⟨difference⟩

/-- Transform keys of a map using an injective function.
    Corresponds to Rocq's `kmap`. -/
def kmap {K' : Type u} {M' : Type u' → _} [FiniteMap K' M'] (f : K → K') (m : M V) : (M' V) :=
  ofList ((toList m).map (fun (k, v) => (f k, v)))

/-- Convert a list to a map with sequential natural number keys starting from `start`.
    Corresponds to Rocq's `map_seq`. -/
def map_seq [FiniteMap Nat M] (start : Nat) (l : List V) : M V :=
  ofList (l.mapIdx (fun i v => (start + i, v)))

/-- Check if a key is the first key in the map's `toList` representation.
    Corresponds to Rocq's `map_first_key`: `∃ x, map_to_list m !! 0 = Some (i,x)`. -/
def firstKey (m : M V) (i : K) : Prop :=
  ∃ x, (toList m).head? = some (i, x)

/-- Corresponds to Rocq's `map_Forall`. -/
def Forall (P : K → V → Prop) (m : M V) : Prop :=
  ∀ k v, get? m k = some v → P k v

end FiniteMap

/-- Notation for singleton map: `{[k := v]}` -/
scoped syntax "{[" term " := " term "]}" : term

scoped macro_rules
  | `({[$k := $v]}) => `(FiniteMap.singleton $k $v)

/-- Notation for map disjointness: `m₁ ##ₘ m₂` -/
scoped infix:50 " ##ₘ " => FiniteMap.disjoint

/-- Membership instance for finite maps: `k ∈ m` means the key `k` is in the map `m`. -/
instance  {K : Type u} {M : Type u' → Type _}  [inst : FiniteMap K M] : Membership K (M V) :=
  ⟨fun (m : M V) (k : K) => (inst.get? m k).isSome⟩

/-- Laws that a finite map implementation must satisfy. -/
class FiniteMapLaws (K : (outParam (Type u))) (M : Type u' → Type _)
    [DecidableEq K] [FiniteMap K M] where
  /-- Corresponds to Rocq's `map_eq`. -/
  ext : ∀ (m₁ m₂ : M V), (∀ i, get? m₁ i = get? m₂ i) → m₁ = m₂
  /-- Corresponds to Rocq's `lookup_empty`. -/
  get?_empty : ∀ k, get? (∅ : M V) k = none
  /-- Corresponds to Rocq's `lookup_insert_eq`. -/
  get?_insert_same : ∀ (m : M V) k v, get? (insert m k v) k = some v
  /-- Corresponds to Rocq's `lookup_insert_ne`. -/
  get?_insert_ne : ∀ (m : M V) k k' v, k ≠ k' → get? (insert m k v) k' = get? m k'
  /-- Corresponds to Rocq's `lookup_delete_eq`. -/
  get?_delete_same : ∀ (m : M V) k, get? (delete m k) k = none
  /-- Corresponds to Rocq's `lookup_delete_ne`. -/
  get?_delete_ne : ∀ (m : M V) k k', k ≠ k' → get? (delete m k) k' = get? m k'
  /-- Corresponds to Rocq's `lookup_union`. -/
  get?_union : ∀ (m₁ m₂ : M V) k,
    get? (m₁ ∪ m₂) k = (get? m₁ k).orElse (fun _ => get? m₂ k)
  /-- Corresponds to Rocq's `lookup_difference`. -/
  get?_difference : ∀ (m₁ m₂ : M V) k,
    get? (m₁ \ m₂) k = if (get? m₂ k).isSome then none else get? m₁ k
  /-- Corresponds to Rocq's implicit behavior of `list_to_map`. -/
  ofList_nil : (ofList [] : M V) = ∅
  /-- Corresponds to Rocq's implicit behavior of `list_to_map`. -/
  ofList_cons : ∀ (k : K) (v : V) (l : List (K × V)),
    (ofList ((k, v) :: l) : M V) = insert (ofList l) k v
  /-- Corresponds to Rocq's `map_to_list_spec`. -/
  toList_spec (m : M V) :
    (toList m).Nodup ∧ (∀ i x, (i, x) ∈ toList m ↔ get? m i = some x)
  /-- Corresponds to Rocq's `map_ind`. -/
  induction_on {P : M V → Prop}
    (hemp : P ∅)
    (hins : ∀ i x m, get? m i = none → P m → P (insert m i x))
    (m : M V) : P m

/-- Self-referential extended laws. -/
class FiniteMapLawsSelf (K : outParam (Type u)) (M : Type u' → Type _)
    [DecidableEq K] [FiniteMap K M] [FiniteMapLaws K M] where
  /-- toList of filterMap is related to filterMap over toList. -/
  toList_filterMap : ∀ (m : M V) (f : V → Option V),
    (toList (FiniteMap.filterMap (M := M) f m)).Perm
      ((toList m).filterMap (fun kv => (f kv.2).map (kv.1, ·)))
  /-- toList of filter is related to filter over toList. -/
  toList_filter : ∀ (m : M V) (φ : K → V → Bool),
    (toList (FiniteMap.filter (M := M) φ m)).Perm
      ((toList m).filter (fun kv => φ kv.1 kv.2))

/-- Laws for kmap operation. -/
class FiniteMapKmapLaws (K : outParam (Type u)) (K' : outParam (Type u)) (M : Type u' → Type _) (M' : Type u' → Type _)
    [DecidableEq K] [DecidableEq K'] [FiniteMap K M] [FiniteMap K' M']
    [FiniteMapLaws K M] [FiniteMapLaws K' M'] where
  /-- toList of kmap is related to mapping over toList.
      Corresponds to Rocq's `map_to_list_kmap`. -/
  toList_kmap : ∀ (f : K → K') (m : M V),
    (∀ {x y}, f x = f y → x = y) →  -- f is injective
    (toList (FiniteMap.kmap (M' := M') f m)).Perm
      ((toList m).map (fun (k, v) => (f k, v)))

/-- Laws for map_seq operation. -/
class FiniteMapSeqLaws (M : Type u → Type _) [FiniteMap Nat M] [FiniteMapLaws Nat M] where
  /-- toList of map_seq is related to zip with sequence.
      Corresponds to Rocq's `map_to_list_seq`. -/
  toList_map_seq : ∀ (start : Nat) (l : List V),
    (toList (FiniteMap.map_seq start l : M V)).Perm
      ((List.range' start l.length).zip l)

export FiniteMapLaws (ext
get?_empty
get?_insert_same get?_insert_ne
get?_delete_same get?_delete_ne
ofList_nil ofList_cons
toList_spec
induction_on)

export FiniteMapLawsSelf (toList_filterMap toList_filter)
export FiniteMapKmapLaws (toList_kmap)
export FiniteMapSeqLaws (toList_map_seq)

namespace FiniteMapLaws

variable {K : Type u} {V : Type u'} {M : Type u' → Type _}
variable [DecidableEq K] [FiniteMap K M] [FiniteMapLaws K M]

private theorem mem_of_get?_ofList (l : List (K × V)) (k : K) (v : V) :
    get? (ofList l : M V) k = some v → (k, v) ∈ l := by
  intro h
  induction l with
  | nil =>
    simp [ofList_nil, get?_empty] at h
  | cons kv kvs ih =>
    rw [ofList_cons] at h
    by_cases heq : kv.1 = k
    · have eq_val : kv.2 = v := by
        rw [heq, get?_insert_same] at h
        exact Option.some.inj h
      have eq_kv : kv = (k, v) := by
        ext
        · exact heq
        · exact eq_val
      rw [← eq_kv]
      exact List.Mem.head _
    · rw [get?_insert_ne _ _ _ _ heq] at h
      have := ih h
      exact List.Mem.tail _ this


/-- Corresponds to Rocq's `lookup_insert`. -/
theorem get?_insert (m : M V) (k k' : K) (v : V) :
    get? (insert m k v) k' = if k = k' then some v else get? m k' := by
  split
  · next h => rw [h, get?_insert_same]
  · next h => exact get?_insert_ne m k k' v h

/-- Corresponds to Rocq's `lookup_delete`. -/
theorem get?_delete (m : M V) (k k' : K) :
    get? (delete m k) k' = if k = k' then none else get? m k' := by
  split
  · next h => rw [h, get?_delete_same]
  · next h => exact get?_delete_ne m k k' h

/-- Corresponds to Rocq's `insert_delete_eq`. -/
theorem get?_insert_delete (m : M V) (k k' : K) (v : V) :
    get? (insert (delete m k) k v) k' = get? (insert m k v) k' := by
  by_cases h : k = k'
  · simp [h, get?_insert_same]
  · simp [get?_insert_ne _ _ _ _ h, get?_delete_ne _ _ _ h]

/-- Corresponds to Rocq's `NoDup_map_to_list`. -/
theorem nodup_toList (m : M V): (toList m).Nodup := by
   apply (toList_spec m).1

/-- If a list has no duplicates and the projection is injective on list elements,
    then the mapped list has no duplicates. -/
theorem List.Nodup.map_of_injective {α β : Type _} {l : List α} {f : α → β}
    (hnodup : l.Nodup) (hinj : ∀ a b, a ∈ l → b ∈ l → f a = f b → a = b) :
    (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hnodup
    constructor
    · intro hx_in
      rw [List.mem_map] at hx_in
      obtain ⟨y, hy_mem, hy_eq⟩ := hx_in
      have hx_mem : x ∈ x :: xs := List.mem_cons_self
      have hy_mem' : y ∈ x :: xs := List.mem_cons_of_mem x hy_mem
      have : x = y := hinj x y hx_mem hy_mem' hy_eq.symm
      subst this
      exact hnodup.1 hy_mem
    · apply ih hnodup.2
      intro a b ha hb
      exact hinj a b (List.mem_cons_of_mem x ha) (List.mem_cons_of_mem x hb)

/-- Keys of toList have no duplicates. -/
theorem nodup_toList_keys (m : M V) : (toList m).map Prod.fst |>.Nodup := by
  apply List.Nodup.map_of_injective (nodup_toList m)
  intro ⟨k₁, v₁⟩ ⟨k₂, v₂⟩ h1 h2 heq
  simp at heq
  obtain ⟨_, hmem⟩ := toList_spec (M := M) (K := K) (V := V) m
  have hv1 : get? m k₁ = some v₁ := (hmem k₁ v₁).mp h1
  have hv2 : get? m k₂ = some v₂ := (hmem k₂ v₂).mp h2
  rw [heq] at hv1
  rw [hv1] at hv2
  cases hv2
  ext <;> simp [heq]

/-- Corresponds to Rocq's `elem_of_map_to_list`. -/
theorem mem_toList (m : M V) : ∀ k v, (k, v) ∈ toList m ↔ get? m k = some v := by
  apply (toList_spec m).2

/-- Corresponds to Rocq's `elem_of_list_to_map_2`. -/
theorem mem_of_mem_ofList (l : List (K × V)) (i : K) (x : V) :
    get? (ofList l : M V) i = some x → (i, x) ∈ l := by
  induction l with
  | nil =>
    intro h
    rw [ofList_nil, get?_empty] at h
    cases h
  | cons kv l ih =>
    intro h
    obtain ⟨k, v⟩ := kv
    rw [ofList_cons] at h
    rw [get?_insert] at h
    split at h
    · next heq =>
        cases h
        rw [← heq]
        simp [List.mem_cons]
    · next hne =>
        have : (i, x) ∈ l := ih h
        exact List.mem_cons_of_mem _ this

/-- Corresponds to Rocq's `elem_of_list_to_map_1`. -/
theorem mem_ofList_of_mem (l : List (K × V)) (i : K) (x : V) :
    (l.map Prod.fst).Nodup → (i, x) ∈ l → get? (ofList l : M V) i = some x := by
  intro hnodup hmem
  induction l with
  | nil =>
    simp at hmem
  | cons kv l ih =>
    obtain ⟨k, v⟩ := kv
    rw [List.map_cons, List.nodup_cons] at hnodup
    simp [List.mem_cons] at hmem
    cases hmem with
    | inl heq =>
      obtain ⟨rfl, rfl⟩ := heq
      rw [ofList_cons, get?_insert_same]
    | inr hmem' =>
      obtain ⟨hk_notin, hnodup_tail⟩ := hnodup
      have hi_in : i ∈ l.map Prod.fst := by
        rw [List.mem_map]
        exact ⟨(i, x), hmem', rfl⟩
      have hne : k ≠ i := by
        intro heq
        subst heq
        exact hk_notin hi_in
      have : get? (ofList l : M V) i = some x := ih hnodup_tail hmem'
      rw [ofList_cons, get?_insert_ne _ _ _ _ hne, this]

/-- Corresponds to Rocq's `elem_of_list_to_map` -/
theorem mem_ofList (l : List (K × V)) i x (hnodup : (l.map Prod.fst).Nodup):
   (i,x) ∈ l ↔ get? (ofList l : M V) i = some x := by
    constructor
    apply mem_ofList_of_mem; exact hnodup
    apply mem_of_mem_ofList

/-- Corresponds to Rocq's `list_to_map_inj`. -/
theorem ofList_injective [DecidableEq V] (l1 l2 : List (K × V)) :
    (l1.map Prod.fst).Nodup → (l2.map Prod.fst).Nodup →
    (ofList l1 : M V) = ofList l2 → l1.Perm l2 := by
  intro hnodup1 hnodup2 heq
  have hnodup1' : l1.Nodup := List.nodup_of_nodup_map_fst l1 hnodup1
  have hnodup2' : l2.Nodup := List.nodup_of_nodup_map_fst l2 hnodup2
  haveI : DecidableEq (K × V) := inferInstance
  apply List.perm_of_nodup_of_mem_iff hnodup1' hnodup2'
  intro ⟨i, x⟩
  rw [mem_ofList (M := M) (K := K) l1 i x hnodup1,
      mem_ofList (M := M) (K := K) l2 i x hnodup2]
  rw [heq]

/-- Coresponds to Rocq's `list_to_map_to_list` -/
theorem ofList_toList (m : M V) :
    ofList (toList m) = m := by
  apply ext (K := K)
  intro i
  cases heq : get? m i
  · cases heq' : get? (ofList (toList m) : M V) i
    · rfl
    · rename_i val
      have hmem : (i, val) ∈ toList m :=
        (mem_ofList (M := M) (K := K) (toList m) i val (nodup_toList_keys m)).mpr heq'
      have : get? m i = some val := (mem_toList m i val).mp hmem
      rw [heq] at this
      exact Option.noConfusion this
  · rename_i val
    have hmem : (i, val) ∈ toList m := (mem_toList m i val).mpr heq
    have : get? (ofList (toList m) : M V) i = some val :=
      (mem_ofList (M := M) (K := K) (toList m) i val (nodup_toList_keys m)).mp hmem
    rw [this]

  /-- Corresponds to Rocq's `map_to_list_to_map`. -/
 theorem toList_ofList [DecidableEq V] : ∀ (l : List (K × V)), (l.map Prod.fst).Nodup →
    (toList (ofList l : M V)).Perm l := by
  intro l hnodup
  apply ofList_injective (M := M) (K:=K)
  · exact nodup_toList_keys (M := M) (K := K) (V := V) (ofList l)
  · exact hnodup
  rw [ofList_toList]

/-- Two maps with the same get? behavior have permutation-equivalent toLists. -/
theorem toList_perm_of_get?_eq [DecidableEq V] {m₁ m₂ : M V}
    (h : ∀ k, get? m₁ k = get? m₂ k) : (toList m₁).Perm (toList m₂) := by
  have hnodup₁ := nodup_toList (M := M) (K := K) (V := V) m₁
  have hnodup₂ := nodup_toList (M := M) (K := K) (V := V) m₂
  have hmem : ∀ kv, kv ∈ toList m₁ ↔ kv ∈ toList m₂ := by
    intro ⟨k, v⟩
    rw [mem_toList m₁ k v, mem_toList m₂ k v, h]
  exact List.perm_of_nodup_of_mem_iff hnodup₁ hnodup₂ hmem

/-- toList of insert and insert-after-delete are permutations of each other. -/
theorem toList_insert_delete [DecidableEq V] (m : M V) (k : K) (v : V) :
    (toList (insert m k v)).Perm (toList (insert (delete m k) k v)) :=
  toList_perm_of_get?_eq (fun k' => (get?_insert_delete m k k' v).symm)

/-- Singleton lookup for equal keys.
    Corresponds to Rocq's `get?_singleton_same`. -/
theorem get?_singleton_same (k : K) (v : V) :
    get? ({[k := v]} : M V) k = some v := by
  simp [FiniteMap.singleton, get?_insert_same]

/-- Singleton lookup for different keys.
    Corresponds to Rocq's `get?_singleton_ne`. -/
theorem get?_singleton_ne (k k' : K) (v : V) (h : k ≠ k') :
    get? ({[k := v]} : M V) k' = none := by
  simp [FiniteMap.singleton, get?_insert_ne _ _ _ _ h, get?_empty]

/-- Singleton lookup general case.
    Corresponds to Rocq's `get?_singleton`. -/
theorem get?_singleton (k k' : K) (v : V) :
    get? ({[k := v]} : M V) k' = if k = k' then some v else none := by
  split
  · next h => rw [h, get?_singleton_same]
  · next h => exact get?_singleton_ne k k' v h

/-- Insert is idempotent for the same key-value.
    Corresponds to Rocq's `insert_insert_eq`. -/
theorem insert_insert (m : M V) (k : K) (v v' : V) :
    get? (insert (insert m k v) k v') = get? (insert m k v' : M V) := by
  funext k'
  by_cases h : k = k'
  · simp [h, get?_insert_same]
  · simp [get?_insert_ne _ _ _ _ h]

/-- Deleting from empty is empty.
    Corresponds to Rocq's `delete_empty_eq`. -/
theorem delete_empty_eq (k : K) :
    get? (delete (∅ : M V) k) = get? (∅ : M V) := by
  funext k'
  by_cases h : k = k'
  · simp [h, get?_delete_same, get?_empty]
  · simp [get?_delete_ne _ _ _ h, get?_empty]

/-- Corresponds to Rocq's `map_empty_subseteq`. -/
theorem empty_subset (m : M V) : (∅ : M V) ⊆ m := by
  intro k v h
  simp [get?_empty] at h

/-- Corresponds to Rocq's `map_disjoint_empty_l`. -/
theorem disjoint_empty_left (m : M V) : (∅ : M V) ##ₘ m := by
  intro k ⟨h₁, _⟩
  simp [get?_empty] at h₁

/-- Corresponds to Rocq's `lookup_insert_Some`. -/
theorem get?_insert_some (m : M V) (i j : K) (x y : V) :
    get? (insert m i x) j = some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ get? m j = some y) := by
  rw [get?_insert]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_insert_is_Some`. -/
theorem get?_insert_isSome (m : M V) (i j : K) (x : V) :
    (get? (insert m i x) j).isSome ↔ i = j ∨ (i ≠ j ∧ (get? m j).isSome) := by
  rw [get?_insert]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_insert_None`. -/
theorem get?_insert_none (m : M V) (i j : K) (x : V) :
    get? (insert m i x) j = none ↔ get? m j = none ∧ i ≠ j := by
  rw [get?_insert]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_insert_rev`. -/
theorem get?_insert_rev (m : M V) (i : K) (x y : V) :
    get? (insert m i x) i = some y → x = y := by
  simp [get?_insert_same]

/-- Corresponds to Rocq's `insert_id`. -/
theorem insert_get? (m : M V) (i : K) (x : V) :
    get? m i = some x → (∀ k, get? (insert m i x) k = get? m k) := by
  intro h k
  by_cases hk : i = k
  · subst hk; simp only [get?_insert_same, h]
  · simp [get?_insert_ne _ _ _ _ hk]

/-- Corresponds to Rocq's `lookup_delete_Some`. -/
theorem get?_delete_some (m : M V) (i j : K) (y : V) :
    get? (delete m i) j = some y ↔ i ≠ j ∧ get? m j = some y := by
  rw [get?_delete]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_delete_is_Some`. -/
theorem get?_delete_isSome (m : M V) (i j : K) :
    (get? (delete m i) j).isSome ↔ i ≠ j ∧ (get? m j).isSome := by
  rw [get?_delete]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_delete_None`. -/
theorem get?_delete_none (m : M V) (i j : K) :
    get? (delete m i) j = none ↔ i = j ∨ get? m j = none := by
  rw [get?_delete]
  split <;> simp_all

/-- Corresponds to Rocq's `insert_delete_id`. -/
theorem insert_delete_cancel (m : M V) (i : K) (x : V) :
    get? m i = some x → insert (delete m i) i x = m := by
  intro h
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_insert_same, h]
  · simp [get?_insert_ne _ _ _ _ hij, get?_delete_ne _ _ _ hij]

  /-- Corresponds to Rocq's `map_to_list_empty`. -/
theorem toList_empty : toList (∅ : M V) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ⟨i, x⟩ hmem
  rw [mem_toList] at hmem
  rw [get?_empty] at hmem
  exact Option.noConfusion hmem

  /-- Corresponds to Rocq's `map_to_list_insert`. -/
theorem toList_insert [DecidableEq V] : ∀ (m : M V) k v, get? m k = none →
    (toList (insert m k v)).Perm ((k, v) :: toList m) := by
  intro m k v hk_none
  apply ofList_injective (M := M) (K := K)
  · exact nodup_toList_keys (insert m k v)
  · rw [List.map_cons, List.nodup_cons]
    constructor
    · intro hk_in
      rw [List.mem_map] at hk_in
      obtain ⟨⟨k', v'⟩, hmem, hk_eq⟩ := hk_in
      simp at hk_eq
      subst hk_eq
      have : get? m k' = some v' := (mem_toList m k' v').mp hmem
      rw [hk_none] at this
      exact Option.noConfusion this
    · exact nodup_toList_keys m
  · rw [ofList_toList]
    rw [ofList_cons, ofList_toList]

/-- Corresponds to Rocq's `map_to_list_delete`. -/
theorem toList_delete [DecidableEq V] (m : M V) (k : K) (v : V) (h : get? m k = some v) :
    (toList m).Perm ((k, v) :: toList (delete m k)) := by
  have heq : toList m = toList (insert (delete m k) k v) := by
    rw [insert_delete_cancel m k v h]
  rw [heq]
  apply toList_insert
  exact get?_delete_same m k


/-- Corresponds to Rocq's `delete_insert_id`. -/
theorem delete_insert_cancel (m : M V) (i : K) (x : V) :
    get? m i = none → delete (insert m i x) i = m := by
  intro h
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_delete_same, h]
  · simp [get?_delete_ne _ _ _ hij, get?_insert_ne _ _ _ _ hij]

/-- Empty map is characterized by all lookups returning none. -/
theorem eq_empty_iff (m : M V) : m = ∅ ↔ ∀ k, get? m k = none := by
  constructor
  · intro h k
    rw [h, get?_empty]
  · intro h
    apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
    intro k
    rw [h, get?_empty]

/-- Corresponds to Rocq's `delete_delete_eq`. -/
theorem delete_delete_same (m : M V) (i : K) :
    delete (delete m i) i = delete m i := by
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_delete_same]
  · simp [get?_delete_ne _ _ _ hij]

/-- Corresponds to Rocq's `delete_delete`. -/
theorem delete_delete_comm (m : M V) (i j : K) :
    delete (delete m i) j = delete (delete m j) i := by
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k <;> simp [get?_delete, *]

/-- Corresponds to Rocq's `delete_insert_ne`. -/
theorem delete_insert_of_ne (m : M V) (i j : K) (x : V) :
    i ≠ j → delete (insert m i x) j = insert (delete m j) i x := by
  intro hij
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk; exact absurd rfl hij
  · subst hik; simp [get?_insert, get?_delete, hjk]
  · subst hjk; simp [get?_insert, get?_delete, hik]
  · simp [get?_insert, get?_delete, hik, hjk]

/-- Corresponds to Rocq's `insert_delete_eq`. -/
theorem insert_delete (m : M V) (i : K) (x : V) :
    insert (delete m i) i x = insert m i x := by
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_insert_same]
  · simp [get?_insert_ne _ _ _ _ hij, get?_delete_ne _ _ _ hij]

/-- Corresponds to Rocq's `insert_insert`. -/
theorem insert_insert_comm (m : M V) (i j : K) (x y : V) :
    i ≠ j → insert (insert m i x) j y = insert (insert m j y) i x := by
  intro hij
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk; exact absurd rfl hij
  · subst hik; simp [get?_insert, hjk]
  · subst hjk; simp [get?_insert, hik]
  · simp [get?_insert, hik, hjk]

/-- Corresponds to Rocq's `insert_insert_eq`. -/
theorem insert_insert_same (m : M V) (i : K) (x y : V) :
    insert (insert m i x) i y = insert m i y := by
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_insert_same]
  · simp [get?_insert_ne _ _ _ _ hij]

/-- Corresponds to Rocq's `delete_empty`. -/
theorem delete_empty_eq' (i : K) :
    delete (∅ : M V) i = ∅ := by
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  simp [get?_delete, get?_empty]

/-- Corresponds to Rocq's `delete_id`. -/
theorem delete_of_get? (m : M V) (i : K) :
    get? m i = none → delete m i = m := by
  intro h
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_delete_same, h]
  · simp [get?_delete_ne _ _ _ hij]

/-- Corresponds to Rocq's `insert_id`. -/
theorem insert_get?' (m : M V) (i : K) (x : V) :
    get? m i = some x → insert m i x = m := by
  intro h
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_insert_same, h]
  · simp [get?_insert_ne _ _ _ _ hij]

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to Rocq's `insert_empty`. -/
theorem insert_empty (i : K) (x : V) :
    insert (∅ : M V) i x = {[i := x]} := by
  rfl

/-- Corresponds to Rocq's `insert_non_empty`. -/
theorem insert_ne_empty (m : M V) (i : K) (x : V) :
    insert m i x ≠ ∅ := by
  intro h
  have := eq_empty_iff (insert m i x) |>.mp h i
  simp [get?_insert_same] at this

/-- Corresponds to Rocq's `delete_subseteq`. -/
theorem delete_subset_self (m : M V) (i : K) : delete m i ⊆ m := by
  intro k v h
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at h
  · simp [get?_delete_ne _ _ _ hik] at h
    exact h

/-- Corresponds to Rocq's `delete_subset`. -/
theorem delete_subset_of_mem (m : M V) (i : K) (v : V) :
    get? m i = some v → delete m i ⊆ m ∧ delete m i ≠ m := by
  intro hi
  constructor
  · exact delete_subset_self m i
  · intro heq
    have : get? (delete m i) i = get? m i := by rw [heq]
    simp [get?_delete_same, hi] at this

/-- Corresponds to Rocq's `insert_subseteq`. -/
theorem subset_insert (m : M V) (i : K) (x : V) :
    get? m i = none → m ⊆ insert m i x := by
  intro hi k v hk
  by_cases hik : i = k
  · subst hik
    simp [hi] at hk
  · simp [get?_insert_ne _ _ _ _ hik, hk]

/-- Corresponds to Rocq's `insert_subset`. -/
theorem subset_insert_of_not_mem (m : M V) (i : K) (x : V) :
    get? m i = none → m ⊆ insert m i x ∧ m ≠ insert m i x := by
  intro hi
  constructor
  · exact subset_insert m i x hi
  · intro heq
    have h2 : get? (insert m i x) i = some x := get?_insert_same m i x
    rw [← heq] at h2
    rw [hi] at h2
    exact Option.noConfusion h2

/-- Corresponds to Rocq's `delete_mono`. -/
theorem delete_subset_delete (m₁ m₂ : M V) (i : K) :
    m₁ ⊆ m₂ → delete m₁ i ⊆ delete m₂ i := by
  intro hsub k v hk
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at hk
  · simp [get?_delete_ne _ _ _ hik] at hk ⊢
    exact hsub k v hk

/-- Corresponds to Rocq's `insert_mono`. -/
theorem insert_subset_insert (m₁ m₂ : M V) (i : K) (x : V) :
    m₁ ⊆ m₂ → insert m₁ i x ⊆ insert m₂ i x := by
  intro hsub k v hk
  by_cases hik : i = k
  · subst hik
    simp [get?_insert_same] at hk ⊢
    exact hk
  · simp [get?_insert_ne _ _ _ _ hik] at hk ⊢
    exact hsub k v hk

/-- Corresponds to Rocq's `map_non_empty_singleton`. -/
theorem singleton_ne_empty (i : K) (x : V) :
    {[i := x]} ≠ (∅ : M V) := by
  exact insert_ne_empty ∅ i x

/-- Corresponds to Rocq's `delete_singleton_eq`. -/
theorem delete_singleton_same (i : K) (x : V) :
    delete ({[i := x]} : M V) i = ∅ := by
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  simp [FiniteMap.singleton, get?_delete, get?_insert, get?_empty]

/-- Corresponds to Rocq's `delete_singleton_ne`. -/
theorem delete_singleton_of_ne (i j : K) (x : V) :
    i ≠ j → delete ({[j := x]} : M V) i = {[j := x]} := by
  intro hij
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  simp [FiniteMap.singleton, get?_delete, get?_insert, get?_empty]
  intro hik
  intro hjk
  subst hik hjk
  exact hij rfl

/-- Corresponds to Rocq's `map_Forall_to_list`. -/
theorem forall_iff_toList (P : K → V → Prop) (m : M V) :
    FiniteMap.Forall P m ↔ ∀ kv ∈ toList m, P kv.1 kv.2 := by
  constructor
  · intro hfa kv hmem
    have := (mem_toList m kv.1 kv.2).mp hmem
    exact hfa kv.1 kv.2 this
  · intro hlist k v hget
    have := (mem_toList m k v).mpr hget
    exact hlist (k, v) this

/-- Corresponds to Rocq's `map_Forall_empty`. -/
theorem forall_empty (P : K → V → Prop) : FiniteMap.Forall P (∅ : M V) := by
  intro k v h
  simp [get?_empty] at h

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to Rocq's `map_Forall_impl`. -/
theorem forall_mono (P Q : K → V → Prop) (m : M V) :
    FiniteMap.Forall P m → (∀ k v, P k v → Q k v) → FiniteMap.Forall Q m := by
  intro hp himpl k v hget
  exact himpl k v (hp k v hget)

/-- Corresponds to Rocq's `map_Forall_insert_1_1`. -/
theorem forall_insert_of_forall (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    FiniteMap.Forall P (insert m i x) → P i x := by
  intro hfa
  exact hfa i x (get?_insert_same m i x)

/-- Corresponds to Rocq's `map_Forall_insert_1_2`. -/
theorem forall_of_forall_insert (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    get? m i = none → FiniteMap.Forall P (insert m i x) → FiniteMap.Forall P m := by
  intro hi hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [hi] at hget
  · have : get? (insert m i x) k = some v := by
      simp [get?_insert_ne _ _ _ _ hik, hget]
    exact hfa k v this

/-- Corresponds to Rocq's `map_Forall_insert_2`. -/
theorem forall_insert (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    P i x → FiniteMap.Forall P m → FiniteMap.Forall P (insert m i x) := by
  intro hpix hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [get?_insert_same] at hget
    rw [← hget]
    exact hpix
  · simp [get?_insert_ne _ _ _ _ hik] at hget
    exact hfa k v hget

/-- Corresponds to Rocq's `map_Forall_insert`. -/
theorem forall_insert_iff (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    get? m i = none → (FiniteMap.Forall P (insert m i x) ↔ P i x ∧ FiniteMap.Forall P m) := by
  intro hi
  constructor
  · intro hfa
    exact ⟨forall_insert_of_forall P m i x hfa, forall_of_forall_insert P m i x hi hfa⟩
  · intro ⟨hpix, hfa⟩
    exact forall_insert P m i x hpix hfa

/-- Corresponds to Rocq's `map_Forall_singleton`. -/
theorem forall_singleton (P : K → V → Prop) (i : K) (x : V) :
    FiniteMap.Forall P ({[i := x]} : M V) ↔ P i x := by
  constructor
  · intro hfa
    exact hfa i x (get?_singleton_same i x)
  · intro hpix k v hget
    simp [get?_singleton] at hget
    obtain ⟨rfl, rfl⟩ := hget
    exact hpix

/-- Corresponds to Rocq's `map_Forall_delete`. -/
theorem forall_delete (P : K → V → Prop) (m : M V) (i : K) :
    FiniteMap.Forall P m → FiniteMap.Forall P (delete m i) := by
  intro hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at hget
  · simp [get?_delete_ne _ _ _ hik] at hget
    exact hfa k v hget

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to Rocq's `map_disjoint_spec`. -/
theorem disjoint_iff (m₁ m₂ : M V) :
    m₁ ##ₘ m₂ ↔ ∀ k, get? m₁ k = none ∨ get? m₂ k = none := by
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

/-- Corresponds to Rocq's `map_disjoint_insert_l`. -/
theorem disjoint_insert_left (m₁ m₂ : M V) (i : K) (x : V) :
    get? m₂ i = none →
    m₁ ##ₘ m₂ →
    insert m₁ i x ##ₘ m₂ := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [get?_insert_ne _ _ _ _ hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

/-- Corresponds to Rocq's `map_disjoint_insert_r`. -/
theorem disjoint_insert_right (m₁ m₂ : M V) (i : K) (x : V) :
    get? m₁ i = none →
    m₁ ##ₘ m₂ →
    m₁ ##ₘ insert m₂ i x := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [get?_insert_ne _ _ _ _ hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

/-- Corresponds to Rocq's `map_disjoint_delete_l`. -/
theorem disjoint_delete_left (m₁ m₂ : M V) (i : K) :
    m₁ ##ₘ m₂ → delete m₁ i ##ₘ m₂ := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at hs1
  · simp [get?_delete_ne _ _ _ hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

/-- Corresponds to Rocq's `map_disjoint_delete_r`. -/
theorem disjoint_delete_right (m₁ m₂ : M V) (i : K) :
    m₁ ##ₘ m₂ → m₁ ##ₘ delete m₂ i := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at hs2
  · simp [get?_delete_ne _ _ _ hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

/-- Corresponds to Rocq's `map_disjoint_singleton_l`. -/
theorem disjoint_singleton_left (m : M V) (i : K) (x : V) :
    get? m i = none → {[i := x]} ##ₘ m := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [FiniteMap.singleton, get?_insert_ne _ _ _ _ hik, get?_empty] at hs1

/-- Corresponds to Rocq's `map_disjoint_singleton_r`. -/
theorem disjoint_singleton_right (m : M V) (i : K) (x : V) :
    get? m i = none → m ##ₘ {[i := x]} := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [FiniteMap.singleton, get?_insert_ne _ _ _ _ hik, get?_empty] at hs2

/-- toList of map (fmap) is a permutation of mapping over toList. -/
theorem toList_map [DecidableEq V'] : ∀ (m : M V) (f : V → V'),
  (toList (FiniteMap.map f m)).Perm
      ((toList m).map (fun kv => (kv.1, f kv.2))) := by
  intro m f
  simp only [FiniteMap.map]
  apply toList_ofList
  simp only [List.map_map]
  show ((toList m).map (fun x => x.1)).Nodup
  exact nodup_toList_keys m

/-- Lookup in a mapped map. -/
theorem get?_map [DecidableEq V] {V' : Type _} [DecidableEq V'] (f : V → V') (m : M V) (k : K) :
    get? (FiniteMap.map f m) k = (get? m k).map f := by
  simp only [FiniteMap.map]
  by_cases h : ∃ v, get? m k = some v
  · obtain ⟨v, hv⟩ := h
    have hmem : (k, v) ∈ toList m := (mem_toList m k v).mpr hv
    have hmem' : (k, f v) ∈ (toList m).map (fun (ki, vi) => (ki, f vi)) := by
      rw [List.mem_map]
      exact ⟨(k, v), hmem, rfl⟩
    have hnodup : ((toList m).map (fun (ki, vi) => (ki, f vi))).map Prod.fst |>.Nodup := by
      simp only [List.map_map]
      show ((toList m).map Prod.fst).Nodup
      exact nodup_toList_keys m
    have := (mem_ofList (M := M) _ k (f v) hnodup).mp hmem'
    simp [hv, this]
  · have hk : get? m k = none := by
      cases hm : get? m k
      · rfl
      · exfalso; apply h; exact ⟨_, hm⟩
    simp [hk]
    cases h' : get? (ofList ((toList m).map (fun (ki, vi) => (ki, f vi))) : M V') k
    · rfl
    · rename_i v'
      have hnodup : ((toList m).map (fun (ki, vi) => (ki, f vi))).map Prod.fst |>.Nodup := by
        simp only [List.map_map]
        show ((toList m).map Prod.fst).Nodup
        exact nodup_toList_keys m
      have hmem : (k, v') ∈ (toList m).map (fun (ki, vi) => (ki, f vi)) :=
        (mem_ofList (M := M) (V := V') _ k v' hnodup).mpr h'
      rw [List.mem_map] at hmem
      obtain ⟨⟨k', v''⟩, hmem', heq⟩ := hmem
      simp at heq
      cases heq
      rename_i heq_k heq_v
      have : get? m k' = some v'' := (mem_toList m k' v'').mp hmem'
      rw [heq_k, hk] at this
      cases this

omit [DecidableEq K] in
/-- filterMap preserves Nodup on keys. -/
private theorem nodup_map_fst_filterMap
    (l : List (K × V)) (g : K → V → Option (K × V')) :
    (l.map Prod.fst).Nodup →
    (∀ ki vi k' v', g ki vi = some (k', v') → k' = ki) →
    ((l.filterMap (fun (ki, vi) => g ki vi)).map Prod.fst).Nodup := by
  intro h_nodup h_preserve_key
  have aux : ∀ (k_target : K) (l' : List (K × V)),
      k_target ∈ (l'.filterMap (fun (ki, vi) => g ki vi)).map Prod.fst →
      k_target ∈ l'.map Prod.fst := by
    intro k_target l'
    induction l' with
    | nil => simp
    | cons kv' tail' ih_aux =>
      obtain ⟨k'', v''⟩ := kv'
      intro hmem_filter
      simp only [List.filterMap] at hmem_filter
      cases hg' : g k'' v'' with
      | none =>
        simp only [hg'] at hmem_filter
        exact List.mem_cons_of_mem k'' (ih_aux hmem_filter)
      | some res' =>
        obtain ⟨k''', v'''⟩ := res'
        have : k''' = k'' := h_preserve_key k'' v'' k''' v''' hg'
        subst this
        simp only [hg', List.map_cons, List.mem_cons] at hmem_filter
        rw [List.map_cons, List.mem_cons]
        cases hmem_filter with
        | inl heq => left; exact heq
        | inr hmem' => right; exact ih_aux hmem'
  induction l with
  | nil => simp
  | cons kv tail ih =>
    obtain ⟨k, v⟩ := kv
    rw [List.map_cons, List.nodup_cons] at h_nodup
    simp only [List.filterMap]
    cases hg : g k v with
    | none =>
      exact ih h_nodup.2
    | some res =>
      obtain ⟨k', v'⟩ := res
      have hk_eq : k' = k := h_preserve_key k v k' v' hg
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [hk_eq] at hmem
        apply h_nodup.1
        exact aux k tail hmem
      · exact ih h_nodup.2

/-- Lookup in zipWith. -/
theorem get?_zipWith [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') (k : K) :
    get? (FiniteMap.zipWith f m1 m2) k =
      match get? m1 k, get? m2 k with
      | some v1, some v2 => some (f v1 v2)
      | _, _ => none := by
  simp only [FiniteMap.zipWith]
  cases h1 : get? m1 k
  · simp
    cases h' : get? (ofList ((toList m1).filterMap (fun (ki, vi) =>
        match get? m2 ki with
        | some v' => some (ki, f vi v')
        | none => none)) : M V'') k
    · rfl
    · rename_i v_result
      have hnodup : ((toList m1).filterMap (fun (ki, vi) =>
          match get? m2 ki with
          | some v' => some (ki, f vi v')
          | none => none)).map Prod.fst |>.Nodup := by
        refine nodup_map_fst_filterMap (V' := V'') (toList m1) (fun ki vi =>
            match get? m2 ki with
            | some v' => some (ki, f vi v')
            | none => none) (nodup_toList_keys m1) ?_
        intros ki vi k' v' heq
        cases heq' : get? m2 ki <;> simp [heq'] at heq
        obtain ⟨rfl, _⟩ := heq
        rfl
      have hmem : (k, v_result) ∈ (toList m1).filterMap (fun (ki, vi) =>
          match get? m2 ki with
          | some v' => some (ki, f vi v')
          | none => none) :=
        (mem_ofList (M := M) (V := V'') _ k v_result hnodup).mpr h'
      rw [List.mem_filterMap] at hmem
      obtain ⟨⟨k', v1'⟩, hmem1, hmatch⟩ := hmem
      simp at hmatch
      cases hm2 : get? m2 k' <;> simp [hm2] at hmatch
      · obtain ⟨heq_k, _⟩ := hmatch
        have : get? m1 k' = some v1' := (mem_toList m1 k' v1').mp hmem1
        rw [heq_k, h1] at this
        cases this
  · rename_i v1
    cases h2 : get? m2 k
    · simp
      cases h' : get? (ofList ((toList m1).filterMap (fun (ki, vi) =>
          match get? m2 ki with
          | some v' => some (ki, f vi v')
          | none => none)) : M V'') k
      · rfl
      · rename_i v_result
        have hnodup : ((toList m1).filterMap (fun (ki, vi) =>
            match get? m2 ki with
            | some v' => some (ki, f vi v')
            | none => none)).map Prod.fst |>.Nodup := by
          refine nodup_map_fst_filterMap (V' := V'') (toList m1) (fun ki vi =>
              match get? m2 ki with
              | some v' => some (ki, f vi v')
              | none => none) (nodup_toList_keys m1) ?_
          intros ki vi k' v' heq
          cases heq' : get? m2 ki <;> simp [heq'] at heq
          obtain ⟨rfl, _⟩ := heq
          rfl
        have hmem : (k, v_result) ∈ (toList m1).filterMap (fun (ki, vi) =>
            match get? m2 ki with
            | some v' => some (ki, f vi v')
            | none => none) :=
          (mem_ofList (M := M) (V := V'') _ k v_result hnodup).mpr h'
        rw [List.mem_filterMap] at hmem
        obtain ⟨⟨k', v1'⟩, hmem1, hmatch⟩ := hmem
        simp at hmatch
        cases hm2 : get? m2 k' <;> simp [hm2] at hmatch
        · obtain ⟨heq_k, _⟩ := hmatch
          rw [heq_k, h2] at hm2
          cases hm2
    · rename_i v2
      simp
      have hmem1 : (k, v1) ∈ toList m1 := (mem_toList m1 k v1).mpr h1
      have hmem_filter : (k, f v1 v2) ∈ (toList m1).filterMap (fun (ki, vi) =>
          match get? m2 ki with
          | some v' => some (ki, f vi v')
          | none => none) := by
        rw [List.mem_filterMap]
        refine ⟨(k, v1), hmem1, ?_⟩
        simp [h2]
      have hnodup : ((toList m1).filterMap (fun (ki, vi) =>
          match get? m2 ki with
          | some v' => some (ki, f vi v')
          | none => none)).map Prod.fst |>.Nodup := by
        refine nodup_map_fst_filterMap (V' := V'') (toList m1) (fun ki vi =>
            match get? m2 ki with
            | some v' => some (ki, f vi v')
            | none => none) (nodup_toList_keys m1) ?_
        intros ki vi k' v' heq
        cases heq' : get? m2 ki <;> simp [heq'] at heq
        obtain ⟨rfl, _⟩ := heq
        rfl
      exact (mem_ofList (M := M) _ k (f v1 v2) hnodup).mp hmem_filter

/-- Corresponds to Rocq's `map_fmap_zip_with_r`. -/
theorem map_zipWith_right [DecidableEq V] {V' V'' : Type _} [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (g1 : V'' → V) (m1 : M V) (m2 : M V')
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    FiniteMap.map g1 (FiniteMap.zipWith f m1 m2) = m1 := by
  apply ext
  intro k
  rw [get?_map, get?_zipWith]
  cases h1 : get? m1 k with
  | none => simp
  | some x =>
    have h2 : (get? m2 k).isSome = true := (hdom k).mp (by simp [h1])
    cases h2' : get? m2 k with
    | none => simp [h2'] at h2
    | some y =>
      simp [hg1]

/-- Corresponds to Rocq's `map_fmap_zip_with_l`. -/
theorem map_zipWith_left [DecidableEq V] [DecidableEq V'] {V'' : Type _} [DecidableEq V'']
    (f : V → V' → V'') (g2 : V'' → V') (m1 : M V) (m2 : M V')
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    FiniteMap.map g2 (FiniteMap.zipWith f m1 m2) = m2 := by
  apply ext
  intro k
  rw [get?_map, get?_zipWith]
  cases h2 : get? m2 k with
  | none => simp
  | some y =>
    have h1 : (get? m1 k).isSome = true := (hdom k).mpr (by simp [h2])
    cases h1' : get? m1 k with
    | none => simp [h1'] at h1
    | some x =>
      simp [hg2]

/-- Insert distributes over zipWith. -/
theorem zipWith_insert [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') (i : K) (x : V) (y : V') :
    FiniteMap.zipWith f (insert m1 i x) (insert m2 i y) =
    insert (FiniteMap.zipWith f m1 m2) i (f x y) := by
  apply ext
  intro k
  by_cases h : k = i
  · subst h
    simp only [get?_insert_same, get?_zipWith]
  · have h' : i ≠ k := Ne.symm h
    simp only [get?_zipWith, get?_insert_ne _ i k _ h']

/-- Corresponds to Rocq's `map_delete_zip_with`. -/
theorem zipWith_delete [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') (i : K) :
    FiniteMap.zipWith f (delete m1 i) (delete m2 i) =
    delete (FiniteMap.zipWith f m1 m2) i := by
  apply ext
  intro k
  by_cases h : k = i
  · subst h
    simp only [get?_delete_same, get?_zipWith]
  · have h' : i ≠ k := Ne.symm h
    simp only [get?_zipWith, get?_delete_ne _ i k h']

theorem zipWith_comm [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') :
    FiniteMap.zipWith (fun x y => f y x) m2 m1 = FiniteMap.zipWith f m1 m2 := by
  apply ext
  intro k
  rw [get?_zipWith, get?_zipWith]
  cases get? m1 k <;> cases get? m2 k <;> simp

/-- Corresponds to Rocq's `map_zip_with_flip`. -/
theorem zip_comm [DecidableEq V] [DecidableEq V']
    (m1 : M V) (m2 : M V') :
    FiniteMap.zip m2 m1 = FiniteMap.map Prod.swap (FiniteMap.zip m1 m2) := by
  apply ext
  intro k
  unfold FiniteMap.zip
  rw [get?_map, get?_zipWith, get?_zipWith]
  cases get? m1 k <;> cases get? m2 k <;> simp [Prod.swap]

/-- Mapping with id is identity.
    Corresponds to Rocq's `map_id`. -/
theorem map_id [DecidableEq V] (m : M V) :
    FiniteMap.map id m = m := by
  apply ext
  intro k
  rw [get?_map]
  cases get? m k <;> simp

/-- Mapping over a zip is the same as zipping the mapped maps.
    Corresponds to Rocq's `map_fmap_zip`. -/
theorem zip_map [DecidableEq V] [DecidableEq V'] {V'' V''' : Type _} [DecidableEq V''] [DecidableEq V''']
    (f : V → V'') (g : V' → V''') (m1 : M V) (m2 : M V') :
    FiniteMap.zip (FiniteMap.map f m1) (FiniteMap.map g m2) =
    FiniteMap.map (fun (x, y) => (f x, g y)) (FiniteMap.zip m1 m2) := by
  apply ext
  intro k
  unfold FiniteMap.zip
  rw [get?_zipWith, get?_map, get?_map, get?_map, get?_zipWith]
  cases h1 : get? m1 k <;> cases h2 : get? m2 k <;> simp

/-- Zipping fst and snd projections of a map recovers the original map.
    Corresponds to Rocq's `map_zip_fst_snd`. -/
theorem zip_fst_snd {V' : Type u'} [DecidableEq V] [DecidableEq V'] (m : M (V × V')) :
    FiniteMap.zip (FiniteMap.map Prod.fst m) (FiniteMap.map Prod.snd m) = m := by
  apply ext
  intro k
  unfold FiniteMap.zip
  rw [get?_zipWith, get?_map, get?_map]
  cases h : get? m k with
  | none => simp
  | some p => cases p with | mk v1 v2 => simp

/-- Corresponds to part of Rocq's dom lemmas for zip. -/
theorem isSome_zipWith [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') (k : K) :
    (get? (FiniteMap.zipWith f m1 m2) k).isSome ↔
    (get? m1 k).isSome ∧ (get? m2 k).isSome := by
  rw [get?_zipWith]
  cases get? m1 k <;> cases get? m2 k <;> simp [Option.isSome_some, Option.isSome_none]

/-- Zipping two empty maps yields an empty map.
    Corresponds to Rocq's `map_zip_empty`. -/
theorem zip_empty [DecidableEq V] [DecidableEq V'] :
    FiniteMap.zip (∅ : M V) (∅ : M V') = ∅ := by
  apply ext
  intro k
  unfold FiniteMap.zip
  rw [get?_zipWith, get?_empty, get?_empty, get?_empty]

/-- Lookup in a zipped map.
    Corresponds to Rocq's `lookup_zip_with` specialized to `zip`. -/
theorem get?_zip [DecidableEq V] [DecidableEq V'] (m1 : M V) (m2 : M V') (k : K) :
    get? (FiniteMap.zip m1 m2) k =
      match get? m1 k, get? m2 k with
      | some v1, some v2 => some (v1, v2)
      | _, _ => none := by
  unfold FiniteMap.zip
  rw [get?_zipWith]

/-- Insert distributes over zip.
    Corresponds to Rocq's `map_zip_insert`. -/
theorem zip_insert [DecidableEq V] [DecidableEq V']
    (m1 : M V) (m2 : M V') (i : K) (x : V) (y : V') :
    get? m1 i = none → get? m2 i = none →
    FiniteMap.zip (insert m1 i x) (insert m2 i y) =
    insert (FiniteMap.zip m1 m2) i (x, y) := by
  intro h1 h2
  unfold FiniteMap.zip
  exact zipWith_insert Prod.mk m1 m2 i x y

/-- Delete distributes over zip.
    Corresponds to Rocq's `map_zip_delete`. -/
theorem zip_delete [DecidableEq V] [DecidableEq V']
    (m1 : M V) (m2 : M V') (i : K) :
    FiniteMap.zip (delete m1 i) (delete m2 i) =
    delete (FiniteMap.zip m1 m2) i := by
  unfold FiniteMap.zip
  exact zipWith_delete Prod.mk m1 m2 i

/-- Domain of a zipped map.
    Corresponds to part of Rocq's `elem_of_dom_2` for zip. -/
theorem isSome_zip [DecidableEq V] [DecidableEq V'] (m1 : M V) (m2 : M V') (k : K) :
    (get? (FiniteMap.zip m1 m2) k).isSome ↔
    (get? m1 k).isSome ∧ (get? m2 k).isSome := by
  unfold FiniteMap.zip
  exact isSome_zipWith Prod.mk m1 m2 k

/-- toList of a zipped map.
    Corresponds to Rocq's `map_to_list_zip`. -/
theorem toList_zip [DecidableEq V] [DecidableEq V'] (m1 : M V) (m2 : M V') :
    (toList (FiniteMap.zip m1 m2)).Perm
      ((toList m1).filterMap (fun (k, v1) =>
        match get? m2 k with
        | some v2 => some (k, (v1, v2))
        | none => none)) := by
  unfold FiniteMap.zip
  simp only [FiniteMap.zipWith]
  apply toList_ofList
  refine nodup_map_fst_filterMap (V' := V × V') (toList m1)
    (fun ki vi => match get? m2 ki with | some v' => some (ki, (vi, v')) | none => none)
    (nodup_toList_keys m1) ?_
  intro ki vi k' vp heq
  cases heq' : get? m2 ki <;> simp [heq'] at heq
  obtain ⟨rfl, _⟩ := heq
  rfl

/-- Corresponds to Rocq's `lookup_union_None`. -/
theorem get?_union_none (m1 m2 : M V) (i : K) :
    get? (m1 ∪ m2) i = none ↔ get? m1 i = none ∧ get? m2 i = none := by
  rw [get?_union]
  cases h1 : get? m1 i <;> cases h2 : get? m2 i <;> simp [Option.orElse]

/-- Corresponds to Rocq's `insert_union_l`. -/
theorem union_insert_left (m1 m2 : M V) (i : K) (x : V) :
    get? (insert (m1 ∪ m2) i x) = get? (insert m1 i x ∪ m2) := by
  funext k
  by_cases hik : i = k
  · subst hik
    simp [get?_insert_same, get?_union]
  · simp [get?_insert_ne _ _ _ _ hik, get?_union]

end FiniteMapLaws

namespace FiniteMap

variable {K : Type v} {M : Type u → _}  [FiniteMap K M]

/-- Submap is reflexive. -/
theorem subset_refl (m : M V) : m ⊆ m := fun _ _ h => h

/-- Submap is transitive. -/
theorem subset_trans {m₁ m₂ m₃ : M V} (h₁ : m₁ ⊆ m₂) (h₂ : m₂ ⊆ m₃) : m₁ ⊆ m₃ :=
  fun k v hm₁ => h₂ k v (h₁ k v hm₁)

/-- Disjointness is symmetric. -/
theorem disjoint_comm {m₁ m₂ : M V} (h : disjoint m₁ m₂) : disjoint m₂ m₁ :=
  fun k ⟨h₂, h₁⟩ => h k ⟨h₁, h₂⟩

theorem disjoint_empty_right [DecidableEq K] [FiniteMapLaws K M] (m : M V) : m ##ₘ (∅ : M V) :=
  disjoint_comm (FiniteMapLaws.disjoint_empty_left (K:= K) m)

/-- `m₂` and `m₁ \ m₂` are disjoint. -/
theorem disjoint_difference_right [DecidableEq K] [FiniteMapLaws K M] [FiniteMapLawsSelf K M]
    (m₁ m₂ : M V) : m₂ ##ₘ (m₁ \ m₂) := by
  intro k ⟨h_in_m2, h_in_diff⟩
  rw [FiniteMapLaws.get?_difference] at h_in_diff
  simp only [h_in_m2, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at h_in_diff

/-- Corresponds to Rocq's `map_difference_union`. -/
theorem union_difference_cancel [DecidableEq K] [FiniteMapLaws K M] [FiniteMapLawsSelf K M]
    (m₁ m₂ : M V) (hsub : m₂ ⊆ m₁) : m₂ ∪ (m₁ \ m₂) = m₁ := by
  apply FiniteMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  rw [FiniteMapLaws.get?_union, FiniteMapLaws.get?_difference]
  cases hm2 : get? m₂ k with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
  | some v =>
    simp only [Option.isSome_some, ↓reduceIte, Option.orElse_some]
    exact (hsub k v hm2).symm

end FiniteMap

end Iris.Std
