/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

import Iris.Std.List

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
class FiniteMap (M : Type u → Type _) (K : outParam (Type v)) where
  /-- Lookup a key in the map, returning `none` if not present.
      Corresponds to Rocq's `lookup` (notation `!!`). -/
  get? : M V → K → Option V
  /-- Insert or update a key-value pair.
      Corresponds to Rocq's `insert` (notation `<[i:=x]>`). -/
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
  fold {A : Type _} : (K → V → A → A) → A → M V → A

export FiniteMap (get? insert delete toList ofList fold)

namespace FiniteMap

variable {M : Type u → Type _} {K : Type v} [FiniteMap M K]  {V : Type _}

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
    Corresponds to Rocq's `map_disjoint` (notation `##ₘ`). -/
def Disjoint (m₁ m₂ : M V) : Prop := ∀ k, ¬((get? m₁ k).isSome ∧ (get? m₂ k).isSome)

/-- Submap relation: `m₁` is a submap of `m₂` if every key-value pair in `m₁` is also in `m₂`.
    Corresponds to Rocq's `map_subseteq` (notation `⊆`).

    Rocq's `map_subseteq_spec` states:
    `m1 ⊆ m2 ↔ ∀ i x, m1 !! i = Some x → m2 !! i = Some x` -/
def Submap (m₁ m₂ : M V) : Prop := ∀ k v, get? m₁ k = some v → get? m₂ k = some v

instance : HasSubset (M V) := ⟨Submap⟩

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
def Mem (m : M V) (k : K) : Prop := (get? m k).isSome

/-- Difference: remove all keys in `m₂` from `m₁`.
    `m₁ ∖ m₂` contains entries `(k, v)` where `k ∈ m₁` but `k ∉ m₂`.
    Corresponds to Rocq's `map_difference` (notation `∖`). -/
def difference (m₁ m₂ : M V) : M V :=
  ofList ((toList m₁).filter (fun (k, _) => (get? m₂ k).isNone))

instance : SDiff (M V) := ⟨difference⟩

/-- Transform keys of a map using an injective function.
    Given `f : K → K'`, `kmap f m` transforms a map with keys of type `K`
    into a map with keys of type `K'`.
    Corresponds to Rocq's `kmap`. -/
def kmap {M' : Type _ → _} {K' : Type v'} [FiniteMap M' K'] (f : K → K') (m : M V) : (M' V) :=
  ofList ((toList m).map (fun (k, v) => (f k, v)))

/-- Convert a list to a map with sequential natural number keys starting from `start`.
    `map_seq start [v₀, v₁, v₂, ...]` creates a map `{start ↦ v₀, start+1 ↦ v₁, start+2 ↦ v₂, ...}`.
    Corresponds to Rocq's `map_seq`. -/
def map_seq [FiniteMap M Nat] (start : Nat) (l : List V) : M V :=
  ofList (l.mapIdx (fun i v => (start + i, v)))

/-- Check if a key is the first key in the map's `toList` representation.
    `firstKey m i` holds if there exists a value `x` such that `(i, x)` is the head of `toList m`.
    Corresponds to Rocq's `map_first_key`: `∃ x, map_to_list m !! 0 = Some (i,x)`. -/
def firstKey (m : M V) (i : K) : Prop :=
  ∃ x, (toList m).head? = some (i, x)

/-- Corresponds to Rocq's `map_Forall`. -/
def map_Forall (P : K → V → Prop) (m : M V) : Prop :=
  ∀ k v, get? m k = some v → P k v

end FiniteMap

/-- Membership instance for finite maps: `k ∈ m` means the key `k` is in the map `m`. -/
instance {M : Type u → Type _} {K : Type v}  [inst : FiniteMap M K] : Membership K (M V) :=
  ⟨fun (m : M V) (k : K) => (inst.get? m k).isSome⟩

/-- Laws that a finite map implementation must satisfy.
    Corresponds to Rocq's `FinMap` class axioms. -/
class FiniteMapLaws (M : Type u → Type _) (K : Type _)
    [DecidableEq K] [FiniteMap M K] where
  /-- Corresponds to Rocq's `map_eq`. -/
  map_eq : ∀ (m₁ m₂ : M V), (∀ i, get? m₁ i = get? m₂ i) → m₁ = m₂
  /-- Corresponds to Rocq's `lookup_empty`. -/
  lookup_empty : ∀ k, get? (∅ : M V) k = none
  /-- Corresponds to Rocq's `lookup_insert_eq`. -/
  lookup_insert_eq : ∀ (m : M V) k v, get? (insert m k v) k = some v
  /-- Corresponds to Rocq's `lookup_insert_ne`. -/
  lookup_insert_ne : ∀ (m : M V) k k' v, k ≠ k' → get? (insert m k v) k' = get? m k'
  /-- Corresponds to Rocq's `lookup_delete_eq`. -/
  lookup_delete_eq : ∀ (m : M V) k, get? (delete m k) k = none
  /-- Corresponds to Rocq's `lookup_delete_ne`. -/
  lookup_delete_ne : ∀ (m : M V) k k', k ≠ k' → get? (delete m k) k' = get? m k'
  /-- Corresponds to Rocq's `lookup_union`. -/
  lookup_union : ∀ (m₁ m₂ : M V) k,
    get? (m₁ ∪ m₂) k = (get? m₁ k).orElse (fun _ => get? m₂ k)
  /-- Corresponds to Rocq's `lookup_difference`. -/
  lookup_difference : ∀ (m₁ m₂ : M V) k,
    get? (m₁ \ m₂) k = if (get? m₂ k).isSome then none else get? m₁ k
  /-- Corresponds to Rocq's implicit behavior of `list_to_map`. -/
  ofList_nil : (ofList [] : M V) = ∅
  /-- Corresponds to Rocq's implicit behavior of `list_to_map`. -/
  ofList_cons : ∀ (k : K) (v : V) (l : List (K × V)),
    (ofList ((k, v) :: l) : M V) = insert (ofList l) k v
  /-- Folding over the empty map returns the initial accumulator.
      Corresponds to Rocq's `map_fold_empty`. -/
  fold_empty : ∀ {A : Type u'} (f : K → V → A → A) (b : A),
    fold f b (∅ : M V) = b
  fold_fmap_ind (P : M V → Prop) :
    P ∅ →
    (∀ i x m,
      get? m i = none →
      (∀ A' B (f : K → A' → B → B) (g : V → A') b x',
        fold f b (insert ((FiniteMap.map g m)) i x') = f i x' (fold f b (FiniteMap.map g m))) →
      P m →
      P (insert m i x)) →
    ∀ m, P m


/-- Self-referential extended laws (for filterMap, filter on the same type). -/
class FiniteMapLawsSelf (M : Type u → _) (K : Type v)
    [DecidableEq K] [FiniteMap M K] [FiniteMapLaws M K] where
  /-- toList of filterMap (omap) is related to filterMap over toList. -/
  toList_filterMap : ∀ (m : M V) (f : V → Option V),
    (toList (FiniteMap.filterMap (M := M) f m)).Perm
      ((toList m).filterMap (fun kv => (f kv.2).map (kv.1, ·)))
  /-- toList of filter is related to filter over toList. -/
  toList_filter : ∀ (m : M V) (φ : K → V → Bool),
    (toList (FiniteMap.filter (M := M) φ m)).Perm
      ((toList m).filter (fun kv => φ kv.1 kv.2))
  /-- toList of union for disjoint maps.
      Corresponds to Rocq's implicit behavior from `map_to_list_union`. -/
  toList_union_disjoint : ∀ (m₁ m₂ : M V),
    FiniteMap.Disjoint m₁ m₂ →
    (toList (m₁ ∪ m₂)).Perm (toList m₁ ++ toList m₂)
  /-- toList of difference is related to filter over toList. -/
  toList_difference : ∀ (m₁ m₂ : M V),
    (toList (m₁ \ m₂)).Perm
      ((toList m₁).filter (fun kv => (get? m₂ kv.1).isNone))

/-- Laws for kmap operation (key transformation). -/
class FiniteMapKmapLaws (M : Type _ → _) (M' : Type _ → _) (K : Type _) (K' : Type _)
    [DecidableEq K] [DecidableEq K'] [FiniteMap M K] [FiniteMap M' K']
    [FiniteMapLaws M K] [FiniteMapLaws M' K'] where
  /-- toList of kmap is related to mapping over toList.
      For an injective function `f : K → K'`, `toList (kmap f m)` is a permutation of
      `(toList m).map (fun (k, v) => (f k, v))`.
      Corresponds to Rocq's `map_to_list_kmap`. -/
  toList_kmap : ∀ (f : K → K') (m : M V),
    (∀ {x y}, f x = f y → x = y) →  -- f is injective
    (toList (FiniteMap.kmap (M' := M') f m)).Perm
      ((toList m).map (fun (k, v) => (f k, v)))

/-- Laws for map_seq operation (list to indexed map). -/
class FiniteMapSeqLaws (M : Type u → _) [FiniteMap M Nat] [FiniteMapLaws M Nat] where
  /-- toList of map_seq is related to zip with sequence.
      `toList (map_seq start l)` is a permutation of `zip (seq start (length l)) l`.
      Corresponds to Rocq's `map_to_list_seq`. -/
  toList_map_seq : ∀ (start : Nat) (l : List V),
    (toList (FiniteMap.map_seq start l : M V)).Perm
      ((List.range' start l.length).zip l)

export FiniteMapLaws (map_eq lookup_empty lookup_insert_eq lookup_insert_ne lookup_delete_eq
lookup_delete_ne
ofList_nil ofList_cons fold_empty fold_fmap_ind)

export FiniteMapLawsSelf (toList_filterMap toList_filter toList_union_disjoint toList_difference)
export FiniteMapKmapLaws (toList_kmap)
export FiniteMapSeqLaws (toList_map_seq)

namespace FiniteMapLaws

variable {M : Type _ → _} {K : Type v} {V : Type _}
variable [DecidableEq K] [FiniteMap M K] [FiniteMapLaws M K]

/-- Auxiliary lemma: if get? (ofList l) k = some v, then (k, v) ∈ l -/
private theorem mem_of_get?_ofList (l : List (K × V)) (k : K) (v : V) :
    get? (ofList l : M V) k = some v → (k, v) ∈ l := by
  intro h
  induction l with
  | nil =>
    simp [ofList_nil, lookup_empty] at h
  | cons kv kvs ih =>
    rw [ofList_cons] at h
    by_cases heq : kv.1 = k
    · -- Case: kv.1 = k, so kv = (k, kv.2)
      -- After insertion, lookup returns kv.2, so v = kv.2
      have eq_val : kv.2 = v := by
        rw [heq, lookup_insert_eq] at h
        exact Option.some.inj h
      -- Therefore (k, v) = (kv.1, kv.2) = kv
      have eq_kv : kv = (k, v) := by
        ext
        · exact heq
        · exact eq_val
      rw [← eq_kv]
      exact List.Mem.head _
    · -- Case: kv.1 ≠ k
      rw [lookup_insert_ne _ _ _ _ heq] at h
      have := ih h
      exact List.Mem.tail _ this


/-- Corresponds to Rocq's `lookup_insert`. -/
theorem lookup_insert (m : M V) (k k' : K) (v : V) :
    get? (insert m k v) k' = if k = k' then some v else get? m k' := by
  split
  · next h => rw [h, lookup_insert_eq]
  · next h => exact lookup_insert_ne m k k' v h

/-- Corresponds to Rocq's `lookup_delete`. -/
theorem lookup_delete (m : M V) (k k' : K) :
    get? (delete m k) k' = if k = k' then none else get? m k' := by
  split
  · next h => rw [h, lookup_delete_eq]
  · next h => exact lookup_delete_ne m k k' h

/-- Corresponds to Rocq's `insert_delete_eq`. -/
theorem lookup_insert_delete (m : M V) (k k' : K) (v : V) :
    get? (insert (delete m k) k v) k' = get? (insert m k v) k' := by
  by_cases h : k = k'
  · simp [h, lookup_insert_eq]
  · simp [lookup_insert_ne _ _ _ _ h, lookup_delete_ne _ _ _ h]

/-- Corresponds to Rocq's `map_to_list_spec`.
  Rocq proof:
  apply (map_fold_weak_ind (λ l m,
    NoDup l ∧ ∀ i x, (i,x) ∈ l ↔ m !! i = Some x)); clear m.
  { split; [constructor|]. intros i x. by rewrite elem_of_nil, lookup_empty. }
  intros i x m l ? [IH1 IH2]. split; [constructor; naive_solver|].
  intros j y. rewrite elem_of_cons, IH2.
  unfold insert, map_insert. destruct (decide (i = j)) as [->|].
  - rewrite lookup_partial_alter_eq. naive_solver.
  - rewrite lookup_partial_alter_ne by done. naive_solver.
-/
private theorem map_to_list_spec (m : M V) :
    (toList m).Nodup ∧ (∀ i x, (i, x) ∈ toList m ↔ get? m i = some x) := by sorry

/-- Corresponds to Rocq's `NoDup_map_to_list`. -/
theorem NoDup_map_to_list (m : M V): (toList m).Nodup := by
   apply (map_to_list_spec m).1

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
    · -- Show f x ∉ xs.map f
      intro hx_in
      rw [List.mem_map] at hx_in
      obtain ⟨y, hy_mem, hy_eq⟩ := hx_in
      -- f y = f x and y ∈ xs
      have hx_mem : x ∈ x :: xs := List.mem_cons_self
      have hy_mem' : y ∈ x :: xs := List.mem_cons_of_mem x hy_mem
      have : x = y := hinj x y hx_mem hy_mem' hy_eq.symm
      subst this
      exact hnodup.1 hy_mem
    · -- xs.map f is nodup
      apply ih hnodup.2
      intro a b ha hb
      exact hinj a b (List.mem_cons_of_mem x ha) (List.mem_cons_of_mem x hb)

/-- Keys of toList have no duplicates - derived from NoDup_map_to_list. -/
theorem NoDup_map_to_list_keys (m : M V): (toList m).map Prod.fst |>.Nodup := by
  apply List.Nodup.map_of_injective (NoDup_map_to_list m)
  -- Need to show: if a, b ∈ toList m and a.fst = b.fst, then a = b
  intro ⟨k₁, v₁⟩ ⟨k₂, v₂⟩ h1 h2 heq
  -- We have (k₁, v₁) and (k₂, v₂) both in toList m with k₁ = k₂
  simp at heq
  -- By map_to_list_spec, both satisfy: get? m kᵢ = some vᵢ
  have ⟨_, hmem⟩ := map_to_list_spec m
  have hv1 : get? m k₁ = some v₁ := (hmem k₁ v₁).mp h1
  have hv2 : get? m k₂ = some v₂ := (hmem k₂ v₂).mp h2
  -- Since k₁ = k₂, we have get? m k₁ = get? m k₂
  rw [heq] at hv1
  -- So some v₁ = some v₂, hence v₁ = v₂
  rw [hv1] at hv2
  cases hv2
  -- Now we have k₁ = k₂ and v₁ = v₂, so the pairs are equal
  ext <;> simp [heq]

/-- Corresponds to Rocq's `elem_of_map_to_list`. -/
theorem elem_of_map_to_list (m : M V) : ∀ k v, (k, v) ∈ toList m ↔ get? m k = some v := by 
  apply (map_to_list_spec m).2

/-- Corresponds to Rocq's `elem_of_list_to_map_2`. -/
theorem elem_of_list_to_map_2 (l : List (K × V)) (i : K) (x : V) :
    get? (ofList l : M V) i = some x → (i, x) ∈ l := by
  induction l with
  | nil =>
    intro h
    rw [ofList_nil, lookup_empty] at h
    cases h
  | cons kv l ih =>
    intro h
    obtain ⟨k, v⟩ := kv
    rw [ofList_cons] at h
    rw [lookup_insert] at h
    split at h
    · next heq =>
        cases h
        rw [← heq]
        simp [List.mem_cons]
    · next hne =>
        have : (i, x) ∈ l := ih h
        exact List.mem_cons_of_mem _ this

/-- Corresponds to Rocq's `elem_of_list_to_map_1`. -/
theorem elem_of_list_to_map_1 (l : List (K × V)) (i : K) (x : V) :
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
      rw [ofList_cons, lookup_insert_eq]
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
      rw [ofList_cons, lookup_insert_ne _ _ _ _ hne, this]

/-- Corresponds to Rocq's `elem_of_list_to_map`
Rocq Proof:
    split; auto using elem_of_list_to_map_1, elem_of_list_to_map_2.  -/
theorem elem_of_list_to_map (l : List (K × V)) i x (hnodup : (l.map Prod.fst).Nodup):
   (i,x) ∈ l ↔ get? (ofList l : M V) i = some x := by sorry

/-- Corresponds to Rocq's `list_to_map_inj`. -/
theorem list_to_map_inj [DecidableEq V] (l1 l2 : List (K × V)) :
    (l1.map Prod.fst).Nodup → (l2.map Prod.fst).Nodup →
    (ofList l1 : M V) = ofList l2 → l1.Perm l2 := by
  intro hnodup1 hnodup2 heq
  have hnodup1' : l1.Nodup := Iris.Std.nodup_of_nodup_map_fst l1 hnodup1
  have hnodup2' : l2.Nodup := Iris.Std.nodup_of_nodup_map_fst l2 hnodup2
  haveI : DecidableEq (K × V) := inferInstance
  apply Iris.Std.perm_of_nodup_of_mem_iff hnodup1' hnodup2'
  intro ⟨i, x⟩
  rw [elem_of_list_to_map (M := M) (K := K) l1 i x hnodup1,
      elem_of_list_to_map (M := M) (K := K) l2 i x hnodup2]
  rw [heq]

/-- Coresponds to Rocq's `list_to_map_to_list` -/
theorem list_to_map_to_list (m : M V) :
    ofList (toList m) = m := by
  apply map_eq (K := K)
  intro i
  cases heq : get? m i
  · cases heq' : get? (ofList (toList m) : M V) i
    · rfl
    · rename_i val
      have hmem : (i, val) ∈ toList m :=
        (elem_of_list_to_map (M := M) (K := K) (toList m) i val (NoDup_map_to_list_keys m)).mpr heq'
      have : get? m i = some val := (elem_of_map_to_list m i val).mp hmem
      rw [heq] at this
      exact Option.noConfusion this
  · rename_i val
    have hmem : (i, val) ∈ toList m := (elem_of_map_to_list m i val).mpr heq
    have : get? (ofList (toList m) : M V) i = some val :=
      (elem_of_list_to_map (M := M) (K := K) (toList m) i val (NoDup_map_to_list_keys m)).mp hmem
    rw [this]

  /-- Corresponds to Rocq's `map_to_list_to_map`. -/
 theorem map_to_list_to_map [DecidableEq V] : ∀ (l : List (K × V)), (l.map Prod.fst).Nodup →
    (toList (ofList l : M V)).Perm l := by
  intro l hnodup
  apply list_to_map_inj (M := M) (K:=K)
  · exact NoDup_map_to_list_keys (M := M) (K := K) (V := V) (ofList l)
  · exact hnodup
  rw [list_to_map_to_list] 

/-- Two maps with the same get? behavior have permutation-equivalent toLists. -/
theorem toList_perm_eq_of_get?_eq [DecidableEq V] {m₁ m₂ : M V}
    (h : ∀ k, get? m₁ k = get? m₂ k) : (toList m₁).Perm (toList m₂) := by
  have hnodup₁ := NoDup_map_to_list (M := M) (K := K) (V := V) m₁
  have hnodup₂ := NoDup_map_to_list (M := M) (K := K) (V := V) m₂
  have hmem : ∀ kv, kv ∈ toList m₁ ↔ kv ∈ toList m₂ := by
    intro ⟨k, v⟩
    rw [elem_of_map_to_list m₁ k v, elem_of_map_to_list m₂ k v, h]
  exact Iris.Std.perm_of_nodup_of_mem_iff hnodup₁ hnodup₂ hmem

/-- toList of insert and insert-after-delete are permutations of each other. -/
theorem toList_insert_delete_perm [DecidableEq V] (m : M V) (k : K) (v : V) :
    (toList (insert m k v)).Perm (toList (insert (delete m k) k v)) :=
  toList_perm_eq_of_get?_eq (fun k' => (lookup_insert_delete m k k' v).symm)

/-- Singleton lookup for equal keys.
    Corresponds to Rocq's `lookup_singleton_eq`. -/
theorem lookup_singleton_eq (k : K) (v : V) :
    get? (FiniteMap.singleton k v : M V) k = some v := by
  simp [FiniteMap.singleton, lookup_insert_eq]

/-- Singleton lookup for different keys.
    Corresponds to Rocq's `lookup_singleton_ne`. -/
theorem lookup_singleton_ne (k k' : K) (v : V) (h : k ≠ k') :
    get? (FiniteMap.singleton k v : M V) k' = none := by
  simp [FiniteMap.singleton, lookup_insert_ne _ _ _ _ h, lookup_empty]

/-- Singleton lookup general case.
    Corresponds to Rocq's `lookup_singleton`. -/
theorem lookup_singleton (k k' : K) (v : V) :
    get? (FiniteMap.singleton k v : M V) k' = if k = k' then some v else none := by
  split
  · next h => rw [h, lookup_singleton_eq]
  · next h => exact lookup_singleton_ne k k' v h

/-- Insert is idempotent for the same key-value.
    Corresponds to Rocq's `insert_insert_eq`. -/
theorem insert_insert_eq (m : M V) (k : K) (v v' : V) :
    get? (insert (insert m k v) k v') = get? (insert m k v' : M V) := by
  funext k'
  by_cases h : k = k'
  · simp [h, lookup_insert_eq]
  · simp [lookup_insert_ne _ _ _ _ h]

/-- Deleting from empty is empty.
    Corresponds to Rocq's `delete_empty`. -/
theorem delete_empty (k : K) :
    get? (delete (∅ : M V) k) = get? (∅ : M V) := by
  funext k'
  by_cases h : k = k'
  · simp [h, lookup_delete_eq, lookup_empty]
  · simp [lookup_delete_ne _ _ _ h, lookup_empty]

/-- Corresponds to Rocq's `map_empty_subseteq`. -/
theorem map_empty_subseteq (m : M V) : (∅ : M V) ⊆ m := by
  intro k v h
  simp [lookup_empty] at h

/-- Corresponds to Rocq's `map_disjoint_empty_l`. -/
theorem map_disjoint_empty_l (m : M V) : FiniteMap.Disjoint (∅ : M V) m := by
  intro k ⟨h₁, _⟩
  simp [lookup_empty] at h₁

/-- Corresponds to Rocq's `lookup_insert_Some`. -/
theorem lookup_insert_Some (m : M V) (i j : K) (x y : V) :
    get? (insert m i x) j = some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ get? m j = some y) := by
  rw [lookup_insert]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_insert_is_Some`. -/
theorem lookup_insert_is_Some (m : M V) (i j : K) (x : V) :
    (get? (insert m i x) j).isSome ↔ i = j ∨ (i ≠ j ∧ (get? m j).isSome) := by
  rw [lookup_insert]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_insert_None`. -/
theorem lookup_insert_None (m : M V) (i j : K) (x : V) :
    get? (insert m i x) j = none ↔ get? m j = none ∧ i ≠ j := by
  rw [lookup_insert]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_insert_rev`. -/
theorem lookup_insert_rev (m : M V) (i : K) (x y : V) :
    get? (insert m i x) i = some y → x = y := by
  simp [lookup_insert_eq]

/-- Corresponds to Rocq's `insert_id`. -/
theorem insert_id (m : M V) (i : K) (x : V) :
    get? m i = some x → (∀ k, get? (insert m i x) k = get? m k) := by
  intro h k
  by_cases hk : i = k
  · subst hk; simp only [lookup_insert_eq, h]
  · simp [lookup_insert_ne _ _ _ _ hk]

/-- Corresponds to Rocq's `lookup_delete_Some`. -/
theorem lookup_delete_Some (m : M V) (i j : K) (y : V) :
    get? (delete m i) j = some y ↔ i ≠ j ∧ get? m j = some y := by
  rw [lookup_delete]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_delete_is_Some`. -/
theorem lookup_delete_is_Some (m : M V) (i j : K) :
    (get? (delete m i) j).isSome ↔ i ≠ j ∧ (get? m j).isSome := by
  rw [lookup_delete]
  split <;> simp_all

/-- Corresponds to Rocq's `lookup_delete_None`. -/
theorem lookup_delete_None (m : M V) (i j : K) :
    get? (delete m i) j = none ↔ i = j ∨ get? m j = none := by
  rw [lookup_delete]
  split <;> simp_all

/-- Corresponds to Rocq's `insert_delete_id`. -/
theorem insert_delete_id (m : M V) (i : K) (x : V) :
    get? m i = some x → insert (delete m i) i x = m := by
  intro h
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_insert_eq, h]
  · simp [lookup_insert_ne _ _ _ _ hij, lookup_delete_ne _ _ _ hij]


  /-- Corresponds to Rocq's `map_to_list_empty`. 
  Rocq proof:
  apply elem_of_nil_inv. intros [i x].
  rewrite elem_of_map_to_list. apply lookup_empty_Some. -/
theorem map_to_list_empty : toList (∅ : M V) = [] := by sorry

  /-- Corresponds to Rocq's `map_to_list_insert`. -/
theorem map_to_list_insert [DecidableEq V] : ∀ (m : M V) k v, get? m k = none →
    (toList (insert m k v)).Perm ((k, v) :: toList m) := by
  intro m k v hk_none
  apply list_to_map_inj (M := M) (K := K)
  · exact NoDup_map_to_list_keys (insert m k v)
  · rw [List.map_cons, List.nodup_cons]
    constructor
    · intro hk_in
      rw [List.mem_map] at hk_in
      obtain ⟨⟨k', v'⟩, hmem, hk_eq⟩ := hk_in
      simp at hk_eq
      subst hk_eq
      have : get? m k' = some v' := (elem_of_map_to_list m k' v').mp hmem
      rw [hk_none] at this
      exact Option.noConfusion this
    · exact NoDup_map_to_list_keys m
  · rw [list_to_map_to_list]
    rw [ofList_cons, list_to_map_to_list]

/-- Corresponds to Rocq's `map_to_list_delete`. -/
theorem map_to_list_delete [DecidableEq V] (m : M V) (k : K) (v : V) (h : get? m k = some v) :
    (toList m).Perm ((k, v) :: toList (delete m k)) := by
  have heq : toList m = toList (insert (delete m k) k v) := by
    rw [insert_delete_id m k v h]
  rw [heq]
  apply map_to_list_insert
  exact lookup_delete_eq m k


/-- Corresponds to Rocq's `delete_insert_id`. -/
theorem delete_insert_id (m : M V) (i : K) (x : V) :
    get? m i = none → delete (insert m i x) i = m := by
  intro h
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_delete_eq, h]
  · simp [lookup_delete_ne _ _ _ hij, lookup_insert_ne _ _ _ _ hij]

/-- Empty map is characterized by all lookups returning none. -/
theorem eq_empty_iff (m : M V) : m = ∅ ↔ ∀ k, get? m k = none := by
  constructor
  · intro h k
    rw [h, lookup_empty]
  · intro h
    apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
    intro k
    rw [h, lookup_empty]

/-- Corresponds to Rocq's `map_ind`. -/
theorem map_ind {P : M V → Prop}
    (hemp : P ∅)
    (hins : ∀ i x m, get? m i = none → P m → P (insert m i x))
    (m : M V) : P m := by
    -- Use fold_fmap_ind to prove map_ind
    apply fold_fmap_ind P hemp
    intro i x m hi _ hPm
    exact hins i x m hi hPm

/-- Corresponds to Rocq's `map_fold_ind`
Rocq proof: 
  intros Hemp Hins m.
  induction m as [|i x m ? Hfold IH] using map_fold_fmap_ind; [done|].
  apply Hins; [done| |done]. intros B f b x'.
  assert (m = id <$> m) as →.
  { apply map_eq; intros j; by rewrite lookup_fmap, option_fmap_id. }
  apply Hfold.
    -/
private theorem map_fold_ind (P : M V → Prop) :
  P ∅ →
  (∀ i x m,
    get? m i = none →
    (∀ B (f : K → V → B → B) b x',
      fold f b (insert m i x') = f i x' (fold f b m)) →
    P m →
    P (insert m i x)) →
  ∀ m, P m := by sorry


/-- Corresponds to Rocq's `map_fold_weak_ind`. -/
theorem fold_weak_ind {B : Type u''}
    (P : B → M V → Prop) (f : K → V → B → B) (b : B)
    (hemp : P b ∅)
    (hins : ∀ i x m r, get? m i = none → P r m → P (f i x r) (insert m i x))
    (m : M V) : P (fold f b m) m := by
  sorry

/-- Induction principle with first key constraint: prove properties about maps by induction,
    where the inductive step requires that the inserted key becomes the first key.

    Corresponds to Rocq's `map_first_key_ind`. -/
theorem map_first_key_ind (P : M V → Prop)
    (hemp : P ∅)
    (hins : ∀ i x m, get? m i = none → FiniteMap.firstKey (insert m i x) i → P m → P (insert m i x))
    (m : M V) : P m := by
  sorry

/-- Corresponds to Rocq's `map_fold_foldr` 
Rocq proof:
  unfold map_to_list. induction m as [|i x m ? Hfold IH] using map_fold_ind.
  - by rewrite !map_fold_empty.
  - by rewrite !Hfold, IH.
-/
theorem fold_foldr (f : K → V → B → B) b (m : M V) :
  fold f b m = List.foldr (fun ⟨k, v⟩ b => f k v b) b (toList m) := by sorry


/-- Corresponds to Rocq's `map_fold_fmap`
Rocq Proof:
  induction m as [|i x m ? Hfold IH] using map_fold_fmap_ind.
  { by rewrite fmap_empty, !map_fold_empty. }
  rewrite fmap_insert. rewrite <-(map_fmap_id m) at 2. rewrite !Hfold.
  by rewrite IH, map_fmap_id. -/
theorem fold_map (f : K → V' → B → B) (g : V → V') b (m : M V) :
  fold f b (FiniteMap.map g m) = fold (fun i => f i ∘ g) b m := by sorry


/-- toList of map (fmap) is a permutation of mapping over toList.
    This is a weaker form that we can prove without the fold-based infrastructure.
    The stronger equality version (`toList_map_eq`) would require `fold_map` and `fold_foldr`. -/
theorem toList_map [DecidableEq V'] : ∀ (m : M V) (f : V → V'),
  (toList (FiniteMap.map f m)).Perm
      ((toList m).map (fun kv => (kv.1, f kv.2))) := by
  intro m f
  simp only [FiniteMap.map]
  -- toList (ofList ((toList m).map g)) is Perm to (toList m).map g
  -- where g = fun kv => (kv.1, f kv.2)
  apply map_to_list_to_map
  -- Need to show: ((toList m).map g).map Prod.fst |>.Nodup
  simp only [List.map_map]
  show ((toList m).map (fun x => x.1)).Nodup
  exact NoDup_map_to_list_keys m

/-- toList of map (fmap) equals mapping over toList (equality version).
    `toList (map f m) = (toList m).map (fun (k, v) => (k, f v))`
    Corresponds to Rocq's `map_to_list_fmap`
   Rocq proof:
  unfold map_to_list. rewrite map_fold_fmap, !map_fold_foldr.
  induction (map_to_list m) as [|[]]; f_equal/=; auto.
  This requires `fold_map` and `fold_foldr` which are currently unimplemented. -/
theorem toList_map_eq [DecidableEq V'] : ∀ (m : M V) (f : V → V'),
  toList (FiniteMap.map f m) =
      ((toList m).map (fun kv => (kv.1, f kv.2))) := by sorry

/-- Corresponds to Rocq's `delete_delete_eq`. -/
theorem delete_delete_eq (m : M V) (i : K) :
    delete (delete m i) i = delete m i := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_delete_eq]
  · simp [lookup_delete_ne _ _ _ hij]

/-- Corresponds to Rocq's `delete_delete`. -/
theorem delete_delete (m : M V) (i j : K) :
    delete (delete m i) j = delete (delete m j) i := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k <;> simp [lookup_delete, *]

/-- Corresponds to Rocq's `delete_insert_ne`. -/
theorem delete_insert_ne (m : M V) (i j : K) (x : V) :
    i ≠ j → delete (insert m i x) j = insert (delete m j) i x := by
  intro hij
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk; exact absurd rfl hij
  · subst hik; simp [lookup_insert, lookup_delete, hjk]
  · subst hjk; simp [lookup_insert, lookup_delete, hik]
  · simp [lookup_insert, lookup_delete, hik, hjk]

/-- Corresponds to Rocq's `insert_delete_eq`. -/
theorem insert_delete_eq (m : M V) (i : K) (x : V) :
    insert (delete m i) i x = insert m i x := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_insert_eq]
  · simp [lookup_insert_ne _ _ _ _ hij, lookup_delete_ne _ _ _ hij]

/-- Corresponds to Rocq's `insert_insert`. -/
theorem insert_insert (m : M V) (i j : K) (x y : V) :
    i ≠ j → insert (insert m i x) j y = insert (insert m j y) i x := by
  intro hij
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk; exact absurd rfl hij
  · subst hik; simp [lookup_insert, hjk]
  · subst hjk; simp [lookup_insert, hik]
  · simp [lookup_insert, hik, hjk]

/-- Corresponds to Rocq's `insert_insert_eq`. -/
theorem insert_insert_eq' (m : M V) (i : K) (x y : V) :
    insert (insert m i x) i y = insert m i y := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_insert_eq]
  · simp [lookup_insert_ne _ _ _ _ hij]

/-- Corresponds to Rocq's `delete_empty`. -/
theorem delete_empty' (i : K) :
    delete (∅ : M V) i = ∅ := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  simp [lookup_delete, lookup_empty]

/-- Corresponds to Rocq's `delete_id`. -/
theorem delete_id (m : M V) (i : K) :
    get? m i = none → delete m i = m := by
  intro h
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_delete_eq, h]
  · simp [lookup_delete_ne _ _ _ hij]

/-- Corresponds to Rocq's `insert_id`. -/
theorem insert_id' (m : M V) (i : K) (x : V) :
    get? m i = some x → insert m i x = m := by
  intro h
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [lookup_insert_eq, h]
  · simp [lookup_insert_ne _ _ _ _ hij]

/-- Corresponds to Rocq's `insert_empty`. -/
theorem insert_empty (i : K) (x : V) :
    insert (∅ : M V) i x = FiniteMap.singleton i x := by
  rfl

/-- Corresponds to Rocq's `insert_non_empty`. -/
theorem insert_non_empty (m : M V) (i : K) (x : V) :
    insert m i x ≠ ∅ := by
  intro h
  have := eq_empty_iff (insert m i x) |>.mp h i
  simp [lookup_insert_eq] at this

/-- Corresponds to Rocq's `delete_subseteq`. -/
theorem delete_subseteq (m : M V) (i : K) : delete m i ⊆ m := by
  intro k v h
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at h
  · simp [lookup_delete_ne _ _ _ hik] at h
    exact h

/-- Corresponds to Rocq's `delete_subset`. -/
theorem delete_subset (m : M V) (i : K) (v : V) :
    get? m i = some v → delete m i ⊆ m ∧ delete m i ≠ m := by
  intro hi
  constructor
  · exact delete_subseteq m i
  · intro heq
    have : get? (delete m i) i = get? m i := by rw [heq]
    simp [lookup_delete_eq, hi] at this

/-- Corresponds to Rocq's `insert_subseteq`. -/
theorem insert_subseteq (m : M V) (i : K) (x : V) :
    get? m i = none → m ⊆ insert m i x := by
  intro hi k v hk
  by_cases hik : i = k
  · subst hik
    simp [hi] at hk
  · simp [lookup_insert_ne _ _ _ _ hik, hk]

/-- Corresponds to Rocq's `insert_subset`. -/
theorem insert_subset (m : M V) (i : K) (x : V) :
    get? m i = none → m ⊆ insert m i x ∧ m ≠ insert m i x := by
  intro hi
  constructor
  · exact insert_subseteq m i x hi
  · intro heq
    have h2 : get? (insert m i x) i = some x := lookup_insert_eq m i x
    rw [← heq] at h2
    rw [hi] at h2
    exact Option.noConfusion h2

/-- Corresponds to Rocq's `delete_mono`. -/
theorem delete_mono (m₁ m₂ : M V) (i : K) :
    m₁ ⊆ m₂ → delete m₁ i ⊆ delete m₂ i := by
  intro hsub k v hk
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at hk
  · simp [lookup_delete_ne _ _ _ hik] at hk ⊢
    exact hsub k v hk

/-- Corresponds to Rocq's `insert_mono`. -/
theorem insert_mono (m₁ m₂ : M V) (i : K) (x : V) :
    m₁ ⊆ m₂ → insert m₁ i x ⊆ insert m₂ i x := by
  intro hsub k v hk
  by_cases hik : i = k
  · subst hik
    simp [lookup_insert_eq] at hk ⊢
    exact hk
  · simp [lookup_insert_ne _ _ _ _ hik] at hk ⊢
    exact hsub k v hk

/-- Corresponds to Rocq's `map_non_empty_singleton`. -/
theorem singleton_non_empty (i : K) (x : V) :
    FiniteMap.singleton i x ≠ (∅ : M V) := by
  exact insert_non_empty ∅ i x

/-- Corresponds to Rocq's `delete_singleton_eq`. -/
theorem delete_singleton_eq (i : K) (x : V) :
    delete (FiniteMap.singleton i x : M V) i = ∅ := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro j
  simp [FiniteMap.singleton, lookup_delete, lookup_insert, lookup_empty]

/-- Corresponds to Rocq's `delete_singleton_ne`. -/
theorem delete_singleton_ne (i j : K) (x : V) :
    i ≠ j → delete (FiniteMap.singleton j x : M V) i = FiniteMap.singleton j x := by
  intro hij
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  simp [FiniteMap.singleton, lookup_delete, lookup_insert, lookup_empty]
  intro hik
  intro hjk
  subst hik hjk
  exact hij rfl

/-- Corresponds to Rocq's `map_Forall_to_list`. -/
theorem map_Forall_to_list (P : K → V → Prop) (m : M V) :
    FiniteMap.map_Forall P m ↔ ∀ kv ∈ toList m, P kv.1 kv.2 := by
  constructor
  · intro hfa kv hmem
    have := (elem_of_map_to_list m kv.1 kv.2).mp hmem
    exact hfa kv.1 kv.2 this
  · intro hlist k v hget
    have := (elem_of_map_to_list m k v).mpr hget
    exact hlist (k, v) this

/-- Corresponds to Rocq's `map_Forall_empty`. -/
theorem map_Forall_empty (P : K → V → Prop) : FiniteMap.map_Forall P (∅ : M V) := by
  intro k v h
  simp [lookup_empty] at h

/-- Corresponds to Rocq's `map_Forall_impl`. -/
theorem map_Forall_impl (P Q : K → V → Prop) (m : M V) :
    FiniteMap.map_Forall P m → (∀ k v, P k v → Q k v) → FiniteMap.map_Forall Q m := by
  intro hp himpl k v hget
  exact himpl k v (hp k v hget)

/-- Corresponds to Rocq's `map_Forall_insert_1_1`. -/
theorem map_Forall_insert_1_1 (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    FiniteMap.map_Forall P (insert m i x) → P i x := by
  intro hfa
  exact hfa i x (lookup_insert_eq m i x)

/-- Corresponds to Rocq's `map_Forall_insert_1_2`. -/
theorem map_Forall_insert_1_2 (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    get? m i = none → FiniteMap.map_Forall P (insert m i x) → FiniteMap.map_Forall P m := by
  intro hi hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [hi] at hget
  · have : get? (insert m i x) k = some v := by
      simp [lookup_insert_ne _ _ _ _ hik, hget]
    exact hfa k v this

/-- Corresponds to Rocq's `map_Forall_insert_2`. -/
theorem map_Forall_insert_2 (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    P i x → FiniteMap.map_Forall P m → FiniteMap.map_Forall P (insert m i x) := by
  intro hpix hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [lookup_insert_eq] at hget
    rw [← hget]
    exact hpix
  · simp [lookup_insert_ne _ _ _ _ hik] at hget
    exact hfa k v hget

/-- Corresponds to Rocq's `map_Forall_insert`. -/
theorem map_Forall_insert (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    get? m i = none → (FiniteMap.map_Forall P (insert m i x) ↔ P i x ∧ FiniteMap.map_Forall P m) := by
  intro hi
  constructor
  · intro hfa
    exact ⟨map_Forall_insert_1_1 P m i x hfa, map_Forall_insert_1_2 P m i x hi hfa⟩
  · intro ⟨hpix, hfa⟩
    exact map_Forall_insert_2 P m i x hpix hfa

/-- Corresponds to Rocq's `map_Forall_singleton`. -/
theorem map_Forall_singleton (P : K → V → Prop) (i : K) (x : V) :
    FiniteMap.map_Forall P (FiniteMap.singleton i x : M V) ↔ P i x := by
  constructor
  · intro hfa
    exact hfa i x (lookup_singleton_eq i x)
  · intro hpix k v hget
    simp [lookup_singleton] at hget
    obtain ⟨rfl, rfl⟩ := hget
    exact hpix

/-- Corresponds to Rocq's `map_Forall_delete`. -/
theorem map_Forall_delete (P : K → V → Prop) (m : M V) (i : K) :
    FiniteMap.map_Forall P m → FiniteMap.map_Forall P (delete m i) := by
  intro hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at hget
  · simp [lookup_delete_ne _ _ _ hik] at hget
    exact hfa k v hget

/-- Corresponds to Rocq's `map_disjoint_spec`. -/
theorem map_disjoint_spec (m₁ m₂ : M V) :
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

/-- Corresponds to Rocq's `map_disjoint_insert_l`. -/
theorem map_disjoint_insert_l (m₁ m₂ : M V) (i : K) (x : V) :
    get? m₂ i = none →
    FiniteMap.Disjoint m₁ m₂ →
    FiniteMap.Disjoint (insert m₁ i x) m₂ := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [lookup_insert_ne _ _ _ _ hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

/-- Corresponds to Rocq's `map_disjoint_insert_r`. -/
theorem map_disjoint_insert_r (m₁ m₂ : M V) (i : K) (x : V) :
    get? m₁ i = none →
    FiniteMap.Disjoint m₁ m₂ →
    FiniteMap.Disjoint m₁ (insert m₂ i x) := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [lookup_insert_ne _ _ _ _ hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

/-- Corresponds to Rocq's `map_disjoint_delete_l`. -/
theorem map_disjoint_delete_l (m₁ m₂ : M V) (i : K) :
    FiniteMap.Disjoint m₁ m₂ → FiniteMap.Disjoint (delete m₁ i) m₂ := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at hs1
  · simp [lookup_delete_ne _ _ _ hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

/-- Corresponds to Rocq's `map_disjoint_delete_r`. -/
theorem map_disjoint_delete_r (m₁ m₂ : M V) (i : K) :
    FiniteMap.Disjoint m₁ m₂ → FiniteMap.Disjoint m₁ (delete m₂ i) := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [lookup_delete_eq] at hs2
  · simp [lookup_delete_ne _ _ _ hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

/-- Corresponds to Rocq's `map_disjoint_singleton_l`. -/
theorem map_disjoint_singleton_l (m : M V) (i : K) (x : V) :
    get? m i = none → FiniteMap.Disjoint (FiniteMap.singleton i x) m := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [FiniteMap.singleton, lookup_insert_ne _ _ _ _ hik, lookup_empty] at hs1

/-- Corresponds to Rocq's `map_disjoint_singleton_r`. -/
theorem map_disjoint_singleton_r (m : M V) (i : K) (x : V) :
    get? m i = none → FiniteMap.Disjoint m (FiniteMap.singleton i x) := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [FiniteMap.singleton, lookup_insert_ne _ _ _ _ hik, lookup_empty] at hs2

/-- Corresponds to Rocq's `map_fmap_zip_with_r`.
    When `g1 (f x y) = x` and the domains of m1 and m2 match,
    mapping g1 over zipWith f m1 m2 gives back m1 (up to map equality). -/
theorem map_fmap_zipWith_r {V' V'' : Type _} [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (g1 : V'' → V) (m1 : M V) (m2 : M V')
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    FiniteMap.map g1 (FiniteMap.zipWith f m1 m2) = m1 := by
  sorry

/-- Corresponds to Rocq's `map_fmap_zip_with_l`.
    When `g2 (f x y) = y` and the domains of m1 and m2 match,
    mapping g2 over zipWith f m1 m2 gives back m2 (up to map equality). -/
theorem map_fmap_zipWith_l {V' V'' : Type _} [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (g2 : V'' → V') (m1 : M V) (m2 : M V')
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    FiniteMap.map g2 (FiniteMap.zipWith f m1 m2) = m2 := by
  sorry

end FiniteMapLaws

namespace FiniteMap

variable {M : Type _ → _} {K : Type v} {V : Type w} [FiniteMap M K]

/-- Submap is reflexive. -/
theorem submap_refl (m : M V) : m ⊆ m := fun _ _ h => h

/-- Submap is transitive. -/
theorem submap_trans {m₁ m₂ m₃ : M V} (h₁ : m₁ ⊆ m₂) (h₂ : m₂ ⊆ m₃) : m₁ ⊆ m₃ :=
  fun k v hm₁ => h₂ k v (h₁ k v hm₁)

/-- Disjointness is symmetric. -/
theorem disjoint_symm {m₁ m₂ : M V} (h : Disjoint m₁ m₂) : Disjoint m₂ m₁ :=
  fun k ⟨h₂, h₁⟩ => h k ⟨h₁, h₂⟩

theorem map_disjoint_empty_r [DecidableEq K] [FiniteMapLaws M K] (m : M V) : Disjoint m (∅ : M V) :=
  disjoint_symm (FiniteMapLaws.map_disjoint_empty_l m)

/-- `m₂` and `m₁ \ m₂` are disjoint. -/
theorem disjoint_difference_r [DecidableEq K] [FiniteMapLaws M K] [FiniteMapLawsSelf M K]
    (m₁ m₂ : M V) : Disjoint m₂ (m₁ \ m₂) := by
  intro k ⟨h_in_m2, h_in_diff⟩
  rw [FiniteMapLaws.lookup_difference] at h_in_diff
  simp only [h_in_m2, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at h_in_diff

/-- Corresponds to Rocq's `map_difference_union`. -/
theorem map_difference_union [DecidableEq K] [FiniteMapLaws M K] [FiniteMapLawsSelf M K]
    (m₁ m₂ : M V) (hsub : m₂ ⊆ m₁) : m₂ ∪ (m₁ \ m₂) = m₁ := by
  apply FiniteMapLaws.map_eq (M := M) (K := K) (V := V)
  intro k
  rw [FiniteMapLaws.lookup_union, FiniteMapLaws.lookup_difference]
  cases hm2 : get? m₂ k with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
  | some v =>
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
