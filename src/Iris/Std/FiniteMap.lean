/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Markus de Medeiros
-/

import Iris.Std.PartialMap
import Iris.Std.List

/-! ## Abstract Finite Map Interface

This file defines an abstract interface for finite maps with finite support,
extending the base PartialMap interface with list conversion operations.

Inspired by stdpp's `fin_maps`. -/

namespace Iris.Std

/-- The type `M` represents a finite map from keys of type `K` to values of type `V`.
    Extends `PartialMap` with operations for converting to/from lists. -/
class FiniteMap (K : outParam (Type u)) (M : Type u' → Type _)
    extends PartialMap M K where
  /-- Convert the map to a list of key-value pairs. -/
  toList : M V → List (K × V)
  /-- Construct a map from a list of key-value pairs. -/
  ofList : List (K × V) → M V
  /-- Fold over all key-value pairs in the map.
      The order of folding depends on the internal representation. -/
  fold {A : Type u'} : (K → V → A → A) → A → M V → A

export FiniteMap (toList ofList fold)

namespace FiniteMap

variable {K : Type u} {V : Type u'} {M : Type u' → Type _} [FiniteMap K M]

/-- Singleton map: a map with a single key-value pair. -/
abbrev singleton (k : K) (v : V) : M V := PartialMap.singleton k v

/-- Union of two maps (left-biased: values from `m₁` take precedence).
    Concrete implementation using toList. -/
def union (m₁ m₂ : M V) : M V :=
  (toList m₁).foldl (fun acc (k, v) => insert acc k v) m₂

instance : Union (M V) := ⟨union⟩

/-- Map a function over all values in the map. -/
def map (f : V → V') : M V → (M V') :=
  fun m => ofList ((toList m).map (fun (k, v) => (k, f v)))

/-- Filter and map: apply a function that can optionally drop entries. -/
def filterMap (f : V → Option V) : M V → M V :=
  fun m => ofList ((toList m).filterMap (fun (k, v) => (f v).map (k, ·)))

/-- Filter entries by a predicate on key-value pairs. -/
def filter (φ : K → V → Bool) : M V → M V :=
  fun m => ofList ((toList m).filter (fun (k, v) => φ k v))

/-- Zip two maps with a combining function. -/
def zipWith {V' : Type _} {V'' : Type _} (f : V → V' → V'') (m₁ : M V) (m₂ : M V') : M V'' :=
  ofList ((toList m₁).filterMap (fun (k, v) =>
    match get? m₂ k with
    | some v' => some (k, f v v')
    | none => none))

/-- Zip two maps: combine values at matching keys into pairs. -/
def zip (m₁ : M V) (m₂ : M V') : M (V × V') :=
  zipWith Prod.mk m₁ m₂

/-- Difference: remove all keys in `m₂` from `m₁`. -/
def difference (m₁ m₂ : M V) : M V :=
  ofList ((toList m₁).filter (fun (k, _) => (get? m₂ k).isNone))

instance : SDiff (M V) := ⟨difference⟩

/-- Transform keys of a map using an injective function. -/
def kmap {K' : Type u} {M' : Type u' → _} [FiniteMap K' M'] (f : K → K') (m : M V) : (M' V) :=
  ofList ((toList m).map (fun (k, v) => (f k, v)))

/-- Convert a list to a map with sequential natural number keys starting from `start`. -/
def map_seq [FiniteMap Nat M] (start : Nat) (l : List V) : M V :=
  ofList (l.mapIdx (fun i v => (start + i, v)))

/-- Check if a key is the first key in the map's `toList` representation. -/
def firstKey (m : M V) (i : K) : Prop :=
  ∃ x, (toList m).head? = some (i, x)

end FiniteMap

/-- Laws that a finite map implementation must satisfy.
    Extends LawfulPartialMap with laws specific to list conversion. -/
class FiniteMapLaws (K : (outParam (Type u))) (M : Type u' → Type _)
    [DecidableEq K] [FiniteMap K M] extends LawfulPartialMap M K where
  ofList_nil : (ofList [] : M V) = ∅
  ofList_cons : ∀ (k : K) (v : V) (l : List (K × V)),
    (ofList ((k, v) :: l) : M V) = insert (ofList l) k v
  toList_spec (m : M V) :
    (toList m).Nodup ∧ (∀ i x, (i, x) ∈ toList m ↔ get? m i = some x)

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
  /-- toList of kmap is related to mapping over toList. -/
  toList_kmap : ∀ (f : K → K') (m : M V),
    (∀ {x y}, f x = f y → x = y) →  -- f is injective
    (toList (FiniteMap.kmap (M' := M') f m)).Perm
      ((toList m).map (fun (k, v) => (f k, v)))

/-- Laws for map_seq operation. -/
class FiniteMapSeqLaws (M : Type u → Type _) [FiniteMap Nat M] [FiniteMapLaws Nat M] where
  /-- toList of map_seq is related to zip with sequence. -/
  toList_map_seq : ∀ (start : Nat) (l : List V),
    (toList (FiniteMap.map_seq start l : M V)).Perm
      ((List.range' start l.length).zip l)

export FiniteMapLaws (ofList_nil ofList_cons toList_spec)

export FiniteMapLawsSelf (toList_filterMap toList_filter)
export FiniteMapKmapLaws (toList_kmap)
export FiniteMapSeqLaws (toList_map_seq)

namespace FiniteMapLaws

variable {K : Type u} {V : Type u'} {M : Type u' → Type _}
variable [DecidableEq K] [FiniteMap K M] [FiniteMapLaws K M]

/-- Extensionality for maps: two maps are equal if they agree on all keys. -/
theorem ext [ExtensionalPartialMap M K] {m₁ m₂ : M V} (h : ∀ k, get? m₁ k = get? m₂ k) : m₁ = m₂ := by
  apply ExtensionalPartialMap.equiv_iff_eq.mp
  exact h

private theorem mem_of_get?_ofList (l : List (K × V)) (k : K) (v : V) :
    get? (ofList l : M V) k = some v → (k, v) ∈ l := by
  intro h
  induction l with
  | nil =>
    rw [ofList_nil] at h
    simp only [EmptyCollection.emptyCollection] at h
    have : get? (empty : M V) k = none := get?_empty k
    rw [this] at h
    cases h
  | cons kv kvs ih =>
    rw [ofList_cons] at h
    by_cases heq : kv.1 = k
    · suffices kv = (k, v) by rw [← this]; exact List.Mem.head _
      ext <;> simp [heq]
      have : get? (insert (ofList kvs) k kv.snd) k = some v := by rw [← heq]; exact h
      rw [get?_insert_eq rfl] at this
      exact Option.some.inj this
    · have : get? (insert (ofList kvs) kv.1 kv.snd) k = get? (ofList kvs) k := get?_insert_ne heq
      rw [this] at h
      exact List.Mem.tail _ (ih h)

theorem nodup_toList (m : M V): (toList m).Nodup :=
  (toList_spec m).1

/-- If a list has no duplicates and the projection is injective on list elements,
    then the mapped list has no duplicates. -/
theorem List.Nodup.map_of_injective {α β : Type _} {l : List α} {f : α → β}
    (hnodup : l.Nodup) (hinj : ∀ a b, a ∈ l → b ∈ l → f a = f b → a = b) :
    (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
    refine ⟨?_, ih hnodup.2 fun a b ha hb => hinj a b (.tail _ ha) (.tail _ hb)⟩
    intro h; rw [List.mem_map] at h
    obtain ⟨y, hy_mem, heq⟩ := h
    exact hnodup.1 (hinj x y (.head _) (.tail _ hy_mem) heq.symm ▸ hy_mem)

/-- Keys of toList have no duplicates. -/
theorem nodup_toList_keys (m : M V) : (toList m).map Prod.fst |>.Nodup := by
  apply List.Nodup.map_of_injective (nodup_toList m)
  intro ⟨k₁, v₁⟩ ⟨k₂, v₂⟩ h1 h2 heq
  simp at heq
  obtain ⟨_, hmem⟩ := toList_spec (M := M) (K := K) (V := V) m
  ext <;> simp [heq]
  have hv1 := (hmem k₁ v₁).mp h1
  have hv2 := (hmem k₂ v₂).mp h2
  rw [heq] at hv1
  rw [hv1] at hv2
  cases hv2;rfl

theorem mem_toList (m : M V) (k : K) (v : V) : (k, v) ∈ toList m ↔ get? m k = some v :=
  (toList_spec m).2 k v

/-- Membership characterization for ofList (right-to-left direction). -/
theorem mem_ofList_of_mem (l : List (K × V)) (i : K) (x : V) :
    (l.map Prod.fst).Nodup → (i, x) ∈ l → get? (ofList l : M V) i = some x := by
  intro hnodup hmem
  induction l with
  | nil => simp at hmem
  | cons kv l ih =>
    obtain ⟨k, v⟩ := kv
    simp [ofList_cons, List.map_cons, List.nodup_cons] at hnodup hmem ⊢
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact get?_insert_eq rfl
    · have hne : k ≠ i := by
        intro heq; subst heq
        exact hnodup.1 _ hmem
      rw [get?_insert_ne hne, ih hnodup.2 hmem]

theorem mem_ofList (l : List (K × V)) i x (hnodup : (l.map Prod.fst).Nodup):
   (i,x) ∈ l ↔ get? (ofList l : M V) i = some x := by
    constructor
    apply mem_ofList_of_mem; exact hnodup
    apply mem_of_get?_ofList

theorem ofList_injective [DecidableEq V] (l1 l2 : List (K × V)) :
    (l1.map Prod.fst).Nodup → (l2.map Prod.fst).Nodup →
    (ofList l1 : M V) = ofList l2 → l1.Perm l2 := by
  intro hnodup1 hnodup2 heq
  apply List.perm_of_nodup_of_mem_iff
  · exact List.nodup_of_nodup_map_fst l1 hnodup1
  · exact List.nodup_of_nodup_map_fst l2 hnodup2
  intro ⟨i, x⟩
  rw [mem_ofList (M := M) (K := K) l1 i x hnodup1,
      mem_ofList (M := M) (K := K) l2 i x hnodup2]
  rw [heq]

theorem ofList_toList (m : M V) [ExtensionalPartialMap M K] :
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
      cases this
  · rename_i val
    have hmem : (i, val) ∈ toList m := (mem_toList m i val).mpr heq
    have : get? (ofList (toList m) : M V) i = some val :=
      (mem_ofList (M := M) (K := K) (toList m) i val (nodup_toList_keys m)).mp hmem
    rw [this]

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
  toList_perm_of_get?_eq (fun k' => LawfulPartialMap.get?_insert_delete_same.symm)

/-- Insert is idempotent for the same key-value. -/
/-- Insert overwrites previous value for the same key. -/
theorem insert_insert (m : M V) (k : K) (v v' : V) :
    get? (insert (insert m k v) k v') = get? (insert m k v' : M V) := by
  funext k'
  by_cases h : k = k'
  · subst h; simp [get?_insert_eq rfl]
  · simp [get?_insert_ne h]

/-- Value at a key after insert must equal the inserted value. -/
theorem get?_insert_rev (m : M V) (i : K) (x y : V) :
    get? (insert m i x) i = some y → x = y := by
  simp [get?_insert_eq rfl]

theorem toList_empty : toList (∅ : M V) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ⟨i, x⟩ hmem
  have h1 : get? (∅ : M V) i = some x := (mem_toList _ i x).mp hmem
  have h2 : get? (∅ : M V) i = none := get?_empty (M := M) i
  rw [h2] at h1
  cases h1

theorem toList_insert [DecidableEq V] : ∀ (m : M V) k v, get? m k = none →
    (toList (insert m k v)).Perm ((k, v) :: toList m) := by
  intro m k v hk_none
  refine ofList_injective (M := M) (K := K) _ _ (nodup_toList_keys _) ?_ ?_
  · simp only [List.map_cons, List.nodup_cons, nodup_toList_keys m]
    simp [mem_toList, hk_none]
  · rw [ofList_toList, ofList_cons, ofList_toList]

theorem toList_delete [DecidableEq V] (m : M V) (k : K) (v : V) (h : get? m k = some v) :
    (toList m).Perm ((k, v) :: toList (delete m k)) := by
  have heq : toList m = toList (insert (delete m k) k v) := by
    rw [LawfulPartialMap.insert_delete_cancel m k v h]
  rw [heq]
  apply toList_insert
  exact get?_delete_eq rfl m k

theorem all_iff_toList (P : K → V → Prop) (m : M V) :
    PartialMap.all P m ↔ ∀ kv ∈ toList m, P kv.1 kv.2 := by
  constructor
  · intro hfa kv hmem
    apply hfa kv.1 kv.2 ((mem_toList m kv.1 kv.2).mp hmem)
  · intro hlist k v hget
    apply hlist (k, v) ((mem_toList m k v).mpr hget)

theorem toList_map [DecidableEq V'] : ∀ (m : M V) (f : V → V'),
  (toList (FiniteMap.map f m)).Perm
      ((toList m).map (fun kv => (kv.1, f kv.2))) := by
  intro m f
  simp only [FiniteMap.map]
  apply toList_ofList
  simp only [List.map_map]
  show ((toList m).map (fun x => x.1)).Nodup
  apply nodup_toList_keys

/-- Lookup in a mapped map. -/
theorem get?_map [DecidableEq V] {V' : Type _} [DecidableEq V'] (f : V → V') (m : M V) (k : K) :
    get? (FiniteMap.map f m) k = (get? m k).map f := by
  simp only [FiniteMap.map]
  have hnodup : ((toList m).map (fun (ki, vi) => (ki, f vi))).map Prod.fst |>.Nodup := by
    simp only [List.map_map]; exact nodup_toList_keys m
  cases hm : get? m k <;> simp
  · apply Option.eq_none_iff_forall_not_mem.mpr
    intro v' hv'
    have := (mem_ofList _ _ _ hnodup).mpr hv'
    rw [List.mem_map] at this
    obtain ⟨⟨k', v⟩, hmem, heq⟩ := this
    simp at heq
    have : get? m k' = some v := (mem_toList m k' v).mp hmem
    rw [heq.1, hm] at this
    cases this
  · rename_i v
    rw [(mem_ofList _ _ _ hnodup).mp]
    rw [List.mem_map]
    exact ⟨(k, v), (mem_toList m k v).mpr hm, rfl⟩

omit [DecidableEq K] in
/-- filterMap preserves Nodup on keys. -/
private theorem nodup_map_fst_filterMap
    (l : List (K × V)) (g : K → V → Option (K × V')) :
    (l.map Prod.fst).Nodup →
    (∀ ki vi k' v', g ki vi = some (k', v') → k' = ki) →
    ((l.filterMap (fun (ki, vi) => g ki vi)).map Prod.fst).Nodup := by
  intro h_nodup h_preserve_key
  induction l with
  | nil => simp
  | cons kv tail ih =>
    obtain ⟨k, v⟩ := kv
    rw [List.map_cons, List.nodup_cons] at h_nodup
    simp only [List.filterMap]
    cases hg : g k v with
    | none => exact ih h_nodup.2
    | some res =>
      obtain ⟨k', v'⟩ := res
      have : k' = k := h_preserve_key k v k' v' hg
      subst this
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => h_nodup.1 ?_, ih h_nodup.2⟩
      clear h_nodup ih
      induction tail with
      | nil => cases hmem
      | cons kv' tail' ih_aux =>
        obtain ⟨k'', v''⟩ := kv'
        simp only [List.filterMap] at hmem
        cases hg' : g k'' v'' with
        | none => simp only [hg'] at hmem; exact List.mem_cons_of_mem k'' (ih_aux hmem)
        | some res' =>
          obtain ⟨k''', v'''⟩ := res'
          have hk_eq : k''' = k'' := h_preserve_key k'' v'' k''' v''' hg'
          simp only [hg', List.map_cons, List.mem_cons] at hmem
          rcases hmem with rfl | hmem'
          · rw [List.map_cons, List.mem_cons, hk_eq]; simp
          · rw [List.map_cons, List.mem_cons]; right; exact ih_aux hmem'

/-- Lookup in zipWith. -/
theorem get?_zipWith [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') (k : K) :
    get? (FiniteMap.zipWith f m1 m2) k =
      match get? m1 k, get? m2 k with
      | some v1, some v2 => some (f v1 v2)
      | _, _ => none := by
  simp only [FiniteMap.zipWith]
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
    exact heq.1.symm
  cases h1 : get? m1 k
  · simp; cases h' : get? (ofList _ : M V'') k
    · rfl
    · rename_i v_result
      have hmem := (mem_ofList (M := M) (V := V'') _ k v_result hnodup).mpr h'
      rw [List.mem_filterMap] at hmem
      obtain ⟨⟨k', v1'⟩, hmem1, hmatch⟩ := hmem
      simp at hmatch
      cases hm2 : get? m2 k' <;> simp [hm2] at hmatch
      have : get? m1 k' = some v1' := (mem_toList m1 k' v1').mp hmem1
      rw [hmatch.1, h1] at this
      cases this
  · rename_i v1
    cases h2 : get? m2 k
    · simp; cases h' : get? (ofList _ : M V'') k
      · rfl
      · rename_i v_result
        have hmem := (mem_ofList (M := M) (V := V'') _ k v_result hnodup).mpr h'
        rw [List.mem_filterMap] at hmem
        obtain ⟨⟨k', v1'⟩, hmem1, hmatch⟩ := hmem
        simp at hmatch
        cases hm2 : get? m2 k' <;> simp [hm2] at hmatch
        rw [hmatch.1, h2] at hm2
        cases hm2
    · rename_i v2
      simp
      apply (mem_ofList _ k (f v1 v2) hnodup).mp
      rw [List.mem_filterMap]
      exact ⟨(k, v1), (mem_toList m1 k v1).mpr h1, by simp [h2]⟩

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
    cases h2' : get? m2 k with
    | none =>
      have : (get? m2 k).isSome = true := (hdom k).mp (by simp [h1])
      simp [h2'] at this
    | some y => simp [hg1]

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
    cases h1' : get? m1 k with
    | none =>
      have : (get? m1 k).isSome = true := (hdom k).mpr (by simp [h2])
      simp [h1'] at this
    | some x => simp [hg2]

/-- Insert distributes over zipWith. -/
theorem zipWith_insert [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') (i : K) (x : V) (y : V') :
    FiniteMap.zipWith f (insert m1 i x) (insert m2 i y) =
    insert (FiniteMap.zipWith f m1 m2) i (f x y) := by
  apply ext
  intro k
  by_cases h : k = i
  · subst h
    simp only [get?_insert_eq rfl, get?_zipWith]
  · have h' : i ≠ k := Ne.symm h
    simp only [get?_zipWith, get?_insert_ne h']

theorem zipWith_delete [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') (i : K) :
    FiniteMap.zipWith f (delete m1 i) (delete m2 i) =
    delete (FiniteMap.zipWith f m1 m2) i := by
  apply ext
  intro k
  by_cases h : k = i
  · subst h
    simp only [get?_delete_eq rfl, get?_zipWith]
  · have h' : i ≠ k := Ne.symm h
    simp only [get?_zipWith, get?_delete_ne h']

theorem zipWith_comm [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') :
    FiniteMap.zipWith (fun x y => f y x) m2 m1 = FiniteMap.zipWith f m1 m2 := by
  apply ext
  intro k
  rw [get?_zipWith, get?_zipWith]
  cases get? m1 k <;> cases get? m2 k <;> simp

theorem zip_comm [DecidableEq V] [DecidableEq V']
    (m1 : M V) (m2 : M V') :
    FiniteMap.zip m2 m1 = FiniteMap.map Prod.swap (FiniteMap.zip m1 m2) := by
  apply ext
  intro k
  unfold FiniteMap.zip
  rw [get?_map, get?_zipWith, get?_zipWith]
  cases get? m1 k <;> cases get? m2 k <;> simp [Prod.swap]

/-- Mapping with id is identity. -/
theorem map_id [DecidableEq V] (m : M V) :
    FiniteMap.map id m = m := by
  apply ext
  intro k
  rw [get?_map]
  cases get? m k <;> simp

/-- Mapping over a zip is the same as zipping the mapped maps. -/
theorem zip_map [DecidableEq V] [DecidableEq V'] {V'' V''' : Type _} [DecidableEq V''] [DecidableEq V''']
    (f : V → V'') (g : V' → V''') (m1 : M V) (m2 : M V') :
    FiniteMap.zip (FiniteMap.map f m1) (FiniteMap.map g m2) =
    FiniteMap.map (fun (x, y) => (f x, g y)) (FiniteMap.zip m1 m2) := by
  apply ext
  intro k
  unfold FiniteMap.zip
  rw [get?_zipWith, get?_map, get?_map, get?_map, get?_zipWith]
  cases h1 : get? m1 k <;> cases h2 : get? m2 k <;> simp

/-- Zipping fst and snd projections of a map recovers the original map. -/
theorem zip_fst_snd {V' : Type u'} [DecidableEq V] [DecidableEq V'] (m : M (V × V')) :
    FiniteMap.zip (FiniteMap.map Prod.fst m) (FiniteMap.map Prod.snd m) = m := by
  apply ext
  intro k
  unfold FiniteMap.zip
  rw [get?_zipWith, get?_map, get?_map]
  cases h : get? m k with
  | none => simp
  | some p => cases p; simp

theorem isSome_zipWith [DecidableEq V] [DecidableEq V'] [DecidableEq V'']
    (f : V → V' → V'') (m1 : M V) (m2 : M V') (k : K) :
    (get? (FiniteMap.zipWith f m1 m2) k).isSome ↔
    (get? m1 k).isSome ∧ (get? m2 k).isSome := by
  rw [get?_zipWith]
  cases get? m1 k <;> cases get? m2 k <;> simp [Option.isSome_some, Option.isSome_none]

/-- Zipping two empty maps yields an empty map. -/
theorem zip_empty [DecidableEq V] [DecidableEq V'] :
    FiniteMap.zip (∅ : M V) (∅ : M V') = ∅ := by
  apply LawfulPartialMap.ext
  intro k
  unfold FiniteMap.zip
  have h1 : get? (∅ : M V) k = none := get?_empty k
  have h2 : get? (∅ : M V') k = none := get?_empty k
  have h3 : get? (∅ : M (V × V')) k = none := get?_empty k
  rw [get?_zipWith, h1, h2, h3]

/-- Lookup in a zipped map. -/
theorem get?_zip [DecidableEq V] [DecidableEq V'] (m1 : M V) (m2 : M V') (k : K) :
    get? (FiniteMap.zip m1 m2) k =
      match get? m1 k, get? m2 k with
      | some v1, some v2 => some (v1, v2)
      | _, _ => none := by
  unfold FiniteMap.zip
  rw [get?_zipWith]

/-- Insert distributes over zip. -/
theorem zip_insert [DecidableEq V] [DecidableEq V']
    (m1 : M V) (m2 : M V') (i : K) (x : V) (y : V') :
    get? m1 i = none → get? m2 i = none →
    FiniteMap.zip (insert m1 i x) (insert m2 i y) =
    insert (FiniteMap.zip m1 m2) i (x, y) := by
  intro h1 h2
  unfold FiniteMap.zip
  exact zipWith_insert Prod.mk m1 m2 i x y

/-- Delete distributes over zip. -/
theorem zip_delete [DecidableEq V] [DecidableEq V']
    (m1 : M V) (m2 : M V') (i : K) :
    FiniteMap.zip (delete m1 i) (delete m2 i) =
    delete (FiniteMap.zip m1 m2) i := by
  unfold FiniteMap.zip
  exact zipWith_delete Prod.mk m1 m2 i

/-- Domain of a zipped map. -/
theorem isSome_zip [DecidableEq V] [DecidableEq V'] (m1 : M V) (m2 : M V') (k : K) :
    (get? (FiniteMap.zip m1 m2) k).isSome ↔
    (get? m1 k).isSome ∧ (get? m2 k).isSome := by
  unfold FiniteMap.zip
  exact isSome_zipWith Prod.mk m1 m2 k

/-- toList of a zipped map. -/
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

theorem induction_on {P : M V → Prop}
    (hemp : P ∅)
    (hins : ∀ i x m, get? m i = none → P m → P (insert m i x))
    (m : M V) : P m := by
  rw [(ofList_toList m).symm]
  have hnodup : (toList m).map Prod.fst |>.Nodup := nodup_toList_keys m
  generalize hgen : toList m = l
  rw [hgen] at hnodup
  clear hgen m
  induction l with
  | nil => rw [ofList_nil]; exact hemp
  | cons kv l ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rw [ofList_cons]
    apply hins
    · cases hget : get? (ofList l : M V) k
      · rfl
      · rename_i v'
        exfalso
        apply hnodup.1
        rw [List.mem_map]
        exact ⟨(k, v'), (mem_of_mem_ofList l k v' hget), rfl⟩
    · exact ih hnodup.2

theorem get?_union : ∀ (m₁ m₂ : M V) k,
    get? (m₁ ∪ m₂) k = (get? m₁ k).orElse (fun _ => get? m₂ k) := by
  intro m₁ m₂ k
  simp only [Union.union, FiniteMap.union]
  have h : ∀ (l : List (K × V)) (hnodup : (l.map Prod.fst).Nodup) (m : M V),
        get? (l.foldl (fun acc x => insert acc x.fst x.snd) m) k =
        (l.lookup k).orElse (fun _ => get? m k) := by
    intro l hnodup m
    induction l generalizing m with
    | nil => simp
    | cons p tail ih =>
      obtain ⟨k', v'⟩ := p
      rw [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.foldl, List.lookup]
      rw [ih hnodup.2, LawfulPartialMap.get?_insert]
      by_cases heq : k = k'
      · subst heq
        have : List.lookup k tail = none := by
          cases h : List.lookup k tail
          · rfl
          · rename_i v
            simp at hnodup
            have hmem : (k, v) ∈ tail := List.list_lookup_some_mem k v tail h
            exact absurd hmem (hnodup.1 v)
        simp [this]
      · have : (k == k') = false := by simp [heq]
        simp [this, Ne.symm heq]
  show get? ((toList m₁).foldl (fun acc x => insert acc x.fst x.snd) m₂) k = _
  rw [h (toList m₁) (nodup_toList_keys m₁) m₂]
  congr 1
  cases hlookup : (toList m₁).lookup k
  · cases hget : get? m₁ k
    · rfl
    · rename_i v
      have : (toList m₁).lookup k = some v :=
        List.list_mem_lookup_some k v _ (nodup_toList_keys m₁) (((toList_spec m₁).2 k v).mpr hget)
      cases this ▸ hlookup
  · rename_i v
    exact (((toList_spec m₁).2 k v).mp (List.list_lookup_some_mem k v _ hlookup)).symm

theorem get?_difference : ∀ (m₁ m₂ : M V) k,
    get? (m₁ \ m₂) k = if (get? m₂ k).isSome then none else get? m₁ k := by
  intro m₁ m₂ k
  simp only [SDiff.sdiff, FiniteMap.difference]
  split
  · rename_i h
    obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp h
    have : k ∉ (List.filter (fun x => (get? m₂ x.fst).isNone) (toList m₁)).map Prod.fst := by
      intro hmem
      obtain ⟨⟨k', v'⟩, hmem_filter, rfl⟩ := List.mem_map.mp hmem
      simp [List.mem_filter, hv₂] at hmem_filter
    cases hget : get? (ofList (List.filter (fun x => (get? m₂ x.fst).isNone) (toList m₁)) : M V) k
    · rfl
    · exact absurd (List.mem_map_of_mem (mem_of_mem_ofList _ k _ hget)) this
  · rename_i h
    have hm₂ : get? m₂ k = none := by
      cases h' : get? m₂ k <;> simp_all [Option.isSome_some]
    cases hm₁ : get? m₁ k
    · cases hget : get? (ofList (List.filter (fun x => (get? m₂ x.fst).isNone) (toList m₁)) : M V) k
      · rfl
      · have := (mem_toList m₁ k _).mp (List.mem_filter.mp (mem_of_mem_ofList _ k _ hget)).1
        rw [hm₁] at this; cases this
    · rename_i v₁
      apply mem_ofList_of_mem _ k v₁
      · apply List.Nodup.map_of_injective ((nodup_toList m₁).filter _)
        intro ⟨k₁, v₁⟩ ⟨k₂, v₂⟩ h₁ h₂ heq; simp at heq
        have hv₁ := (mem_toList m₁ k₁ v₁).mp (List.mem_filter.mp h₁).1
        have hv₂ := (mem_toList m₁ k₂ v₂).mp (List.mem_filter.mp h₂).1
        ext <;> simp [heq]
        rw [← heq] at hv₂; rw [hv₁] at hv₂; cases hv₂; rfl
      · exact List.mem_filter.mpr ⟨(mem_toList m₁ k v₁).mpr hm₁, by simp [hm₂]⟩

theorem get?_union_none (m1 m2 : M V) (i : K) :
    get? (m1 ∪ m2) i = none ↔ get? m1 i = none ∧ get? m2 i = none := by
  rw [get?_union]
  cases h1 : get? m1 i <;> cases h2 : get? m2 i <;> simp [Option.orElse]

theorem union_insert_left (m1 m2 : M V) (i : K) (x : V) :
    get? (insert (m1 ∪ m2) i x) = get? (insert m1 i x ∪ m2) := by
  funext k
  by_cases hik : i = k
  · subst hik
    simp [get?_insert_eq rfl, get?_union]
  · simp [get?_insert_ne hik, get?_union]

end FiniteMapLaws

namespace FiniteMap

variable {K : Type v} {M : Type u → _}  [FiniteMap K M]

theorem disjoint_empty_right [DecidableEq K] [FiniteMapLaws K M] (m : M V) : m ##ₘ (∅ : M V) :=
  PartialMap.disjoint_comm (LawfulPartialMap.disjoint_empty_left (K:= K) m)

/-- `m₂` and `m₁ \ m₂` are disjoint. -/
theorem disjoint_difference_right [DecidableEq K] [FiniteMapLaws K M] [FiniteMapLawsSelf K M]
    (m₁ m₂ : M V) : m₂ ##ₘ (m₁ \ m₂) := by
  intro k ⟨h_in_m2, h_in_diff⟩
  rw [FiniteMapLaws.get?_difference] at h_in_diff
  simp only [h_in_m2, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at h_in_diff

theorem union_difference_cancel [DecidableEq K] [FiniteMapLaws K M] [FiniteMapLawsSelf K M]
    (m₁ m₂ : M V) (hsub : m₂ ⊆ m₁) : m₂ ∪ (m₁ \ m₂) = m₁ := by
  apply LawfulPartialMap.ext
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
