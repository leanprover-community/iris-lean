/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Std.PartialMap

/-! ## Generic stores and heaps -/

section Store

/-- The type `T` can store and retrieve values of type `V` using keys of type `K`. -/
class Store (T : Type _) (K V : outParam (Type _)) where
  get : T → K → V
  set : T → K → V → T
  get_set_eq {t k k' v} : k = k' → get (set t k v) k' = v
  get_set_ne {t k k' v} : k ≠ k' → get (set t k v) k' = get t k'
export Store (get set get_set_eq get_set_ne)

open Classical in
theorem Store.get_set [Store T K V] {t : T} {k k' : K} {v : V} :
    get (set t k v) k' = if k = k' then v else get t k' := by
  by_cases h : k = k'
  · rw [if_pos h, get_set_eq h]
  · rw [if_neg h, get_set_ne h]

/-- An index-dependent predicate holds at every member of the store. -/
def Store.all [Store T K V] (P : K → V → Prop) : T → Prop :=
  fun t => ∀ k, P k (get t k)

/-- Two Stores are pointwise equivalent. -/
@[simp] def Store.Equiv [Store T K V] (t1 t2 : T) : Prop := get t1 = get t2

instance Store.Equiv_trans [Store T K V] : Trans Equiv (Equiv (T := T)) Equiv := ⟨by simp_all⟩

/-- RepFunStore: The type T can represent all functions that satisfy Rep.
For instance, this holds with `rep _ = True` when `T = K → V`. On the other hand, when
`T = list (K × Option V)` representing a partial function with an association list, this holds
when `rep f` is the predicate that says `f` has finite domain. -/
class RepFunStore (T : Type _) (K V : outParam (Type _)) [Store T K V] where
  rep : (K → V) → Prop
  rep_get (t : T) : rep (get t)
  of_fun : { f : K → V // rep f } → T
  get_of_fun : get (of_fun f) = f
export RepFunStore (rep rep_get of_fun get_of_fun)

/-- IsoFunStore: The type T is isomorphic the type of functions `{f : Rep f}`, or in other words,
equality of T is the same as equality of `{f : Rep f}`. -/
class IsoFunStore (T : Type _) (K V : outParam (Type _)) [Store T K V] extends RepFunStore T K V where
  of_fun_get {t : T} : of_fun ⟨get t, rep_get t⟩ = t
export IsoFunStore (of_fun_get)

theorem IsoFunStore.ext [Store T K V] [IsoFunStore T K V] {t1 t2 : T}
    (H : ∀ k, get t1 k = get t2 k) : t1 = t2 := by
  rw [← of_fun_get (t := t1), ← of_fun_get (t := t2)]
  simp only [funext H]

theorem IsoFunStore.store_eq_of_Equiv [Store T K V] [IsoFunStore T K V] {t1 t2 : T}
    (H : Store.Equiv t1 t2) : t1 = t2 := IsoFunStore.ext <| congrFun H

/-- Stores of type T1 can be coerced to stores of type T2. -/
class HasStoreMap (T1 T2 : Type _) (K V1 V2 : outParam (Type _)) [Store T1 K V1] [Store T2 K V2] where
  /-- Map a function that depends on the element across the entire structure  -/
  dmap (f : K → V1 → V2) : T1 → T2
  get_dmap : get (dmap f t) k = f k (get t k)
export HasStoreMap (dmap get_dmap)

def HasStoreMap.map (f : V1 → V2) [Store T1 K V1] [Store T2 K V2] [HasStoreMap T1 T2 K V1 V2] : T1 → T2 :=
  HasStoreMap.dmap (fun _ => f)

end Store

section Heap

open Iris.Std

/-- Map between heaps that preserves non-allocations. -/
class HasHeapMap (T1 T2 : Type _) (K V1 V2 : outParam (Type _))
   [Store T1 K (Option V1)] [Store T2 K (Option V2)] where
  hhmap (f : K → V1 → Option V2) : T1 → T2
  hhmap_get (f : K → V1 → Option V2) : get (hhmap f t) k = (get t k).bind (f k)
export HasHeapMap (hhmap hhmap_get)

/-- Heap extends PartialMap with heap-specific operations for separation logic.
    The heap stores optional values, where `none` represents unallocated locations. -/
class Heap (K : outParam (Type _)) (M : Type _ → Type _) extends PartialMap K M where
  /-- Map operation that can optionally remove entries. -/
  hmap (f : K → V → Option V) : M V → M V
  /-- Merge two heaps with a combining operation. -/
  merge (op : V → V → V) : M V → M V → M V
  /-- get? on hmap applies the function to present values. -/
  get?_hmap : get? (hmap f m) k = (get? m k).bind (f k)
  /-- get? on merge combines values using Option.merge. -/
  get?_merge : get? (merge op m₁ m₂) k = Option.merge op (get? m₁ k) (get? m₂ k)

export Heap (hmap merge get?_hmap get?_merge)

theorem hmap_alloc [Heap K M] {m : M V} (H : get? m k = some v) : get? (hmap f m) k = f k v := by
  simp [get?_hmap, H]

theorem hmap_unalloc [Heap K M] {m : M V} (H : get? m k = none) : get? (hmap f m) k = none := by
  simp [get?_hmap, H]

/-- The heap of a single point (singleton with optional value). -/
def Heap.point [Heap K M] (k : K) (v : Option V) : M V :=
  match v with
  | some v' => insert empty k v'
  | none => empty

/-- The domain of a heap is the set of keys that map to .some values. -/
def Heap.dom [Heap K M] (m : M V) : K → Prop := fun k => (get? m k).isSome

@[simp] def Heap.union [Heap K M] : M V → M V → M V := merge (fun v _ => v)

theorem Heap.point_get?_eq [Heap K M] [DecidableEq K] [PartialMapLaws K M] (H : k = k') : get? (point k (some v) : M V) k' = some v := by
  rw [point, H]
  exact PartialMapLaws.get?_insert_same _ _ _

theorem Heap.point_get?_ne [Heap K M] [DecidableEq K] [PartialMapLaws K M] (H : k ≠ k') :
    get? (point k (some v) : M V) k' = none := by
  rw [point]
  rw [PartialMapLaws.get?_insert_ne _ _ _ _ H]
  exact PartialMapLaws.get?_empty k'

open Classical in
theorem Heap.get?_point [Heap K M] [DecidableEq K] [PartialMapLaws K M] {k k' : K} {v : V} :
    get? (point k (some v) : M V) k' = if k = k' then some v else none := by
  by_cases h : k = k'
  · rw [if_pos h, h]; exact Heap.point_get?_eq rfl
  · rw [if_neg h]; exact Heap.point_get?_ne h

/-- An AllocHeap is a heap which can allocate elements under some condition. -/
class AllocHeap (K : outParam (Type _)) (M : Type _ → Type _) extends Heap K M where
  notFull : M V → Prop
  fresh {m : M V} : notFull m → K
  get?_fresh {m : M V} {H : notFull m} : get? m (fresh H) = none
export AllocHeap (notFull fresh get?_fresh)

/-- An UnboundedHeap is a heap which can allocate an unbounded number of elements starting at empty. -/
class UnboundedHeap (K : outParam (Type _)) (M : Type _ → Type _) extends AllocHeap K M where
  notFull_empty : notFull (empty : M V)
  notFull_insert_fresh {m : M V} {H : notFull m} : notFull (insert m (fresh H) v)
export UnboundedHeap (notFull_empty notFull_insert_fresh)

end Heap
