/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu
-/

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

/-- Map between heaps that preserves non-allocations. -/
class HasHeapMap (T1 T2 : Type _) (K V1 V2 : outParam (Type _))
   [Store T1 K (Option V1)] [Store T2 K (Option V2)] where
  hhmap (f : K → V1 → Option V2) : T1 → T2
  hhmap_get (f : K → V1 → Option V2) : get (hhmap f t) k = (get t k).bind (f k)
export HasHeapMap (hhmap hhmap_get)

theorem hhmap_compose [Store T1 K (Option V1)] [Store T2 K (Option V2)] [Store T3 K (Option V3)] [HasHeapMap T1 T2 K V1 V2] [HasHeapMap T2 T3 K V2 V3] [HasHeapMap T1 T3 K V1 V3] (f : K → V1 → Option V2) (g : K → V2 → Option V3) (m : T1) :
    Store.Equiv (hhmap g ((hhmap f m) : T2) : T3)  (hhmap (fun k a => (f k a) >>= (g k)) m) := by
  ext
  constructor <;> simp [hhmap_get] <;> intro h <;> rw [← h]
  · apply Eq.symm (Option.bind_assoc (Store.get m _) (f _) (g _))
  · (expose_names; exact Option.bind_assoc (Store.get m x) (f x) (g x))

class Heap (T : Type _) (K V : outParam (Type _)) extends Store T K (Option V) where
  empty : T
  hmap (f : K → V → Option V) : T → T
  merge (op : V → V → V) : T → T → T
  get_empty : get empty k = none
  get_hmap : get (hmap f t) k = (get t k).bind (f k)
  get_merge : get (merge op t1 t2) k = Option.merge op (get t1 k) (get t2 k)
export Heap (empty hmap merge get_empty get_hmap get_merge)

theorem hmap_alloc [Heap T K V] {t : T} (H : get t k = some v) : get (hmap f t) k = f k v := by
  simp [get_hmap, H]

theorem hmap_unalloc [Heap T K V] {t : T} (H : get t k = none) : get (hmap f t) k = none := by
  simp [get_hmap, H]

/-- The heap of a single point -/
def Heap.point [Heap T K V] (k : K) (v : Option V) : T := set empty k v

/-- Delete an element from a heap by setting its value to .none -/
def Heap.delete [Heap T K V] (t : T) (k : K) : T := set t k none

/-- The domain of a heap is the set of keys that map to .some values. -/
def Heap.dom [Heap T K V] (t : T) : K → Prop := fun k => (get t k).isSome

@[simp] def Heap.union [Heap T K V] : T → T → T := merge (fun v _ => v)

theorem Heap.point_get_eq [Heap T K V] (H : k = k') : get (point k v : T) k' = v := by
  rw [point, get_set_eq H]

theorem Heap.point_get_ne [Heap T K V] (H : k ≠ k') : get (point k v : T) k' = none := by
  rw [point, get_set_ne H, get_empty]

open Classical in
theorem Heap.get_point [Heap T K V] {k k' : K} {v : Option V} :
    get (point k v : T) k' = if k = k' then v else .none := by
  by_cases h : k = k'
  · rw [if_pos h, point_get_eq h]
  · rw [if_neg h, point_get_ne h]

/-- An AllocHeap is a heap which can allocate elements under some condition. -/
class AllocHeap (T : Type _) (K V : outParam (Type _)) extends Heap T K V where
  notFull : T → Prop
  fresh {t : T} : notFull t → K
  get_fresh {H : notFull t} : get t (fresh H) = none
export AllocHeap (notFull fresh get_fresh)

/-- An UnboundedHeap is a heap which can allocate an unbounded number of elements starting at empty. -/
class UnboundedHeap (T : Type _) (K V : outParam (Type _)) extends AllocHeap T K V where
  notFull_empty : notFull (empty : T)
  notFull_set_fresh {H : notFull t} : notFull (set t (fresh H) v)
export UnboundedHeap (notFull_empty notFull_set_fresh)

end Heap
