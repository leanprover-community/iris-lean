/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Std.PartialMap

/-! ## Generic stores and heaps -/

section Store

open Iris Std PartialMap


-- /-- The type `T` can store and retrieve values of type `V` using keys of type `K`. -/
-- class Store (T : Type _) (K V : outParam (Type _)) where
--   get : T → K → V
--   set : T → K → V → T
--   get_set_eq {t k k' v} : k = k' → get (set t k v) k' = v
--   get_set_ne {t k k' v} : k ≠ k' → get (set t k v) k' = get t k'
-- export Store (get set get_set_eq get_set_ne)
--
-- open Classical in
-- theorem Store.get_set [Store T K V] {t : T} {k k' : K} {v : V} :
--     get (set t k v) k' = if k = k' then v else get t k' := by
--   by_cases h : k = k'
--   · rw [if_pos h, get_set_eq h]
--   · rw [if_neg h, get_set_ne h]

-- /-- An index-dependent predicate holds at every member of the store. -/
-- def Store.all [Store T K V] (P : K → V → Prop) : T → Prop :=
--   fun t => ∀ k, P k (get t k)


/-- RepFunMap: The map T is capable of representing all partial functions out of K. -/
class RepFunMap (T : Type _ → Type _) (K : outParam (Type _)) [PartialMap T K] where
  of_fun : (K → Option V) → T V
  get_of_fun (f : K → Option V) (k : K) : get? (of_fun f) k = f k
export RepFunMap (of_fun get_of_fun)

/-- IsoFunStore: The map T is isomorphic to the type of functions out of `K`. In other words,
    equality of T is the same as equality of functions, so the CMRA on these partial functions
    is leibniz. -/
class IsoFunMap (T : Type _  → Type _) (K : outParam (Type _)) [PartialMap T K]
  extends RepFunMap T K where
  of_fun_get {t : T V} : of_fun (get? t) = t
export IsoFunMap (of_fun_get)

theorem IsoFunStore.ext [PartialMap T K] [IsoFunMap T K] {t1 t2 : T V}
    (H : ∀ k, get? t1 k = get? t2 k) : t1 = t2 := by
  rw [← of_fun_get (t := t1), ← of_fun_get (t := t2)]
  simp only [funext H]

-- theorem IsoFunStore.store_eq_of_Equiv [Store T K V] [IsoFunStore T K V] {t1 t2 : T}
--     (H : Store.Equiv t1 t2) : t1 = t2 := IsoFunStore.ext <| congrFun H

-- /-- Stores of type T1 can be coerced to stores of type T2. -/
-- class HasStoreMap (T1 T2 : Type _) (K V1 V2 : outParam (Type _)) [Store T1 K V1] [Store T2 K V2] where
--   /-- Map a function that depends on the element across the entire structure  -/
--   dmap (f : K → V1 → V2) : T1 → T2
--   get_dmap : get (dmap f t) k = f k (get t k)
-- export HasStoreMap (dmap get_dmap)
--
-- def HasStoreMap.map (f : V1 → V2) [Store T1 K V1] [Store T2 K V2] [HasStoreMap T1 T2 K V1 V2] : T1 → T2 :=
--   HasStoreMap.dmap (fun _ => f)

end Store

section Heap

open Iris.Std

-- /-- Map between heaps that preserves non-allocations. -/
-- class HasHeapMap (T1 T2 : Type _) (K V1 V2 : outParam (Type _))
--    [Store T1 K (Option V1)] [Store T2 K (Option V2)] where
--   hhmap (f : K → V1 → Option V2) : T1 → T2
--   hhmap_get (f : K → V1 → Option V2) : get (hhmap f t) k = (get t k).bind (f k)
-- export HasHeapMap (hhmap hhmap_get)

/-- Heap extends PartialMap with heap-specific operations for separation logic.
    The heap stores optional values, where `none` represents unallocated locations. -/
class Heap (M : Type _ → Type _) (K : outParam (Type _)) extends LawfulPartialMap M K where
  /-- Merge two heaps with a combining operation. -/
  merge (op : K → V1 → V2 → V) : M V1 → M V2 → M V
  /-- get? on merge combines values using Option.merge. -/
  get?_merge : get? (merge op m₁ m₂) k = Option.merge (op k) (get? m₁ k) (get? m₂ k)
export Heap (merge get?_merge)

-- Changed to: singleton
-- /-- The heap of a single point (singleton with optional value). -/
-- def Heap.point [Heap K M] (k : K) (v : Option V) : M V :=
--   match v with
--   | some v' => PartialMap.insert empty k v'
--   | none => empty

/-- The domain of a heap is the set of keys that map to .some values. -/
def Heap.dom [Heap M K] (m : M V) : K → Prop := fun k => (get? m k).isSome

-- Should this be part of the typeclass, or should we use this derived one?
@[simp] def Heap.union [Heap M K] : M V → M V → M V := merge (fun _ v _ => v)

/-- An AllocHeap is a heap which can allocate elements under some condition. -/
class AllocHeap (M : Type _ → Type _) (K : outParam (Type _)) extends Heap M K where
  notFull : M V → Prop
  fresh {m : M V} : notFull m → K
  get?_fresh {m : M V} {H : notFull m} : get? m (fresh H) = none
export AllocHeap (notFull fresh get?_fresh)

/-- An UnboundedHeap is a heap which can allocate an unbounded number of elements starting at empty. -/
class UnboundedHeap (M : Type _ → Type _) (K : outParam (Type _)) extends AllocHeap M K where
  notFull_empty : notFull (empty : M V)
  notFull_insert_fresh {m : M V} {H : notFull m} : notFull (insert m (fresh H) v)
export UnboundedHeap (notFull_empty notFull_insert_fresh)

end Heap
