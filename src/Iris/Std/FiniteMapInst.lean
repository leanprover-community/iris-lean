/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Std.FiniteMap
import Std

/-! ## FiniteMap Instance for Std.ExtTreeMap

This file instantiates the abstract finite map interface `Iris.Std.FiniteMap` with Lean's `Std.ExtTreeMap`,
which is a balanced binary search tree implementation.

`Std.ExtTreeMap` requires:
- A type `K` with decidable equality and an `Ord` instance
- A comparison function `cmp : K → K → Ordering` (defaults to `compare` from `Ord`)
-/
namespace Iris.Std

/-- Instance of FiniteMap for Std.ExtTreeMap. -/
instance {K : Type _} [Ord K] [Std.TransCmp (α := K) compare] [Std.LawfulEqCmp (α := K) compare] [DecidableEq K]:
    FiniteMap (Std.ExtTreeMap K) K where
  get? m k := m.get? k
  insert m k v := m.insert k v
  delete m k := m.erase k
  empty := Std.ExtTreeMap.empty
  toList m := m.toList
  ofList l := Std.ExtTreeMap.ofList l
  fold := sorry

namespace FiniteMapInst

variable {K : Type _} [Ord K] [Std.TransCmp (α := K) compare] [Std.LawfulEqCmp (α := K) compare] [DecidableEq K]

/-- The FiniteMapLaws instance for ExtTreeMap. -/
instance : FiniteMapLaws (Std.ExtTreeMap K) K where
  map_eq := by
    intro m₁ m₂ h
    apply Std.ExtTreeMap.ext_getElem?

  lookup_empty := by
    intro k
    simp [FiniteMap.get?]

  lookup_insert_eq := by
    intro m k v
    simp [FiniteMap.get?, FiniteMap.insert]

  lookup_insert_ne := by
    intro m _ k k' h
    simp [FiniteMap.get?, FiniteMap.insert, Std.ExtTreeMap.getElem?_insert]
    intro h h'
    trivial

  lookup_delete_eq := by
    intro m k
    simp [FiniteMap.get?, FiniteMap.delete]

  lookup_delete_ne := by
    intro m k k' h h'
    simp [FiniteMap.get?, FiniteMap.delete, Std.ExtTreeMap.getElem?_erase]
    intro h h'
    trivial

  lookup_union := by
    intro m₁ m₂ k
    simp [FiniteMap.get?]
    sorry

  lookup_difference := by
    intro m₁ m₂ k
    simp [FiniteMap.get?]
    sorry

  ofList_nil := by
    simp [FiniteMap.ofList]

  ofList_cons := by
    intro k v l
    simp only [FiniteMap.ofList, FiniteMap.insert]
    sorry

  fold_empty := by sorry

  fold_fmap_ind := by sorry

/-- The FiniteMapLawsSelf instance for ExtTreeMap. -/
instance : FiniteMapLawsSelf (Std.ExtTreeMap K) K where
  toList_filterMap := by
    intro m f
    simp [FiniteMap.toList, FiniteMap.filterMap, FiniteMap.ofList]
    sorry

  toList_filter := by
    intro m φ
    simp [FiniteMap.toList, FiniteMap.filter, FiniteMap.ofList]
    sorry

  toList_union_disjoint := by
    intro m₁ m₂ h
    simp [FiniteMap.toList]
    sorry

  toList_difference := by
    intro m₁ m₂
    simp [FiniteMap.toList]
    sorry

/-- The FiniteMapKmapLaws instance for ExtTreeMap with key type transformation. -/
instance {K' : Type _} [Ord K'] [Std.TransCmp (α := K') compare] [Std.LawfulEqCmp (α := K') compare] [DecidableEq K'] :
    FiniteMapKmapLaws (Std.ExtTreeMap K) (Std.ExtTreeMap K') K K' where
  toList_kmap := by
    intro f m hinj
    simp [FiniteMap.toList, FiniteMap.kmap, FiniteMap.ofList]
    sorry

/-- The FiniteMapSeqLaws instance for ExtTreeMap with Nat keys. -/
instance {V' : Type _} [Std.TransCmp (α := Nat) compare] [Std.LawfulEqCmp (α := Nat) compare] :
    FiniteMapSeqLaws (Std.ExtTreeMap Nat) where
  toList_map_seq := by
    intro start l
    simp [FiniteMap.toList, FiniteMap.map_seq, FiniteMap.ofList]
    sorry

end FiniteMapInst

end Iris.Std
