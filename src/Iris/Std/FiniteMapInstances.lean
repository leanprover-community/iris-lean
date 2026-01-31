/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Std.FiniteMap
import Iris.Std.List
import Std

/-! ## FiniteMap Instance for Std.ExtTreeMap

This file instantiates the abstract finite map interface `Iris.Std.FiniteMap` with Lean's `Std.ExtTreeMap`.
ExtTreeMap provides both PartialMap (via get?/insert/delete) and FiniteMap (via toList/ofList) operations.
-/
namespace Iris.Std

/-- PartialMap instance for Std.ExtTreeMap. -/
instance {K : Type u} [Ord K] [Std.TransCmp (α := K) compare] [Std.LawfulEqCmp (α := K) compare] [DecidableEq K]:
    PartialMap K (Std.ExtTreeMap K) where
  get? m k := m.get? k
  insert m k v := m.insert k v
  delete m k := m.erase k
  empty := Std.ExtTreeMap.empty

/-- FiniteMap instance for Std.ExtTreeMap (extends PartialMap). -/
instance {K : Type u} [Ord K] [Std.TransCmp (α := K) compare] [Std.LawfulEqCmp (α := K) compare] [DecidableEq K]:
    FiniteMap K (Std.ExtTreeMap K) where
  toList m := m.toList
  ofList l := Std.ExtTreeMap.ofList l.reverse
  fold := fun f init m => m.foldr f init

namespace FiniteMapInst

variable {K : Type _} [Ord K] [Std.TransCmp (α := K) compare] [Std.LawfulEqCmp (α := K) compare] [DecidableEq K]

/-- The PartialMapLaws instance for ExtTreeMap. -/
instance : PartialMapLaws K (Std.ExtTreeMap K) where
  ext := by
    intro m₁ m₂ h
    apply Std.ExtTreeMap.ext_getElem?

  get?_empty := by
    intro k
    simp [PartialMap.get?]

  get?_insert_same := by
    intro m k v
    simp [PartialMap.get?, PartialMap.insert]

  get?_insert_ne := by
    intro m _ k k' h
    simp [PartialMap.get?, PartialMap.insert, Std.ExtTreeMap.getElem?_insert]
    intro h h'
    trivial

  get?_delete_same := by
    intro m k
    simp [PartialMap.get?, PartialMap.delete]

  get?_delete_ne := by
    intro m k k' h h'
    simp [PartialMap.get?, PartialMap.delete, Std.ExtTreeMap.getElem?_erase]
    intro h h'
    trivial

/-- The FiniteMapLaws instance for ExtTreeMap (extends PartialMapLaws). -/
instance : FiniteMapLaws K (Std.ExtTreeMap K) where
  ofList_nil := by
    simp [FiniteMap.ofList]

  ofList_cons := by
    intro k v l l_1
    simp only [FiniteMap.ofList, PartialMap.insert]
    rw [List.reverse_cons, Std.ExtTreeMap.ofList_eq_insertMany_empty, Std.ExtTreeMap.ofList_eq_insertMany_empty, Std.ExtTreeMap.insertMany_append, Std.ExtTreeMap.insertMany_list_singleton]

  toList_spec := by
    intro V m
    constructor
    · simp only [FiniteMap.toList]
      have hdistinct : m.toList.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) :=
        Std.ExtTreeMap.distinct_keys_toList
      apply hdistinct.imp
      intro a b hne heq
      subst heq
      have : compare a.1 a.1 = .eq := Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl
      exact hne this
    · intro i x
      simp only [FiniteMap.toList, PartialMap.get?]
      exact Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some


/-- The FiniteMapLawsSelf instance for ExtTreeMap. -/
instance : FiniteMapLawsSelf K (Std.ExtTreeMap K) where
  toList_filterMap := by
    intro V m f
    haveI : DecidableEq V := Classical.typeDecidableEq V
    simp only [FiniteMap.toList, FiniteMap.filterMap, FiniteMap.ofList]

    obtain H := FiniteMapLaws.toList_ofList (M := (Std.ExtTreeMap K)) (K := K) (V := V) (l := (List.filterMap (fun kv => Option.map (fun x => (kv.fst, x)) (f kv.snd)) m.toList))

    simp only [FiniteMap.toList, FiniteMap.ofList] at H
    apply H
    rw [List.map_filterMap]
    have eq_goal : (List.filterMap (fun x => Option.map Prod.fst (Option.map (fun x_1 => (x.fst, x_1)) (f x.snd))) m.toList) =
                   (List.filterMap (fun x => Option.map (fun _ => x.fst) (f x.snd)) m.toList) := by
      congr 1
      ext x
      rw [Option.map_map]
      rfl
    rw [eq_goal]
    have nodup_keys : (m.toList.map Prod.fst).Nodup := by
      rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
      exact Std.ExtTreeMap.nodup_keys
    exact List.nodup_filterMap_of_nodup_keys m.toList f nodup_keys

  toList_filter := by
    intro V m φ
    simp [FiniteMap.toList, FiniteMap.filter, FiniteMap.ofList]
    haveI : DecidableEq V := Classical.typeDecidableEq V
    obtain H := FiniteMapLaws.toList_ofList (M := (Std.ExtTreeMap K)) (K := K) (V := V) (l := (List.filter (fun x => φ x.fst x.snd) m.toList))

    simp only [FiniteMap.toList, FiniteMap.ofList] at H
    apply H

    have nodup_keys : (m.toList.map Prod.fst).Nodup := by
      rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
      exact Std.ExtTreeMap.nodup_keys

    exact List.nodup_map_fst_filter m.toList (fun x => φ x.fst x.snd) nodup_keys

/-- The FiniteMapKmapLaws instance for ExtTreeMap with key type transformation. -/
instance {K' : Type _} [Ord K'] [Std.TransCmp (α := K') compare] [Std.LawfulEqCmp (α := K') compare] [DecidableEq K'] :
    FiniteMapKmapLaws K K' (Std.ExtTreeMap K) (Std.ExtTreeMap K') where
  toList_kmap := by
    intro V f m hinj
    simp [FiniteMap.toList, FiniteMap.kmap, FiniteMap.ofList]
    haveI : DecidableEq V := Classical.typeDecidableEq V
    obtain H := FiniteMapLaws.toList_ofList (M := (Std.ExtTreeMap K')) (K := K') (V := V) (l := (List.map (fun x => (f x.fst, x.snd)) m.toList))

    simp only [FiniteMap.toList, FiniteMap.ofList] at H
    apply H

    have nodup_keys : (m.toList.map Prod.fst).Nodup := by
      rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
      exact Std.ExtTreeMap.nodup_keys

    exact List.nodup_map_fst_map_injective m.toList f hinj nodup_keys

/-- The FiniteMapSeqLaws instance for ExtTreeMap with Nat keys. -/
instance [Std.TransCmp (α := Nat) compare] [Std.LawfulEqCmp (α := Nat) compare] :
    FiniteMapSeqLaws (Std.ExtTreeMap Nat) where
  toList_map_seq := by
    intro V start l
    simp [FiniteMap.toList, FiniteMap.map_seq, FiniteMap.ofList]
    haveI : DecidableEq V := Classical.typeDecidableEq V

    have heq : List.mapIdx (fun i v => (start + i, v)) l = (List.range' start l.length).zip l :=
      List.mapIdx_add_eq_zip_range' start l

    rw [heq]

    obtain H := FiniteMapLaws.toList_ofList (M := (Std.ExtTreeMap Nat)) (K := Nat) (V := V) (l := ((List.range' start l.length).zip l))

    simp only [FiniteMap.toList, FiniteMap.ofList] at H
    apply H

    -- The keys from range' are all distinct
    rw [← heq]
    exact List.nodup_map_fst_mapIdx_add start l

end FiniteMapInst

end Iris.Std
