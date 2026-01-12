/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Std.FiniteMap
import Iris.Std.List
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
instance {K : Type u} [Ord K] [Std.TransCmp (α := K) compare] [Std.LawfulEqCmp (α := K) compare] [DecidableEq K]:
    FiniteMap K (Std.ExtTreeMap K) where
  get? m k := m.get? k
  insert m k v := m.insert k v
  delete m k := m.erase k
  empty := Std.ExtTreeMap.empty
  toList m := m.toList
  ofList l := Std.ExtTreeMap.ofList l.reverse
  fold := fun f init m => m.foldr f init

namespace FiniteMapInst

variable {K : Type _} [Ord K] [Std.TransCmp (α := K) compare] [Std.LawfulEqCmp (α := K) compare] [DecidableEq K]

/-- The FiniteMapLaws instance for ExtTreeMap. -/
instance : FiniteMapLaws K (Std.ExtTreeMap K) where
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
    intro V m₁ m₂ k
    simp only [FiniteMap.get?, Union.union, FiniteMap.union]
    have h : ∀ (l : List (K × V)) (hnodup : (l.map Prod.fst).Nodup) (m : Std.ExtTreeMap K V compare),
        (l.foldl (fun (acc: Std.ExtTreeMap K V compare) (x : K × V) => (Std.ExtTreeMap.insert acc x.fst x.snd: Std.ExtTreeMap K V compare)) m).get? k =
        (l.lookup k).orElse (fun _ => m.get? k) := by
      intro l hnodup m
      induction l generalizing m with
      | nil =>
        simp [List.foldl, List.lookup, Option.orElse]
      | cons p tail ih =>
        obtain ⟨k', v'⟩ := p
        simp only [List.foldl]
        rw [List.map_cons, List.nodup_cons] at hnodup
        rw [ih hnodup.2]
        simp only [List.lookup]
        by_cases h : k = k'
        · subst h
          simp
          have hlookup_none : List.lookup k tail = none := by
            cases hlookup : List.lookup k tail with
            | none => rfl
            | some v =>
              exfalso
              have hmem : (k, v) ∈ tail := Iris.Std.list_lookup_some_mem k v tail hlookup
              have : k ∈ tail.map Prod.fst := by
                simp
                exact ⟨v, hmem⟩
              exact hnodup.1 this
          simp [hlookup_none]
        · simp [Std.ExtTreeMap.getElem?_insert]
          have heq : (k == k') = false := by
            simp
            intro heq_k_k'
            exact h heq_k_k'
          rw [heq]
          have : k' ≠ k := fun heq_contr => h heq_contr.symm
          simp [if_neg this]

    have nodup : (m₁.toList.map Prod.fst).Nodup := by
      rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
      exact Std.ExtTreeMap.nodup_keys
    show (m₁.toList.foldl (fun acc x => acc.insert x.fst x.snd) m₂).get? k = _
    rw [h m₁.toList nodup m₂]

    congr 1
    cases hlookup : m₁.toList.lookup k with
    | none =>
      cases hget : m₁.get? k with
      | none => rfl
      | some v =>
        exfalso
        have hmem : (k, v) ∈ m₁.toList :=
          Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hget
        have : m₁.toList.lookup k = some v :=
          Iris.Std.list_mem_lookup_some k v _ nodup hmem
        rw [hlookup] at this
        contradiction
    | some v =>
      have hmem : (k, v) ∈ m₁.toList :=
        Iris.Std.list_lookup_some_mem k v _ hlookup
      have : m₁.get? k = some v :=
        Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
      rw [this]

  lookup_difference := by
    intro V m₁ m₂ k
    simp only [FiniteMap.get?, SDiff.sdiff, FiniteMap.difference, FiniteMap.ofList, FiniteMap.toList]
    rw [Std.ExtTreeMap.ofList_eq_insertMany_empty]
    by_cases hm₂ : m₂.get? k = none
    · simp only [hm₂, Option.isSome_none]
      simp
      cases hm₁ : m₁.get? k with
      | none =>
        have hk_not_in : k ∉ ((List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList).reverse.map Prod.fst) := by
          intro hmem
          rw [List.mem_map] at hmem
          obtain ⟨⟨k', v'⟩, hmem_rev, hkeq⟩ := hmem
          simp at hkeq
          subst hkeq
          have hmem_filter : (k', v') ∈ List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList :=
            List.mem_reverse.mp hmem_rev
          rw [List.mem_filter] at hmem_filter
          obtain ⟨hmem_toList, _⟩ := hmem_filter
          have hcontr : m₁.get? k' = some v' := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem_toList
          rw [hm₁] at hcontr
          contradiction
        have hk_contains : ((List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList).reverse.map Prod.fst).contains k = false := by
          cases h : ((List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList).reverse.map Prod.fst).contains k
          · rfl
          · rw [List.contains_iff_mem] at h
            exact absurd h hk_not_in
        show ((∅ : Std.ExtTreeMap K V compare).insertMany (List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList).reverse)[k]? = m₁[k]?
        rw [Std.ExtTreeMap.getElem?_insertMany_list_of_contains_eq_false hk_contains]
        show (∅ : Std.ExtTreeMap K V compare)[k]? = m₁[k]?
        simp only [Std.ExtTreeMap.getElem?_empty]
        exact hm₁.symm
      | some v₁ =>
        have hmem_toList : (k, v₁) ∈ m₁.toList :=
          Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hm₁
        have hfilter : (m₂.get? k).isNone = true := by
          rw [hm₂]
          rfl
        have hmem_filter : (k, v₁) ∈ List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList := by
          rw [List.mem_filter]
          simp only
          exact ⟨hmem_toList, hfilter⟩
        have hmem_rev : (k, v₁) ∈ (List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList).reverse :=
          List.mem_reverse.mpr hmem_filter
        have hdistinct : (List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList).reverse.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) := by
          rw [List.pairwise_reverse]
          have hdist_toList : m₁.toList.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) :=
            Std.ExtTreeMap.distinct_keys_toList
          have hdist_filter : (List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList).Pairwise (fun a b => ¬compare a.1 b.1 = .eq) := by
            apply List.Pairwise.filter
            exact hdist_toList
          apply hdist_filter.imp
          intro a b h heq
          have : compare a.1 b.1 = .eq := by
            have hsym : compare b.1 a.1 = .eq → compare a.1 b.1 = .eq := by
              intro hba
              rw [Std.LawfulEqCmp.compare_eq_iff_eq] at hba ⊢
              exact hba.symm
            exact hsym heq
          exact h this
        have hcmp_eq : compare k k = .eq := Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl
        show ((∅ : Std.ExtTreeMap K V compare).insertMany (List.filter (fun x => m₂[x.fst]?.isNone) m₁.toList).reverse)[k]? = m₁[k]?
        rw [Std.ExtTreeMap.getElem?_insertMany_list_of_mem hcmp_eq hdistinct hmem_rev]
        exact hm₁.symm
    · cases hget : m₂.get? k with
      | none => contradiction
      | some v₂ =>
        simp only [Option.isSome_some, ite_true]
        have hk_not_in : k ∉ ((List.filter (fun x => (m₂.get? x.fst).isNone) m₁.toList).reverse.map Prod.fst) := by
          intro hmem
          rw [List.mem_map] at hmem
          obtain ⟨⟨k', v'⟩, hmem_rev, hkeq⟩ := hmem
          simp at hkeq
          subst hkeq
          have hmem_filter : (k', v') ∈ List.filter (fun x => (m₂.get? x.fst).isNone) m₁.toList :=
            List.mem_reverse.mp hmem_rev
          rw [List.mem_filter] at hmem_filter
          obtain ⟨_, hfilter⟩ := hmem_filter
          simp only [Option.isNone_iff_eq_none] at hfilter
          rw [hget] at hfilter
          contradiction
        have hk_contains : ((List.filter (fun x => (m₂.get? x.fst).isNone) m₁.toList).reverse.map Prod.fst).contains k = false := by
          cases h : ((List.filter (fun x => (m₂.get? x.fst).isNone) m₁.toList).reverse.map Prod.fst).contains k
          · rfl
          · rw [List.contains_iff_mem] at h
            exact absurd h hk_not_in
        show ((∅ : Std.ExtTreeMap K V compare).insertMany (List.filter (fun x => (m₂.get? x.fst).isNone) m₁.toList).reverse)[k]? = none
        rw [Std.ExtTreeMap.getElem?_insertMany_list_of_contains_eq_false hk_contains]
        rfl

  ofList_nil := by
    simp [FiniteMap.ofList]

  ofList_cons := by
    intro k v l l_1
    simp only [FiniteMap.ofList, FiniteMap.insert]
    rw [List.reverse_cons, Std.ExtTreeMap.ofList_eq_insertMany_empty, Std.ExtTreeMap.ofList_eq_insertMany_empty, Std.ExtTreeMap.insertMany_append, Std.ExtTreeMap.insertMany_list_singleton]

  map_to_list_spec := by
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
      simp only [FiniteMap.toList, FiniteMap.get?]
      exact Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some

  map_ind := by
    intros V P H0 Hind m

    have hm : m = Std.ExtTreeMap.insertMany ∅ (Std.ExtTreeMap.toList m).reverse := by
      apply Std.ExtTreeMap.ext_getElem?
      intro k
      cases hget : m[k]? with
      | none =>
        have hk_not_in : k ∉ (m.toList.reverse.map Prod.fst) := by
          intro hmem
          rw [List.mem_map] at hmem
          obtain ⟨⟨k', v'⟩, hmem_rev, hkeq⟩ := hmem
          simp at hkeq
          subst hkeq
          have hmem_toList : (k', v') ∈ m.toList := List.mem_reverse.mp hmem_rev
          have : m[k']? = some v' := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem_toList
          rw [hget] at this
          contradiction
        have hk_contains : (m.toList.reverse.map Prod.fst).contains k = false := by
          cases h : (m.toList.reverse.map Prod.fst).contains k
          · rfl
          · rw [List.contains_iff_mem] at h
            exact absurd h hk_not_in
        rw [Std.ExtTreeMap.getElem?_insertMany_list_of_contains_eq_false hk_contains]
        rfl
      | some v =>
        have hmem_toList : (k, v) ∈ m.toList :=
          Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hget
        have hmem_rev : (k, v) ∈ m.toList.reverse := List.mem_reverse.mpr hmem_toList
        have hdistinct : m.toList.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) :=
          Std.ExtTreeMap.distinct_keys_toList
        have hdistinct_rev : m.toList.reverse.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) := by
          rw [List.pairwise_reverse]
          apply hdistinct.imp
          intro a b h
          intro heq
          have : compare a.1 b.1 = .eq := by
            have hsym : compare b.1 a.1 = .eq → compare a.1 b.1 = .eq := by
              intro h
              rw [Std.LawfulEqCmp.compare_eq_iff_eq] at h ⊢
              exact h.symm
            exact hsym heq
          exact h this
        have hcmp_eq : compare k k = .eq := Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl
        have : ((∅ : Std.ExtTreeMap K V compare).insertMany m.toList.reverse)[k]? = some v :=
          Std.ExtTreeMap.getElem?_insertMany_list_of_mem hcmp_eq hdistinct_rev hmem_rev
        exact this.symm

    rw [hm]

    generalize hgen : (Std.ExtTreeMap.toList m) = l
    have hdistinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
      rw [← hgen]
      exact Std.ExtTreeMap.distinct_keys_toList
    clear hgen hm m
    induction l with
    | nil =>
      simp [Std.ExtTreeMap.insertMany_nil]
      exact H0
    | cons kv tail ih =>
      obtain ⟨k, v⟩ := kv
      simp
      rw [Std.ExtTreeMap.insertMany_append]
      simp

      rw [List.pairwise_cons] at hdistinct
      obtain ⟨hk_not_in_tail, htail_distinct⟩ := hdistinct

      have hk_not_contains : (tail.reverse.map Prod.fst).contains k = false := by
        apply Decidable.byContradiction
        intro h
        have h_true : (tail.reverse.map Prod.fst).contains k = true := by
          cases h_dec : (tail.reverse.map Prod.fst).contains k
          · exact absurd h_dec h
          · rfl
        rw [List.contains_iff_mem] at h_true
        rw [List.mem_map] at h_true
        obtain ⟨⟨k', v'⟩, hmem_rev, hkeq⟩ := h_true
        simp at hkeq
        have hmem_tail : (k', v') ∈ tail := List.mem_reverse.mp hmem_rev
        have hk_neq : ¬ compare k k' = .eq := hk_not_in_tail (k', v') hmem_tail
        have : compare k k' = .eq := by
          rw [hkeq]
          rw [Std.LawfulEqCmp.compare_eq_iff_eq]
        exact hk_neq this

      apply Hind
      · show ((∅ : Std.ExtTreeMap K V compare).insertMany tail.reverse)[k]? = none
        rw [Std.ExtTreeMap.getElem?_insertMany_list_of_contains_eq_false hk_not_contains]
        rfl
      · exact ih htail_distinct

/-- The FiniteMapLawsSelf instance for ExtTreeMap. -/
instance : FiniteMapLawsSelf K (Std.ExtTreeMap K) where
  toList_filterMap := by
    intro V m f
    haveI : DecidableEq V := Classical.typeDecidableEq V
    simp only [FiniteMap.toList, FiniteMap.filterMap, FiniteMap.ofList]

    obtain H := FiniteMapLaws.map_to_list_to_map (M := (Std.ExtTreeMap K)) (K := K) (V := V) (l := (List.filterMap (fun kv => Option.map (fun x => (kv.fst, x)) (f kv.snd)) m.toList))

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
    exact nodup_filterMap_of_nodup_keys m.toList f nodup_keys

  toList_filter := by
    intro V m φ
    simp [FiniteMap.toList, FiniteMap.filter, FiniteMap.ofList]
    haveI : DecidableEq V := Classical.typeDecidableEq V
    obtain H := FiniteMapLaws.map_to_list_to_map (M := (Std.ExtTreeMap K)) (K := K) (V := V) (l := (List.filter (fun x => φ x.fst x.snd) m.toList))

    simp only [FiniteMap.toList, FiniteMap.ofList] at H
    apply H

    have nodup_keys : (m.toList.map Prod.fst).Nodup := by
      rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
      exact Std.ExtTreeMap.nodup_keys

    exact nodup_map_fst_filter m.toList (fun x => φ x.fst x.snd) nodup_keys

/-- The FiniteMapKmapLaws instance for ExtTreeMap with key type transformation. -/
instance {K' : Type _} [Ord K'] [Std.TransCmp (α := K') compare] [Std.LawfulEqCmp (α := K') compare] [DecidableEq K'] :
    FiniteMapKmapLaws K K' (Std.ExtTreeMap K) (Std.ExtTreeMap K') where
  toList_kmap := by
    intro V f m hinj
    simp [FiniteMap.toList, FiniteMap.kmap, FiniteMap.ofList]
    haveI : DecidableEq V := Classical.typeDecidableEq V
    obtain H := FiniteMapLaws.map_to_list_to_map (M := (Std.ExtTreeMap K')) (K := K') (V := V) (l := (List.map (fun x => (f x.fst, x.snd)) m.toList))

    simp only [FiniteMap.toList, FiniteMap.ofList] at H
    apply H

    have nodup_keys : (m.toList.map Prod.fst).Nodup := by
      rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
      exact Std.ExtTreeMap.nodup_keys

    exact nodup_map_fst_map_injective m.toList f hinj nodup_keys

/-- The FiniteMapSeqLaws instance for ExtTreeMap with Nat keys. -/
instance [Std.TransCmp (α := Nat) compare] [Std.LawfulEqCmp (α := Nat) compare] :
    FiniteMapSeqLaws (Std.ExtTreeMap Nat) where
  toList_map_seq := by
    intro V start l
    simp [FiniteMap.toList, FiniteMap.map_seq, FiniteMap.ofList]
    haveI : DecidableEq V := Classical.typeDecidableEq V

    have heq : List.mapIdx (fun i v => (start + i, v)) l = (List.range' start l.length).zip l :=
      mapIdx_add_eq_zip_range' start l

    rw [heq]

    obtain H := FiniteMapLaws.map_to_list_to_map (M := (Std.ExtTreeMap Nat)) (K := Nat) (V := V) (l := ((List.range' start l.length).zip l))

    simp only [FiniteMap.toList, FiniteMap.ofList] at H
    apply H

    -- The keys from range' are all distinct
    rw [← heq]
    exact nodup_map_fst_mapIdx_add start l

end FiniteMapInst

end Iris.Std
