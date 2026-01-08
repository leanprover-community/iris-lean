/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Std.FiniteMap
import Iris.Std.FiniteSet
import Iris.Std.List

/-!
# Finite Map Domain Operations

This file defines operations for converting between finite maps and finite sets,
particularly for representing the domain of a map as a set.
-/

namespace Iris.Std

open FiniteMap FiniteSet

variable {M : Type _} {K : Type _} {V : Type _}
variable [DecidableEq K] [FiniteMap M K V] [FiniteMapLaws M K V]

section DomainSet

variable {S : Type _} [FiniteSet S K] [FiniteSetLaws S K]
variable [FiniteMapLawsSelf M K V]

/-- Convert map domain to a finite set. -/
def domSet (m : M) : S := FiniteSet.ofList ((FiniteMap.toList m).map Prod.fst)

/-- Create map from set with constant value. -/
def ofSet (c : V) (X : S) : M := FiniteMap.ofList ((FiniteSet.toList X).map (fun k => (k, c)))

/-- Domain of empty map is empty set. -/
theorem domSet_empty : domSet (∅ : M) = (∅ : S) := by
  simp only [domSet, FiniteMapLaws.map_to_list_empty, List.map_nil, FiniteSetLaws.ofList_nil]

/-- Membership in domSet iff key has a value in the map. -/
theorem elem_of_domSet (m : M) (k : K) :
    FiniteSet.mem k (domSet (m : M) : S) = true ↔ ∃ v, FiniteMap.get? m k = some v := by
  simp only [domSet, FiniteSetLaws.mem_ofList, List.mem_map]
  constructor
  · intro ⟨p, hp, hk⟩
    have : (p.fst, p.snd) ∈ FiniteMap.toList m := hp
    have : FiniteMap.get? m p.fst = some p.snd := FiniteMapLaws.elem_of_map_to_list m p.fst p.snd |>.mpr this
    rw [hk] at this
    exact ⟨p.snd, this⟩
  · intro ⟨v, hv⟩
    refine ⟨(k, v), FiniteMapLaws.elem_of_map_to_list m k v |>.mp hv, rfl⟩

/-- Domain of insert includes the inserted key. -/
theorem domSet_insert (m : M) (k : K) (v : V) :
    (domSet (FiniteMap.insert m k v) : S) = FiniteSet.insert k (domSet m : S) := by
  apply @FiniteSetLaws.ext S K _ _
  intro x
  by_cases h : x = k
  · -- Case: x = k
    subst h
    rw [FiniteSetLaws.mem_insert_eq (domSet m) x x rfl]
    have : FiniteSet.mem x (domSet (FiniteMap.insert m x v) : S) = true :=
      elem_of_domSet (FiniteMap.insert m x v) x |>.mpr ⟨v, FiniteMapLaws.lookup_insert_eq m x v⟩
    exact this
  · -- Case: x ≠ k
    rw [FiniteSetLaws.mem_insert_ne (domSet m) x k h]
    cases hmem : FiniteSet.mem x (domSet m : S)
    · -- mem x (domSet m) = false, need to show mem x (domSet (insert m k v)) = false
      have : ¬∃ v', FiniteMap.get? m x = some v' := by
        intro ⟨v', hv'⟩
        have : FiniteSet.mem x (domSet m : S) = true := elem_of_domSet m x |>.mpr ⟨v', hv'⟩
        rw [hmem] at this
        cases this
      cases hins : FiniteSet.mem x (domSet (FiniteMap.insert m k v) : S)
      · rfl
      · -- Contradiction
        have ⟨v', hv'⟩ := elem_of_domSet (FiniteMap.insert m k v) x |>.mp hins
        have heq : FiniteMap.get? (FiniteMap.insert m k v) x = FiniteMap.get? m x :=
          FiniteMapLaws.lookup_insert_ne m k x v (Ne.symm h)
        rw [heq] at hv'
        have : False := this ⟨v', hv'⟩
        cases this
    · -- mem x (domSet m) = true, need to show mem x (domSet (insert m k v)) = true
      have ⟨v', hv'⟩ := elem_of_domSet m x |>.mp hmem
      have heq : FiniteMap.get? (FiniteMap.insert m k v) x = FiniteMap.get? m x :=
        FiniteMapLaws.lookup_insert_ne m k x v (Ne.symm h)
      have : FiniteSet.mem x (domSet (FiniteMap.insert m k v) : S) = true :=
        elem_of_domSet (FiniteMap.insert m k v) x |>.mpr ⟨v', heq.symm ▸ hv'⟩
      exact this

/-- Domain of ofSet equals the original set. -/
theorem domSet_ofSet (c : V) (X : S) :
    domSet (ofSet c X : M) = X := by
  apply @FiniteSetLaws.ext S K _ _
  intro k
  simp only [domSet]
  apply Bool.eq_iff_iff.mpr
  constructor
  · -- Forward: k ∈ domSet (ofSet c X) → k ∈ X
    intro hmem
    rw [FiniteSetLaws.mem_ofList] at hmem
    rw [List.mem_map] at hmem
    obtain ⟨⟨k', v⟩, hmem_list, heq⟩ := hmem
    simp at heq
    rw [← heq]
    have : FiniteMap.get? (ofSet c X : M) k' = some v :=
      FiniteMapLaws.elem_of_map_to_list _ _ _ |>.mpr hmem_list
    simp only [ofSet, FiniteMapLaws.elem_of_list_to_map] at this
    have : k' ∈ ((FiniteSet.toList X).map (fun x => (x, c))).map Prod.fst := by
      have : (k', v) ∈ ((FiniteSet.toList X).map (fun x => (x, c))).reverse := by
        exact list_lookup_some_mem k' v _ this
      have hmem' : (k', v) ∈ (FiniteSet.toList X).map (fun x => (x, c)) := by
        exact List.mem_reverse.mp this
      rw [List.mem_map]
      exact ⟨(k', v), hmem', rfl⟩
    simp [List.map_map] at this
    exact FiniteSetLaws.mem_toList X k' |>.mp this
  · -- Backward: k ∈ X → k ∈ domSet (ofSet c X)
    intro hmem
    rw [FiniteSetLaws.mem_ofList, List.mem_map]
    have hk_in : k ∈ FiniteSet.toList X := FiniteSetLaws.mem_toList X k |>.mpr hmem
    have hmapped : (k, c) ∈ (FiniteSet.toList X).map (fun x => (x, c)) := by
      rw [List.mem_map]
      exact ⟨k, hk_in, rfl⟩
    have : FiniteMap.get? (ofSet c X : M) k = some c := by
      simp only [ofSet, FiniteMapLaws.elem_of_list_to_map]
      have : (k, c) ∈ ((FiniteSet.toList X).map (fun x => (x, c))).reverse :=
        List.mem_reverse.mpr hmapped
      have hnodup : ((FiniteSet.toList X).map (fun x => (x, c))).reverse.map Prod.fst |>.Nodup := by
        rw [List.map_reverse]
        simp only [List.map_map]
        show (List.map (fun x => x) (FiniteSet.toList X)).reverse.Nodup
        simp only [List.map_id']
        have ⟨l', hperm, hnodup', _⟩ : ∃ l', (FiniteSet.toList X).Perm l' ∧ l'.Nodup ∧ FiniteSet.ofList l' = X :=
          FiniteSetLaws.ofList_toList X
        have hnodup_toList : (FiniteSet.toList X).Nodup := hperm.symm.nodup hnodup'
        exact list_nodup_reverse (FiniteSet.toList X) |>.mpr hnodup_toList
      exact list_mem_lookup k c _ hnodup this
    have : (k, c) ∈ FiniteMap.toList (ofSet c X : M) :=
      FiniteMapLaws.elem_of_map_to_list _ _ _ |>.mp this
    exact ⟨(k, c), this, rfl⟩

end DomainSet

end Iris.Std
