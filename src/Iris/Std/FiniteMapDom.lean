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

variable {M : Type _ → _} {K : Type _}
variable [DecidableEq K] [FiniteMap M K] [FiniteMapLaws M K]

section DomainSet

variable {S : Type _} [FiniteSet S K] [FiniteSetLaws S K]

/-- Convert map domain to a finite set. -/
def domSet (m : M V) : S := FiniteSet.ofList ((FiniteMap.toList m).map Prod.fst)

/-- Create map from set with constant value. -/
def ofSet (c : V) (X : S) : M V := FiniteMap.ofList ((FiniteSet.toList X).map (fun k => (k, c)))

  /-- Lookup returns `none` iff the key is not in the domain.
      Corresponds to Rocq's `not_elem_of_dom`. -/
theorem not_elem_of_domSet : ∀ (m : M V) k, get? m k = none ↔ k ∉ (domSet m : S) := by sorry

  /-- Lookup returns `some` iff the key is in the domain.
      Corresponds to Rocq's `elem_of_dom`. -/
theorem elem_of_domSet : ∀ (m : M V) k, (∃ v, get? m k = some v) ↔ k ∈ (domSet m : S) := by sorry

/-- Domain of empty map is empty set. -/
theorem domSet_empty : domSet (∅ : M V) = (∅ : S) := by
  simp only [domSet, FiniteMapLaws.map_to_list_empty, List.map_nil, FiniteSetLaws.ofList_nil]

/-- The domain after insert includes the inserted key. -/
theorem domSet_insert (m : M V) (k : K) (v : V) :
   k ∈ (domSet (insert m k v) : S) := by
  simp only [domSet, Membership.mem]
  rw [FiniteSetLaws.mem_ofList]
  rw [List.mem_map]
  have : get? (insert m k v) k = some v := lookup_insert_eq m k v
  have : (k, v) ∈ FiniteMap.toList (insert m k v) :=
    FiniteMapLaws.elem_of_map_to_list (insert m k v) k v |>.mpr this
  exact ⟨(k, v), this, rfl⟩

/-- Domain of ofSet equals the original set. -/
theorem domSet_ofSet (c : V) (X : S) :
    domSet (ofSet c X : M V) = X := by
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
    have hget : FiniteMap.get? (ofSet c X : M V) k' = some v :=
      FiniteMapLaws.elem_of_map_to_list _ _ _ |>.mp hmem_list
    -- Use elem_of_list_to_map_2 to get membership from lookup
    have hmem' : (k', v) ∈ (FiniteSet.toList X).map (fun x => (x, c)) := by
      simp only [ofSet] at hget
      exact FiniteMapLaws.elem_of_list_to_map_2 _ _ _ hget
    have : k' ∈ ((FiniteSet.toList X).map (fun x => (x, c))).map Prod.fst := by
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
    have : FiniteMap.get? (ofSet c X : M V) k = some c := by
      simp only [ofSet]
      -- Use elem_of_list_to_map_1 to get lookup from membership
      have hnodup : ((FiniteSet.toList X).map (fun x => (x, c))).map Prod.fst |>.Nodup := by
        simp only [List.map_map]
        show (List.map (fun x => x) (FiniteSet.toList X)).Nodup
        simp only [List.map_id']
        have ⟨l', hperm, hnodup', _⟩ : ∃ l', (FiniteSet.toList X).Perm l' ∧ l'.Nodup ∧ FiniteSet.ofList l' = X :=
          FiniteSetLaws.ofList_toList X
        exact hperm.symm.nodup hnodup'
      exact FiniteMapLaws.elem_of_list_to_map_1 _ _ _ hnodup hmapped
    have : (k, c) ∈ FiniteMap.toList (ofSet c X : M V) :=
      FiniteMapLaws.elem_of_map_to_list _ _ _ |>.mpr this
    exact ⟨(k, c), this, rfl⟩

end DomainSet

end Iris.Std
