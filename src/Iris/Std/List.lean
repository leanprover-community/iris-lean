/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

/-!
# List Lemmas

This file contains list theory lemmas that are standard properties
not available in Lean core.
-/

namespace Iris.Std

/-- If lookup returns some value, the key-value pair is in the list. -/
theorem list_lookup_some_mem {A B : Type _} [BEq A] [LawfulBEq A]
    (k : A) (v : B) (l : List (A × B)) :
    List.lookup k l = some v → (k, v) ∈ l := by
  intro h
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp [List.lookup] at h
    split at h
    · simp at h
      subst h
      simp
      left
      next heq =>
        have : k = hd.1 := eq_of_beq heq
        exact Prod.ext this rfl
    · simp
      right
      exact ih h

/-- Lookup in a mapped list returns the mapped value. -/
theorem list_lookup_map {A B : Type _} [BEq A] [LawfulBEq A]
    (f : A → B) (k : A) (l : List A) (h : k ∈ l) :
    List.lookup k (l.map (fun x => (x, f x))) = some (f k) := by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp [List.lookup, List.map]
    split
    · next heq =>
      have : k = hd := eq_of_beq heq
      simp [this]
    · next hneq =>
      simp at h
      cases h with
      | inl heq =>
        subst heq
        have : (k == k) = true := BEq.refl k
        rw [this] at hneq
        contradiction
      | inr hmem =>
        exact ih hmem

/-- If lookup succeeds in a mapped list, the key must be in the original list. -/
theorem list_lookup_map_inv {A B : Type _} [BEq A] [LawfulBEq A]
    (f : A → B) (k : A) (l : List A) (v : B) :
    List.lookup k (l.map (fun x => (x, f x))) = some v → v = f k ∧ k ∈ l := by
  intro h
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp [List.lookup, List.map] at h
    split at h
    · next heq =>
      simp at h
      subst h
      have : k = hd := eq_of_beq heq
      subst this
      simp [List.mem_cons]
    · next hneq =>
      have ⟨hv, hmem⟩ := ih h
      constructor
      · exact hv
      · simp [List.mem_cons]
        right
        exact hmem

/-- If a key-value pair is in a list with unique keys (nodup on fst projection),
    then lookup returns that value. -/
theorem list_mem_lookup {A B : Type _} [BEq A] [LawfulBEq A]
    (k : A) (v : B) (l : List (A × B)) (hnodup : l.map Prod.fst |>.Nodup) :
    (k, v) ∈ l → List.lookup k l = some v := by
  intro h
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp at h
    simp [List.lookup]
    split
    · next heq =>
      cases h with
      | inl heq_pair =>
        -- (k, v) = hd, so we need to show some hd.2 = some v
        rw [Prod.ext_iff] at heq_pair
        exact congrArg some heq_pair.2.symm
      | inr hmem =>
        -- k is in tl but k == hd.1, contradicts nodup
        have keq : k = hd.1 := eq_of_beq heq
        subst keq
        have hmem_map : hd.1 ∈ tl.map Prod.fst := by
          rw [List.mem_map]
          exact ⟨(hd.1, v), hmem, rfl⟩
        have : (List.map Prod.fst (hd :: tl)).Nodup := hnodup
        rw [List.map_cons] at this
        have h_nodup_cons := List.nodup_cons.mp this
        have : hd.1 ∉ tl.map Prod.fst := h_nodup_cons.1
        contradiction
    · next hneq =>
      cases h with
      | inl heq_pair =>
        rw [Prod.ext_iff] at heq_pair
        have : k = hd.1 := heq_pair.1
        subst this
        have : (hd.1 == hd.1) = true := BEq.refl hd.1
        rw [this] at hneq
        contradiction
      | inr hmem =>
        simp [List.map, List.Nodup, List.pairwise_cons] at hnodup
        exact ih hnodup.2 hmem

/-- Reversing a list preserves the nodup property. -/
theorem list_nodup_reverse {A : Type _} (l : List A) :
    l.reverse.Nodup ↔ l.Nodup := by
  constructor
  · intro h
    induction l with
    | nil => constructor
    | cons hd tl ih =>
      rw [List.reverse_cons] at h
      have ⟨h1, h2, h3⟩ := List.nodup_append.mp h
      constructor
      · intro a' hmem
        have hmem_rev : a' ∈ tl.reverse := List.mem_reverse.mpr hmem
        have hd_mem : hd ∈ [hd] := List.mem_singleton_self hd
        have := h3 a' hmem_rev hd hd_mem
        exact this.symm
      · exact ih h1
  · intro h
    induction l with
    | nil => constructor
    | cons hd tl ih =>
      rw [List.reverse_cons]
      match h with
      | .cons hnotin hnodup =>
        have ih_result := ih hnodup
        apply List.nodup_append.mpr
        constructor
        · exact ih_result
        · constructor
          · constructor
            · intro a' hmem; contradiction
            · constructor
          · intro a ha b hb
            simp at hb
            subst hb
            have := List.mem_reverse.mp ha
            exact (hnotin a this).symm

end Iris.Std
