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

/-- For a Nodup list, erasing an element removes it completely. -/
theorem not_mem_erase_self_of_nodup {α : Type _} [DecidableEq α] (x : α) (l : List α)
    (hnd : l.Nodup) : x ∉ l.erase x := by
  induction l with
  | nil => exact List.not_mem_nil
  | cons y ys ih =>
    simp only [List.erase_cons]
    rw [List.nodup_cons] at hnd
    split
    · next h =>
      have heq : y = x := eq_of_beq h
      rw [← heq]
      exact hnd.1
    · next h =>
      simp only [List.mem_cons]
      intro hor
      cases hor with
      | inl heq =>
        have : (y == x) = true := beq_iff_eq.mpr heq.symm
        exact absurd this h
      | inr hmem => exact ih hnd.2 hmem

/-- Two Nodup lists with the same membership are permutations of each other.
    This is the key lemma corresponding to Rocq's `NoDup_Permutation`. -/
theorem perm_of_nodup_of_mem_iff {α : Type _} [DecidableEq α]
    {l₁ l₂ : List α} (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.refl []
    | cons y ys =>
      have : y ∈ ([] : List α) := (hmem y).mpr List.mem_cons_self
      exact absurd this List.not_mem_nil
  | cons x xs ih =>
    have hx_in_l₂ : x ∈ l₂ := (hmem x).mp List.mem_cons_self
    have hperm₂ : l₂.Perm (x :: l₂.erase x) := List.perm_cons_erase hx_in_l₂
    rw [List.nodup_cons] at hnd₁
    have hx_notin_xs : x ∉ xs := hnd₁.1
    have hnd_xs : xs.Nodup := hnd₁.2
    have hnd_erase : (l₂.erase x).Nodup := hnd₂.erase x
    have hmem_erase : ∀ y, y ∈ xs ↔ y ∈ l₂.erase x := by
      intro y
      constructor
      · intro hy
        have hne : y ≠ x := fun heq => hx_notin_xs (heq ▸ hy)
        have hy_l₂ : y ∈ l₂ := (hmem y).mp (List.mem_cons_of_mem x hy)
        exact (List.mem_erase_of_ne hne).mpr hy_l₂
      · intro hy
        have hne : y ≠ x := by
          intro heq
          rw [heq] at hy
          exact not_mem_erase_self_of_nodup x l₂ hnd₂ hy
        have hy_l₂ : y ∈ l₂ := List.mem_of_mem_erase hy
        have hy_l₁ : y ∈ x :: xs := (hmem y).mpr hy_l₂
        cases List.mem_cons.mp hy_l₁ with
        | inl heq => exact absurd heq hne
        | inr h => exact h
    have hperm_xs : xs.Perm (l₂.erase x) := ih hnd_xs hnd_erase hmem_erase
    exact (List.Perm.cons x hperm_xs).trans hperm₂.symm


theorem nodup_of_nodup_map_fst {α β : Type _} (l : List (α × β))
    (h : (l.map Prod.fst).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons]
    constructor
    · intro hx
      rw [List.map_cons, List.nodup_cons] at h
      have : x.1 ∈ xs.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hx
      exact h.1 this
    · rw [List.map_cons, List.nodup_cons] at h
      exact ih h.2

end Iris.Std
