/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

/-!
# List Lemmas

This file contains list theory lemmas that are standard properties
not available in Lean core.
-/

namespace Iris.Std.List

/-- List equivalence relation parameterized by an element equivalence relation.
    Corresponds to Rocq's `list_equiv`. -/
inductive Equiv {α : Type _} (R : α → α → Prop) : List α → List α → Prop where
  | nil : Equiv R [] []
  | cons {x y : α} {l k : List α} : R x y → Equiv R l k → Equiv R (x :: l) (y :: k)

def zipIdxInt {α : Type _} (l : List α) (n : Int) : List (α × Int) :=
  l.mapIdx (fun i v => (v, (i : Int) + n))

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
    Corresponds to Rocq's `NoDup_Permutation`. -/
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

end Iris.Std.List
