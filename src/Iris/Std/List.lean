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

/-- Bidirectional relationship between lookup and membership for lists with no duplicate keys.
    For a list with no duplicate keys, `List.lookup k l = some v` if and only if `(k, v) ∈ l`. -/
theorem list_lookup_some_iff_mem {A B : Type _} [DecidableEq A]
    (k : A) (v : B) (l : List (A × B))
    (hnodup : (l.map Prod.fst).Nodup) :
    List.lookup k l = some v ↔ (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    simp only [List.lookup, List.mem_cons]
    rw [List.map_cons, List.nodup_cons] at hnodup
    split
    · next heq =>
      constructor
      · intro h; left; cases Option.some.inj h; ext
        · apply eq_of_beq heq
        · rfl
      · intro h; cases h with
        | inl h => cases h; rfl
        | inr h => have : k ∈ tl.map Prod.fst := by simp; exact ⟨v, h⟩
                   exact absurd (by rw [← eq_of_beq heq]; exact this) hnodup.1
    · next hneq =>
      rw [ih hnodup.2]; constructor
      · intro h; exact Or.inr h
      · intro h; cases h with
        | inl h => cases h; simp at hneq
        | inr h => exact h

/-- If lookup returns some value, the key-value pair is in the list. -/
theorem list_lookup_some_mem {A B : Type _} [DecidableEq A]
    (k : A) (v : B) (l : List (A × B)) :
    List.lookup k l = some v → (k, v) ∈ l := by
  intro h
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.lookup, List.mem_cons] at h ⊢
    split at h
    · next heq => left; cases Option.some.inj h; ext; apply eq_of_beq heq; rfl
    · exact Or.inr (ih h)

/-- If a key-value pair is in the list with no duplicate keys, lookup returns that value. -/
theorem list_mem_lookup_some {A B : Type _} [DecidableEq A]
    (k : A) (v : B) (l : List (A × B))
    (hnodup : (l.map Prod.fst).Nodup) :
    (k, v) ∈ l → List.lookup k l = some v := by
  exact (list_lookup_some_iff_mem k v l hnodup).mpr

/-- For a Nodup list, erasing an element removes it completely. -/
theorem not_mem_erase_self_of_nodup {α : Type _} [DecidableEq α] (x : α) (l : List α)
    (hnd : l.Nodup) : x ∉ l.erase x := by
  induction l with
  | nil => exact List.not_mem_nil
  | cons y ys ih =>
    simp only [List.erase_cons]; rw [List.nodup_cons] at hnd
    split
    · next h => rw [← eq_of_beq h]; exact hnd.1
    · next h => simp; exact ⟨fun heq => absurd (beq_iff_eq.mpr heq.symm) h, ih hnd.2⟩

/-- Two Nodup lists with the same membership are permutations of each other.
    Corresponds to Rocq's `NoDup_Permutation`. -/
theorem perm_of_nodup_of_mem_iff {α : Type _} [DecidableEq α]
    {l₁ l₂ : List α} (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.refl []
    | cons y ys => exact absurd ((hmem y).mpr List.mem_cons_self) List.not_mem_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd₁
    have hmem_erase : ∀ y, y ∈ xs ↔ y ∈ l₂.erase x := fun y => ⟨
      fun hy => (List.mem_erase_of_ne (fun (heq : y = x) => hnd₁.1 (heq ▸ hy))).mpr ((hmem y).mp (List.mem_cons_of_mem x hy)),
      fun hy => by
        have hy_l₁ : y ∈ x :: xs := (hmem y).mpr (List.mem_of_mem_erase hy)
        cases List.mem_cons.mp hy_l₁ with
        | inl heq => exact absurd (heq ▸ hy) (not_mem_erase_self_of_nodup x l₂ hnd₂)
        | inr h => exact h⟩
    exact (List.Perm.cons x (ih hnd₁.2 (hnd₂.erase x) hmem_erase)).trans
          (List.perm_cons_erase ((hmem x).mp List.mem_cons_self)).symm


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

/-- If a list has no duplicate keys (Nodup on first components),
    then filtering preserves this property on the first components. -/
theorem nodup_map_fst_filter {α β : Type _}
    (l : List (α × β)) (p : α × β → Bool)
    (h : (l.map Prod.fst).Nodup) :
    ((List.filter p l).map Prod.fst).Nodup := by
  induction l with
  | nil => simp
  | cons kv tail ih =>
    rw [List.map_cons, List.nodup_cons] at h
    simp only [List.filter]; split
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => h.1 ?_, ih h.2⟩
      clear h ih; induction tail with
      | nil => simp at hmem
      | cons kv' tail' ih_tail =>
        simp only [List.filter] at hmem
        split at hmem
        · rw [List.map_cons, List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · rw [List.map_cons, List.mem_cons]; exact Or.inl heq
          · rw [List.map_cons, List.mem_cons]; exact Or.inr (ih_tail hmem')
        · rw [List.map_cons, List.mem_cons]; exact Or.inr (ih_tail hmem)
    · exact ih h.2

/-- If a list has no duplicate keys (Nodup on first components) and we map keys
    with an injective function, the result also has no duplicate keys. -/
theorem nodup_map_fst_map_injective {α β γ : Type _}
    (l : List (α × β)) (f : α → γ)
    (hinj : ∀ {x y : α}, f x = f y → x = y)
    (h : (l.map Prod.fst).Nodup) :
    ((List.map (fun x => (f x.fst, x.snd)) l).map Prod.fst).Nodup := by
  rw [List.map_map]
  induction l with
  | nil => constructor
  | cons kv tail ih =>
    rw [List.map_cons, List.nodup_cons] at h ⊢
    refine ⟨fun hmem => h.1 ?_, ih h.2⟩
    clear h ih; induction tail with
    | nil => simp at hmem
    | cons kv' tail' ih_tail =>
      rw [List.map_cons, List.mem_cons] at hmem
      rcases hmem with heq | hmem'
      · simp [hinj heq]
      · simp [ih_tail hmem']

/-- mapIdx with addition creates the same result as zipping with range'. -/
theorem mapIdx_add_eq_zip_range' {α : Type _} (start : Nat) (l : List α) :
    List.mapIdx (fun i v => (start + i, v)) l = (List.range' start l.length).zip l := by
  induction l generalizing start with
  | nil =>
    rw [List.mapIdx_nil, List.length_nil, List.range'_zero, List.zip_nil_left]
  | cons hd tl ih =>
    rw [List.mapIdx_cons, List.length_cons, List.range'_succ, List.zip_cons_cons]
    congr 1
    have heq : (fun (i : Nat) (v : α) => (start + (i + 1), v)) = (fun (i : Nat) (v : α) => (start + 1 + i, v)) := by
      funext i v
      simp only [Nat.add_assoc, Nat.add_comm 1]
    rw [heq]
    exact ih (start + 1)

/-- The keys from mapIdx with addition are all distinct. -/
theorem nodup_map_fst_mapIdx_add {α : Type _} (start : Nat) (l : List α) :
    (List.mapIdx (fun i v => (start + i, v)) l).map Prod.fst |>.Nodup := by
  rw [mapIdx_add_eq_zip_range', List.map_fst_zip]
  · exact List.nodup_range' (step := 1)
  · rw [List.length_range']
    omega

/-- If a list has no duplicate keys (Nodup on first components),
    then filtering by mapping the second components preserves this property. -/
theorem nodup_filterMap_of_nodup_keys {α β : Type _}
    (l : List (α × β)) (f : β → Option β)
    (h : (l.map Prod.fst).Nodup) :
    (List.filterMap (fun x => Option.map (fun _ => x.fst) (f x.snd)) l).Nodup := by
  induction l with
  | nil => simp
  | cons kv tail ih =>
    rw [List.map_cons, List.nodup_cons] at h
    simp only [List.filterMap]; split
    · exact ih h.2
    · next b heq =>
      have hb : b = kv.fst := by
        obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.1 heq; exact hf.symm
      subst hb; constructor
      · intro a' hmem heq; subst heq; apply h.1; clear h ih heq
        induction tail with
        | nil => simp at hmem
        | cons kv' tail' ih_tail =>
          simp only [List.filterMap] at hmem; split at hmem
          · simp [ih_tail hmem]
          · next b' heq' =>
            have hb' : b' = kv'.fst := by
              obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.1 heq'; exact hf.symm
            subst hb'; simp only [List.mem_cons] at hmem
            rcases hmem with heq | hmem'
            · simp [heq]
            · simp [ih_tail hmem']
      · exact ih h.2

end Iris.Std.List
