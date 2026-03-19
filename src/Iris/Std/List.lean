/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

@[expose] public section

/-!
# List Lemmas

This file contains list theory lemmas that are standard properties
not available in Lean core.
-/

namespace Iris.Std.List

/-- List equivalence relation parameterized by an element equivalence relation. -/
inductive Equiv {α : Type _} (R : α → α → Prop) : List α → List α → Prop where
  | nil : Equiv R [] []
  | cons {x y : α} {l k : List α} : R x y → Equiv R l k → Equiv R (x :: l) (y :: k)

def zipIdxInt {α : Type _} (l : List α) (n : Int) : List (α × Int) :=
  l.mapIdx (fun i v => (v, (i : Int) + n))

/-- Two lists without duplicates with the same membership relation are permutations. -/
theorem Perm.of_mem {l₁ l₂ : List α} (nd₁ : l₁.Nodup) (nd₂ : l₂.Nodup)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : List.Perm l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.refl []
    | cons hd tl =>
      have ha : hd ∈ ([] : List α) := (h hd).mpr List.mem_cons_self
      simp at ha
  | cons a l₁' ih =>
    have ha : a ∈ l₂ := (h a).mp List.mem_cons_self
    cases l₂ with
    | nil => simp at ha
    | cons b l₂' =>
      have hb : b ∈ a :: l₁' := (h b).mpr List.mem_cons_self
      have ha_eq_or_mem : a = b ∨ a ∈ l₂' := by
        cases ha with
        | head _ => left; rfl
        | tail _ h' => right; exact h'
      have hb_eq_or_mem : b = a ∨ b ∈ l₁' := by
        cases hb with
        | head _ => left; rfl
        | tail _ h' => right; exact h'
      cases ha_eq_or_mem with
      | inl hab =>
        subst hab
        apply List.Perm.cons
        apply ih
        · exact List.nodup_cons.mp nd₁ |>.right
        · exact List.nodup_cons.mp nd₂ |>.right
        · intro x
          constructor
          · intro hx
            have : x ∈ a :: l₁' := List.mem_cons_of_mem a hx
            have : x ∈ a :: l₂' := (h x).mp this
            cases this with
            | head _ =>
              have : a ∉ l₁' := List.nodup_cons.mp nd₁ |>.left
              contradiction
            | tail _ hx' => exact hx'
          · intro hx
            have : x ∈ a :: l₂' := List.mem_cons_of_mem a hx
            have : x ∈ a :: l₁' := (h x).mpr this
            cases this with
            | head _ =>
              have : a ∉ l₂' := List.nodup_cons.mp nd₂ |>.left
              contradiction
            | tail _ hx' => exact hx'
      | inr hal₂' =>
        cases hb_eq_or_mem with
        | inl hba =>
          have : b ∉ l₂' := List.nodup_cons.mp nd₂ |>.left
          rw [←hba] at hal₂'
          contradiction
        | inr hbl₁' =>
          obtain ⟨l₁'', l₁''', rfl⟩ := List.append_of_mem hbl₁'
          obtain ⟨l₂'', l₂''', rfl⟩ := List.append_of_mem hal₂'
          have step1 : List.Perm (a :: (l₁'' ++ b :: l₁''')) (a :: b :: (l₁'' ++ l₁''')) := by
            apply List.Perm.cons
            exact List.perm_middle
          have step2 : List.Perm (b :: (l₂'' ++ a :: l₂''')) (b :: a :: (l₂'' ++ l₂''')) := by
            apply List.Perm.cons
            exact List.perm_middle
          apply List.Perm.trans step1
          apply List.Perm.trans _ step2.symm
          have swap_step : List.Perm (a :: b :: (l₂'' ++ l₂''')) (b :: a :: (l₂'' ++ l₂''')) :=
            (List.Perm.swap b a (l₂'' ++ l₂'''))
          apply List.Perm.trans _ swap_step
          apply List.Perm.cons
          specialize (@ih (b :: (l₂'' ++ l₂''')))
          apply List.Perm.trans List.perm_middle.symm
          apply ih
          · apply (List.nodup_cons.mp nd₁).right
          · rw [List.nodup_cons]
            rw [List.nodup_cons, List.Perm.nodup_iff List.perm_middle, List.nodup_cons] at nd₂
            apply And.intro
            · intro hin
              apply nd₂.left
              rw [List.mem_append]; rw [List.mem_append] at hin
              cases hin with
              | inl hin =>
                left; exact hin
              | inr hin =>
                right; rw [List.mem_cons]; right; exact hin
            · exact nd₂.right.right
          · intro x
            specialize h x
            rw [List.mem_cons, List.mem_cons, List.mem_append, List.mem_append, List.mem_cons, List.mem_cons] at h
            rw [List.mem_append, List.mem_cons, List.mem_cons, List.mem_append]
            grind only [= List.nodup_cons, = List.nodup_append, =_ List.cons_append,
              usr List.Perm.nodup_iff, = List.mem_append, = List.mem_cons, usr List.Perm.mem_iff]

end Iris.Std.List
