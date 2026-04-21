/-
Copyright (c) 2026 Zongyuan Liu, Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Batteries.Data.List.Basic


@[expose] public section

namespace FromMathlib

/-- NB. Copied from Mathlib -/
theorem List.Nodup.of_map (f : α → β) {l : List α} : List.Nodup (List.map f l) → List.Nodup l := by
  refine (List.Pairwise.of_map f) fun _ _ => mt <| fun a => (congrArg f ∘ fun _ => a) α

/-- NB. Copied from Mathlib -/
theorem Pairwise.forall {l : List α} {R : α → α → Prop} (hR : ∀ {a b}, R a b ↔ a ≠ b)
    (hl : l.Pairwise (· ≠ ·)) : ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons]
    rintro x (rfl | hx) y (rfl | hy)
    · simp
    · exact fun a => hR.mpr a
    · exact fun a => hR.mpr a
    · refine ih (List.Pairwise.of_cons hl) hx hy

/-- NB. Copied from Mathlib -/
theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : List.Nodup (List.map f l)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map, List.nodup_cons, List.mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [List.mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃

/-- NB. Copied from Mathlib -/
theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : List.Nodup l) :
    (List.map f l).Nodup :=
  List.Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (List.Pairwise.and_mem.1 d)

/-- NB. Copied from Mathlib -/
 theorem Nodup.filterMap {f : α → Option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    List.Nodup l → List.Nodup (List.filterMap f l) :=
  (List.Pairwise.filterMap f) @fun a a' n b bm b' bm' e => n <| h a a' b' (by rw [← e]; exact bm) bm'

/-- NB. Copied from Mathlib -/
theorem Nodup.filter (p : α → Bool) {l} : List.Nodup l → List.Nodup (List.filter p l) := by
  simpa using List.Pairwise.filter p

inductive Relation.ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflTransGen r a a
  | tail {b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

namespace Relation.ReflTransGen

theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac.tail hcd

@[elab_as_elim]
theorem head_induction_on {motive : ∀ a : α, ReflTransGen r a b → Prop} {a : α}
    (h : ReflTransGen r a b) (refl : motive b refl)
    (head : ∀ {a c} (h' : r a c) (h : ReflTransGen r c b), motive c h → motive a (h.head h')) :
    motive a h := by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
  apply ih
  · exact head hbc _ refl
  · exact fun h1 h2 ↦ head h1 (h2.tail hbc)

theorem cases_head (h : ReflTransGen r a b) : a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  induction h using ReflTransGen.head_induction_on <;> grind

end Relation.ReflTransGen

@[grind .]
theorem List.forall₂_zip : ∀ {l₁ l₂}, List.Forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ l₁.zip l₂ → R a b
  | _, _, List.Forall₂.cons h₁ h₂, x, y, hx => by
    rw [List.zip, List.zipWith, List.mem_cons] at hx
    match hx with
    | Or.inl rfl => exact h₁
    | Or.inr h₃ => exact forall₂_zip h₂ h₃

end FromMathlib
