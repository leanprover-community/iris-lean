/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Std.FromMathlib
public import Batteries.Data.List.Basic

/-!
# List Lemmas

This file contains list theory lemmas that are standard properties
not available in Lean core.
-/

public section

namespace Iris.Std.List

/-- List equivalence relation parameterized by an element equivalence relation. -/
inductive Equiv {α : Type _} (R : α → α → Prop) : List α → List α → Prop where
  | nil : Equiv R [] []
  | cons {x y : α} {l k : List α} : R x y → Equiv R l k → Equiv R (x :: l) (y :: k)

@[expose] def zipIdxInt {α : Type _} (l : List α) (n : Int) : List (α × Int) :=
  l.mapIdx (fun i v => (v, (i : Int) + n))

@[expose, match_pattern]
def Forall₂.append : ∀ {l₁ l₁' l₂ l₂'}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₁' l₂' → List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons step rest, h => .cons step (append rest h)

@[grind →]
theorem exists_of_forall₂_cons : ∀ {l₁ l₂}{x},
    List.Forall₂ R (x :: l₁) l₂ → ∃ y l₂', l₂ = y :: l₂' ∧ R x y ∧ List.Forall₂ R l₁ l₂' := by
  intro l₁ l₂ x h
  cases h with
  | cons y l₂' => grind only

@[grind →]
theorem exists_of_forall₂_append : ∀ {l₁ l₁' l},
    List.Forall₂ R (l₁ ++ l₁') l → ∃ l₂ l₂', l = l₂ ++ l₂' ∧ List.Forall₂ R l₁ l₂ ∧ List.Forall₂ R l₁' l₂' ∧ l₁.length = l₂.length := by
  intro l₁ l₁' l h
  induction l₁ generalizing l with
  | nil =>
    exists [], l
    simpa using h
  | cons x l₁ IH =>
    grind only [= List.cons_append, → exists_of_forall₂_cons,
      =_ List.cons_append, = List.length_cons, List.Forall₂.cons]
    -- obtain ⟨y, l, rfl, x_y, h⟩ := List.exists_of_forall₂_cons h
    -- obtain ⟨l₂, l₂', h, Rleft, Rright, hlen⟩ := IH h
    -- exists (y :: l₂), l₂'
    -- refine ⟨h ▸ rfl, List.Forall₂.cons x_y Rleft, Rright, ?_⟩
    -- simp only [List.length_cons, hlen]

@[grind =]
theorem getElem?_some_iff_append
{a : α} {i : Nat} {l : List α} : l[i]? = some a ↔ ∃ s t : List α, l = s ++ a :: t ∧ s.length = i := by
  constructor
  · intros h
    induction i generalizing l with
    | zero =>
      rcases l with _ | ⟨hd, tl⟩
      · simp at h
      · simpa using h
    | succ i IH =>
      rcases l with _ | ⟨hd, tl⟩
      · simp at h
      simp at h
      grind only [=_ List.cons_append, = List.length_cons]
  · rintro ⟨ps, ss, rfl, h2⟩
    grind only [= List.getElem?_append, = List.getElem?_cons]

end Iris.Std.List
