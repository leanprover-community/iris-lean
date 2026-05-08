/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Std.FromMathlib
public import Iris.Std.Infinite
public import Iris.Std.Classes
import Batteries.Data.List.Basic
import Batteries.Data.List.Perm

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

theorem nodup_map_of_injective {B : Type _} {f : A → B} {l : List A}
    (hinj : f.Injective) (hnodup : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp [List.Nodup]
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [List.nodup_cons] at hnodup ⊢
    simp only [List.mem_map]
    constructor
    · intro ⟨y, hy, heq⟩
      cases (hinj heq.symm)
      exact hnodup.1 hy
    · exact ih hnodup.2

theorem fresh [InfiniteType A] (X : List A) : ∃ a : A, a ∉ X := by
  refine Classical.byContradiction fun Hcontra => ?_
  simp only [not_exists, Classical.not_not] at Hcontra
  let Nalloc := X |>.length
  let L := List.range (Nalloc + 1)
  have hnodup : L.map (InfiniteType.enum (T := A)) |>.Nodup :=
    nodup_map_of_injective (fun _ _ => InfiniteType.enum_inj _ _) List.nodup_range
  have hsub : L.map InfiniteType.enum ⊆ X := by
    intro _ ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    exact Hcontra _
  have H := List.subperm_of_subset hnodup hsub |>.length_le
  simp only [List.length_map, Nalloc, L, List.length_range] at H
  omega

@[expose, match_pattern]
def Forall₂.append {l₁ l₁' l₂ l₂'} : List.Forall₂ R l₁ l₂ → List.Forall₂ R l₁' l₂' → List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂')
  | .nil, h => h
  | .cons step rest, h => .cons step (append rest h)

@[grind →]
theorem exists_of_forall₂_cons {l₁ l₂} {x} : List.Forall₂ R (x :: l₁) l₂ →
    ∃ y l₂', l₂ = y :: l₂' ∧ R x y ∧ List.Forall₂ R l₁ l₂'
  | .cons y l₂' => by grind

@[grind →]
theorem exists_of_forall₂_append {l₁ l₁' l} (h : List.Forall₂ R (l₁ ++ l₁') l) :
     ∃ l₂ l₂', l = l₂ ++ l₂' ∧ List.Forall₂ R l₁ l₂ ∧ List.Forall₂ R l₁' l₂' ∧ l₁.length = l₂.length := by
  induction l₁ generalizing l with
  | nil =>
    exists [], l
    simpa using h
  | cons x l₁ IH =>
    grind only [= List.cons_append, → exists_of_forall₂_cons, =_ List.cons_append,
      = List.length_cons, List.Forall₂.cons]

@[grind =]
theorem getElem?_some_iff_append
{a : α} {i : Nat} {l : List α} : l[i]? = some a ↔ ∃ s t : List α, l = s ++ a :: t ∧ s.length = i := by
  refine ⟨fun h => ?_, ?_⟩
  · induction i generalizing l with
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
