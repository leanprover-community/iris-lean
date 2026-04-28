/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Std.Infinite
public import Iris.Std.Classes
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

end Iris.Std.List
