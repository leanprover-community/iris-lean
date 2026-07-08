/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.Std.Classes
public import Iris.Std.GenSets
public import Batteries.Data.List.Perm

@[expose] public section

namespace Iris.Std

/-- Abstract multiset operations: a `Nat`-valued `multiplicity` and `⊎` (sum), alongside the
`∪` (max), `∩` (min) and `∖` inherited from `Set`. -/
class MultiSet (MS : Type _) (A : outParam (Type _)) extends
    Singleton A MS, EmptyCollection MS, Union MS, Inter MS, SDiff MS where
  multiplicity : A → MS → Nat
  disjUnion : MS → MS → MS

infixl:65 " ⊎ " => MultiSet.disjUnion

instance instMembershipMultiSet [MultiSet MS A] : Membership A MS :=
  ⟨fun X x => 0 < MultiSet.multiplicity x X⟩

theorem mem_iff_multiplicity_pos [MultiSet MS A] {x : A} {X : MS} :
    x ∈ X ↔ 0 < MultiSet.multiplicity x X := Iff.rfl

/-- Laws a multiset implementation must satisfy. -/
class LawfulMultiSet (MS : Type _) (A : outParam (Type _)) extends MultiSet MS A where
  ext : ∀ {X Y : MS}, (∀ x, multiplicity x X = multiplicity x Y) → X = Y
  multiplicity_empty : ∀ {x : A}, multiplicity x (∅ : MS) = 0
  multiplicity_singleton_eq : ∀ {x : A}, multiplicity x ({x} : MS) = 1
  multiplicity_singleton_ne : ∀ {x y : A}, x ≠ y → multiplicity x ({y} : MS) = 0
  multiplicity_disjUnion : ∀ {X Y : MS} {x : A},
    multiplicity x (X ⊎ Y) = multiplicity x X + multiplicity x Y
  multiplicity_union : ∀ {X Y : MS} {x : A},
    multiplicity x (X ∪ Y) = max (multiplicity x X) (multiplicity x Y)
  multiplicity_intersection : ∀ {X Y : MS} {x : A},
    multiplicity x (X ∩ Y) = min (multiplicity x X) (multiplicity x Y)
  multiplicity_difference : ∀ {X Y : MS} {x : A},
    multiplicity x (X \ Y) = multiplicity x X - multiplicity x Y

export LawfulMultiSet (multiplicity_empty multiplicity_singleton_eq multiplicity_singleton_ne
  multiplicity_disjUnion multiplicity_union multiplicity_intersection multiplicity_difference)

attribute [ext] LawfulMultiSet.ext

/-- Finite multiset: carries a list-with-repetitions witness. -/
class FiniteMultiSet (MS : Type _) (A : outParam (Type _)) extends LawfulMultiSet MS A where
  toList : MS → List A
export FiniteMultiSet (toList)

class LawfulFiniteMultiSet (MS : Type _) (A : outParam (Type _))
    extends FiniteMultiSet MS A where
  mem_toList : ∀ {a : A} {m : MS}, a ∈ toList m ↔ a ∈ m
  toList_empty : toList (∅ : MS) = []
  toList_singleton : ∀ {a : A}, toList ({a} : MS) = [a]
  toList_disjUnion : ∀ {X Y : MS}, (toList (X ⊎ Y)).Perm (toList X ++ toList Y)
export LawfulFiniteMultiSet (mem_toList toList_empty toList_singleton toList_disjUnion)

section Lemmas

variable {MS : Type _} {A : Type _}

instance instHasSubsetMultiSet [MultiSet MS A] : HasSubset MS :=
  ⟨fun X Y => ∀ a, MultiSet.multiplicity a X ≤ MultiSet.multiplicity a Y⟩

theorem subset_iff [MultiSet MS A] {X Y : MS} :
    X ⊆ Y ↔ ∀ a, MultiSet.multiplicity a X ≤ MultiSet.multiplicity a Y := Iff.rfl

variable [LawfulMultiSet MS A]

theorem mem_singleton_iff {x a : A} : x ∈ ({a} : MS) ↔ x = a := by
  rw [mem_iff_multiplicity_pos]
  by_cases hxa : x = a
  · subst hxa; simp [multiplicity_singleton_eq]
  · simp [multiplicity_singleton_ne hxa, hxa]

theorem mem_disjUnion_iff {x : A} {X Y : MS} : x ∈ (X ⊎ Y) ↔ x ∈ X ∨ x ∈ Y := by
  rw [mem_iff_multiplicity_pos, mem_iff_multiplicity_pos, mem_iff_multiplicity_pos,
    multiplicity_disjUnion]
  omega

theorem mem_union_iff {x : A} {X Y : MS} : x ∈ (X ∪ Y) ↔ x ∈ X ∨ x ∈ Y := by
  rw [mem_iff_multiplicity_pos, mem_iff_multiplicity_pos, mem_iff_multiplicity_pos,
    multiplicity_union]
  omega

theorem mem_inter_iff {x : A} {X Y : MS} : x ∈ (X ∩ Y) ↔ x ∈ X ∧ x ∈ Y := by
  rw [mem_iff_multiplicity_pos, mem_iff_multiplicity_pos, mem_iff_multiplicity_pos,
    multiplicity_intersection]
  omega

theorem disjUnion_difference_of_subseteq {X Y : MS} (h : Y ⊆ X) : X = Y ⊎ (X \ Y) := by
  refine LawfulMultiSet.ext fun a => ?_
  rw [multiplicity_disjUnion, multiplicity_difference]
  have := subset_iff.mp h a
  omega

theorem disjUnion_singleton_difference {x : A} {X : MS} (h : x ∈ X) : X = {x} ⊎ (X \ {x}) := by
  refine LawfulMultiSet.ext fun a => ?_
  rw [multiplicity_disjUnion, multiplicity_difference]
  by_cases hax : a = x
  · subst hax
    rw [multiplicity_singleton_eq]
    have : 0 < MultiSet.multiplicity a X := h
    omega
  · rw [multiplicity_singleton_ne hax]; omega

end Lemmas

section FiniteLemmas

variable {MS : Type _} {A : Type _} [LawfulFiniteMultiSet MS A]

theorem eq_empty_of_toList_nil {X : MS} (h : toList X = []) : X = ∅ := by
  refine LawfulMultiSet.ext fun a => ?_
  rw [multiplicity_empty]
  have hni : ¬ (0 < MultiSet.multiplicity a X) := by
    rw [← mem_iff_multiplicity_pos, ← mem_toList, h]; simp
  omega

theorem multiset_ind {motive : MS → Prop} (empty : motive ∅)
    (disjUnion_singleton : ∀ a X, motive X → motive ({a} ⊎ X)) (X : MS) : motive X := by
  match hl : toList X with
  | [] => exact eq_empty_of_toList_nil hl ▸ empty
  | a :: _ =>
    have hdecomp : X = {a} ⊎ (X \ {a}) :=
      disjUnion_singleton_difference (mem_toList.mp (by rw [hl]; exact List.mem_cons_self))
    exact hdecomp ▸ disjUnion_singleton a _ (multiset_ind empty disjUnion_singleton (X \ {a}))
termination_by (toList X).length
decreasing_by
  rw [congrArg (fun z : MS => toList z) hdecomp, toList_disjUnion.length_eq, toList_singleton]
  simp only [List.length_append, List.length_cons, List.length_nil]; omega

end FiniteLemmas

end Iris.Std
