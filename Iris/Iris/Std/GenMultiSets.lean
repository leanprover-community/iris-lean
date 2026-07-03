/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.Std.Classes
public import Iris.Std.GenSets
import Batteries.Data.List.Perm
import Iris.Std.List
import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.Std

/-- Abstract multiset operations. Mirrors `Set`, but a `Nat`-valued `multiplicity`
replaces boolean membership, and `⊎` (multiset sum) is added alongside `∪`/`∩`/`∖`. -/
class MultiSet (MS : Type _) (A : outParam (Type _)) extends
    Singleton A MS, EmptyCollection MS, Union MS, Inter MS, SDiff MS where
  /-- Multiplicity (count) of `x` in the multiset. The multiset analog of `∈`. -/
  multiplicity : A → MS → Nat
  /-- Disjoint union (multiset sum): multiplicities add. Distinct from `∪` (max). -/
  disjUnion : MS → MS → MS

@[inherit_doc] infixl:65 " ⊎ " => MultiSet.disjUnion

/-- Membership is derived: `x ∈ X` iff its multiplicity is positive. -/
instance instMembershipMultiSet [MultiSet MS A] : Membership A MS :=
  ⟨fun X x => 0 < MultiSet.multiplicity x X⟩

theorem mem_iff_multiplicity_pos [MultiSet MS A] {x : A} {X : MS} :
    x ∈ X ↔ 0 < MultiSet.multiplicity x X := Iff.rfl

/-- Laws a multiset implementation must satisfy. -/
class LawfulMultiSet (MS : Type _) (A : outParam (Type _)) extends MultiSet MS A where
  /-- Multiset extensionality: equal multiplicities everywhere ⇒ equal. -/
  ext : ∀ {X Y : MS}, (∀ x, multiplicity x X = multiplicity x Y) → X = Y
  multiplicity_empty        : ∀ {x : A},        multiplicity x (∅ : MS) = 0
  multiplicity_singleton_eq : ∀ {x : A},        multiplicity x ({x} : MS) = 1
  multiplicity_singleton_ne : ∀ {x y : A}, x ≠ y → multiplicity x ({y} : MS) = 0
  multiplicity_disjUnion    : ∀ {X Y : MS} {x : A}, multiplicity x (X ⊎ Y) = multiplicity x X + multiplicity x Y
  multiplicity_union        : ∀ {X Y : MS} {x : A}, multiplicity x (X ∪ Y) = max (multiplicity x X) (multiplicity x Y)
  multiplicity_intersection : ∀ {X Y : MS} {x : A}, multiplicity x (X ∩ Y) = min (multiplicity x X) (multiplicity x Y)
  multiplicity_difference   : ∀ {X Y : MS} {x : A}, multiplicity x (X \ Y) = multiplicity x X - multiplicity x Y

export LawfulMultiSet (multiplicity_empty multiplicity_singleton_eq multiplicity_singleton_ne
  multiplicity_disjUnion multiplicity_union multiplicity_intersection multiplicity_difference)

attribute [ext] LawfulMultiSet.ext

/-- Finite multiset: carries a list-with-repetitions witness (analog of `FiniteSet.toList`). -/
class FiniteMultiSet (MS : Type _) (A : outParam (Type _)) extends LawfulMultiSet MS A where
  /-- Convert to a list, WITH repetitions (each `x` occurs `multiplicity x m` times). -/
  toList : MS → List A
export FiniteMultiSet (toList)

/-- Laws linking `toList` to the multiset operations (analog of `FiniteSet`, without `nodup`). -/
class LawfulFiniteMultiSet (MS : Type _) (A : outParam (Type _))
    extends FiniteMultiSet MS A where
  /-- `toList` realises membership (analog of `FiniteSet.mem_toList`). -/
  mem_toList    : ∀ {a : A} {m : MS}, a ∈ toList m ↔ a ∈ m
  /-- `toList ∅` is empty. -/
  toList_empty  : toList (∅ : MS) = []
  /-- `toList` of a singleton. -/
  toList_singleton : ∀ {a : A}, toList ({a} : MS) = [a]
  /-- `toList` distributes over `⊎` up to permutation (order unspecified). -/
  toList_disjUnion : ∀ {X Y : MS}, (toList (X ⊎ Y)).Perm (toList X ++ toList Y)
export LawfulFiniteMultiSet (mem_toList toList_empty toList_singleton toList_disjUnion)

section Lemmas

variable {MS : Type _} {A : Type _}

/-- Multiset inclusion: `X ⊆ Y` iff every element's multiplicity in `X` is at most in `Y`
(Coq gmultiset `⊆`). -/
instance instHasSubsetMultiSet [MultiSet MS A] : HasSubset MS :=
  ⟨fun X Y => ∀ a, MultiSet.multiplicity a X ≤ MultiSet.multiplicity a Y⟩

theorem subset_iff [MultiSet MS A] {X Y : MS} :
    X ⊆ Y ↔ ∀ a, MultiSet.multiplicity a X ≤ MultiSet.multiplicity a Y := Iff.rfl

variable [LawfulMultiSet MS A]

theorem mem_singleton_iff {x a : A} : x ∈ ({a} : MS) ↔ x = a := by
  rw [mem_iff_multiplicity_pos]
  by_cases hxa : x = a
  · subst hxa; rw [multiplicity_singleton_eq]; exact iff_of_true (by omega) rfl
  · rw [multiplicity_singleton_ne hxa]; exact iff_of_false (by omega) hxa

theorem mem_disjUnion_iff {x : A} {X Y : MS} : x ∈ (X ⊎ Y) ↔ x ∈ X ∨ x ∈ Y := by
  rw [mem_iff_multiplicity_pos, mem_iff_multiplicity_pos, mem_iff_multiplicity_pos,
    multiplicity_disjUnion]
  omega

/-- If `Y ⊆ X`, then `X` splits as `Y ⊎ (X ∖ Y)` (Coq `gmultiset_disj_union_difference`). -/
theorem disjUnion_difference_of_subseteq {X Y : MS} (h : Y ⊆ X) : X = Y ⊎ (X \ Y) := by
  refine LawfulMultiSet.ext fun a => ?_
  rw [multiplicity_disjUnion, multiplicity_difference]
  have := subset_iff.mp h a
  omega

/-- If `x ∈ X`, then `X` splits as `{x} ⊎ (X ∖ {x})` (Coq `gmultiset_disj_union_difference'`). -/
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

/-- An empty `toList` forces the empty multiset. -/
theorem eq_empty_of_toList_nil {X : MS} (h : toList X = []) : X = ∅ := by
  refine LawfulMultiSet.ext fun a => ?_
  rw [multiplicity_empty]
  have hni : ¬ (0 < MultiSet.multiplicity a X) := by
    rw [← mem_iff_multiplicity_pos, ← mem_toList, h]; simp
  omega

/-- Multiset induction (Coq `gmultiset_ind`), derived from `toList` — like `set_ind`. -/
theorem multiset_ind {motive : MS → Prop}
    (empty : motive ∅)
    (disjUnion_singleton : ∀ a X, motive X → motive ({a} ⊎ X)) (X : MS) : motive X := by
  suffices h : ∀ n (Y : MS), (toList Y).length ≤ n → motive Y from h (toList X).length X (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro Y hle
    have hnil : toList Y = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hle)
    exact eq_empty_of_toList_nil hnil ▸ empty
  | succ n IH =>
    intro Y hle
    by_cases hempty : toList Y = []
    · exact eq_empty_of_toList_nil hempty ▸ empty
    · obtain ⟨a, ha⟩ : ∃ a, a ∈ toList Y := by
        cases hl : toList Y with
        | nil => exact absurd hl hempty
        | cons x xs => exact ⟨x, List.mem_cons_self⟩
      have haY : a ∈ Y := mem_toList.mp ha
      have hdecomp : Y = {a} ⊎ (Y \ {a}) := disjUnion_singleton_difference haY
      have hperm : (toList Y).Perm ([a] ++ toList (Y \ {a})) := by
        have e : toList Y = toList ({a} ⊎ (Y \ {a})) := congrArg (fun z : MS => toList z) hdecomp
        have ts : toList ({a} : MS) = [a] := toList_singleton
        rw [e, ← ts]
        exact toList_disjUnion
      have hlen' : (toList (Y \ {a})).length ≤ n := by
        have hpe := hperm.length_eq
        simp only [List.length_append, List.length_cons, List.length_nil] at hpe
        omega
      exact hdecomp ▸ disjUnion_singleton a (Y \ {a}) (IH (Y \ {a}) hlen')

end FiniteLemmas

end Iris.Std
