/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Iris.Std.GenSets
public import Std.Data.ExtTreeSet
public import Iris.Std.CoPset

@[expose] public section

/-! ## LawfulSet Instances -/

namespace Iris.Std

open Iris.Std

/-! ### ExtTreeSet Instance -/

theorem mem_singleton_extTreeSet {α : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {x y : α} :
    x ∈ ({y} : Std.ExtTreeSet α cmp) ↔ x = y := by
  simp only [Std.ExtTreeSet.singleton_eq_insert, Std.ExtTreeSet.mem_insert,
    Std.LawfulEqCmp.compare_eq_iff_eq, Std.ExtTreeSet.not_mem_empty, or_false]
  apply Iff.intro <;> rintro ⟨⟩ <;> rfl

instance {α : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    LawfulSet (Std.ExtTreeSet α cmp) α where
  ext _ _ h := Std.ExtTreeSet.ext_mem h
  mem_empty := Std.ExtTreeSet.not_mem_empty
  mem_singleton := mem_singleton_extTreeSet
  mem_union := Std.ExtTreeSet.mem_union_iff
  mem_inter := Std.ExtTreeSet.mem_inter_iff
  mem_diff := Std.ExtTreeSet.mem_diff_iff

instance {α : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : FiniteSet (Std.ExtTreeSet α cmp) α where
  toList s := s.toList

instance {α : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : LawfulFiniteSet (Std.ExtTreeSet α cmp) α where
  mem_toList := Std.ExtTreeSet.mem_toList
  toList_nodup := by
    intro m
    have e := Std.ExtTreeSet.distinct_toList (t := m)
    simp only [List.Nodup]
    have heq : (fun x1 x2 => x1 ≠ x2) = (fun a b => ¬cmp a b = Ordering.eq) := by
      ext x1 x2; simp
    rw [heq]
    apply e

end Iris.Std
