/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

import Iris.Std.FiniteSet
import Std

/-! ## Concrete Instance of Finite Set Interface

This file provides a concrete implementation of the `FiniteSet` interface using `Std.TreeSet`
-/

namespace Iris.Std

open Lean

/-- Concrete implementation of FiniteSet using TreeSet -/
instance {A : Type v} [Ord A] [Std.LawfulEqCmp (compare : A → A → Ordering)] [Std.TransCmp (compare : A → A → Ordering)] [DecidableEq A] : FiniteSet A (Std.TreeSet A compare) where
  empty := Std.TreeSet.empty
  toList s := s.toList
  ofList l := Std.TreeSet.ofList l

namespace FiniteSetInst

variable {A : Type v} [Ord A] [Std.LawfulEqCmp (compare : A → A → Ordering)] [Std.TransCmp (compare : A → A → Ordering)] [DecidableEq A]

omit [DecidableEq A] in
theorem mem_toList (s : Std.TreeSet A compare) (x : A) :
    x ∈ s.toList ↔ s.contains x := by
  exact Std.TreeSet.mem_toList.trans Std.TreeSet.mem_iff_contains

theorem ofList_mem (l : List A) (x : A) :
    (Std.TreeSet.ofList l : Std.TreeSet A compare).contains x ↔ x ∈ l := by
  rw [← Std.TreeSet.mem_iff_contains, Std.TreeSet.mem_ofList, List.contains_iff_mem]

end FiniteSetInst

/-- Laws for TreeSet FiniteSet instance -/
instance {A : Type v} [DecidableEq A] [LawfulBEq A] [Ord A] [Std.LawfulEqCmp (compare : A → A → Ordering)] [Std.LawfulBEqCmp (compare : A → A → Ordering)] [Std.TransCmp (compare : A → A → Ordering)] : FiniteSetLaws A (Std.TreeSet A compare) where
  mem_empty := by
    intro x h
    simp [Membership.mem, FiniteSet.mem, FiniteSet.toList] at h
    cases h

  toList_ofList := by
    intro l s hnodup heq
    subst heq
    simp [toList, ofList]
    have h_nodup_toList : (Std.TreeSet.ofList l compare).toList.Nodup := by
      have h_distinct := Std.TreeSet.distinct_toList (t := Std.TreeSet.ofList l compare)
      apply List.Pairwise.imp _ h_distinct
      intro a b hab
      intro heq
      subst heq
      exact hab (Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)
    apply List.perm_iff_count.mpr
    intro a
    rw [hnodup.count, h_nodup_toList.count]
    by_cases ha : a ∈ l
    · have : a ∈ Std.TreeSet.ofList l compare := by
        rw [Std.TreeSet.mem_ofList]
        exact List.contains_iff_mem.mpr ha
      have : a ∈ (Std.TreeSet.ofList l compare).toList := Std.TreeSet.mem_toList.mpr this
      simp [ha, this]
    · have : a ∉ Std.TreeSet.ofList l compare := by
        intro h
        rw [Std.TreeSet.mem_ofList, List.contains_iff_mem] at h
        exact ha h
      have : a ∉ (Std.TreeSet.ofList l compare).toList := fun h => this (Std.TreeSet.mem_toList.mp h)
      simp [ha, this]

  toList_nodup := fun X => by
    have h_distinct := Std.TreeSet.distinct_toList (t := X)
    apply List.Pairwise.imp _ h_distinct
    intro a b hab
    intro heq
    subst heq
    exact hab (Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)

  set_to_list_insert := by
    intro s x hnotin
    simp [toList, FiniteSet.insert, ofList]
    have h_not_mem : x ∉ s.toList := by
      intro hmem
      apply hnotin
      simp [Membership.mem, FiniteSet.mem, FiniteSet.toList]
      exact hmem
    have h_nodup : (x :: s.toList).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · exact h_not_mem
      · have h_distinct := Std.TreeSet.distinct_toList (t := s)
        apply List.Pairwise.imp _ h_distinct
        intro a b hab heq
        subst heq
        exact hab (Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)
    apply List.perm_iff_count.mpr
    intro a
    have h_nodup2 : (Std.TreeSet.ofList (x :: s.toList) compare).toList.Nodup := by
      have h_distinct := Std.TreeSet.distinct_toList (t := Std.TreeSet.ofList (x :: s.toList) compare)
      apply List.Pairwise.imp _ h_distinct
      intro a b hab heq
      subst heq
      exact hab (Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)
    rw [h_nodup2.count, h_nodup.count]
    by_cases ha : a ∈ (x :: s.toList)
    · have : a ∈ Std.TreeSet.ofList (x :: s.toList) compare := by
        rw [Std.TreeSet.mem_ofList]
        exact List.contains_iff_mem.mpr ha
      have : a ∈ (Std.TreeSet.ofList (x :: s.toList) compare).toList := Std.TreeSet.mem_toList.mpr this
      simp [ha, this]
    · have : a ∉ Std.TreeSet.ofList (x :: s.toList) compare := by
        intro h
        rw [Std.TreeSet.mem_ofList, List.contains_iff_mem] at h
        exact ha h
      have : a ∉ (Std.TreeSet.ofList (x :: s.toList) compare).toList := fun h => this (Std.TreeSet.mem_toList.mp h)
      simp [ha, this]

  set_to_list_erase := by
    intro s x hin
    exists toList (FiniteSet.erase x s)
    constructor
    · simp [toList, FiniteSet.erase, ofList]
      have h_mem : x ∈ s.toList := by
        simp [Membership.mem, FiniteSet.mem, FiniteSet.toList] at hin
        exact hin
      have h_nodup : s.toList.Nodup := by
        have h_distinct := Std.TreeSet.distinct_toList (t := s)
        apply List.Pairwise.imp _ h_distinct
        intro a b hab heq
        subst heq
        exact hab (Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)
      have h_filter_eq : List.filter (fun y => !decide (y = x)) s.toList = s.toList.erase x := by
        have h_pred_eq : (fun y => !decide (y = x)) = (fun y => y != x) := by
          funext y
          simp only [bne]
          rfl
        rw [h_pred_eq, ← h_nodup.erase_eq_filter]
      rw [h_filter_eq]
      have h_perm1 : s.toList.Perm (x :: s.toList.erase x) := List.perm_cons_erase h_mem
      have h_nodup_erase : (s.toList.erase x).Nodup := h_nodup.erase x
      have h_perm2 : (Std.TreeSet.ofList (s.toList.erase x) compare).toList.Perm (s.toList.erase x) := by
        apply List.perm_iff_count.mpr
        intro a
        have h_nodup2 : (Std.TreeSet.ofList (s.toList.erase x) compare).toList.Nodup := by
          have h_distinct := Std.TreeSet.distinct_toList (t := Std.TreeSet.ofList (s.toList.erase x) compare)
          apply List.Pairwise.imp _ h_distinct
          intro a b hab heq
          subst heq
          exact hab (Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)
        rw [h_nodup2.count, h_nodup_erase.count]
        by_cases ha : a ∈ s.toList.erase x
        · have : a ∈ Std.TreeSet.ofList (s.toList.erase x) compare := by
            rw [Std.TreeSet.mem_ofList]
            exact List.contains_iff_mem.mpr ha
          have : a ∈ (Std.TreeSet.ofList (s.toList.erase x) compare).toList := Std.TreeSet.mem_toList.mpr this
          simp [ha, this]
        · have : a ∉ Std.TreeSet.ofList (s.toList.erase x) compare := by
            intro h
            rw [Std.TreeSet.mem_ofList, List.contains_iff_mem] at h
            exact ha h
          have : a ∉ (Std.TreeSet.ofList (s.toList.erase x) compare).toList := fun h => this (Std.TreeSet.mem_toList.mp h)
          simp [ha, this]
      exact h_perm1.trans (List.Perm.cons x h_perm2.symm)
    · rfl

  ofList_nil := by
    rfl

  toList_empty := by
    rfl

  mem_toList := by
    intro X x
    simp [Membership.mem, FiniteSet.mem]

  toList_filter := by
    intro X φ
    simp [toList, FiniteSet.filter, ofList]
    have h_nodup : (List.filter φ X.toList).Nodup := by
      have h_nodup_orig : X.toList.Nodup := by
        have h_distinct := Std.TreeSet.distinct_toList (t := X)
        apply List.Pairwise.imp _ h_distinct
        intro a b hab heq
        subst heq
        exact hab (Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)
      exact h_nodup_orig.filter φ
    apply List.perm_iff_count.mpr
    intro a
    have h_nodup2 : (Std.TreeSet.ofList (List.filter φ X.toList) compare).toList.Nodup := by
      have h_distinct := Std.TreeSet.distinct_toList (t := Std.TreeSet.ofList (List.filter φ X.toList) compare)
      apply List.Pairwise.imp _ h_distinct
      intro a b hab heq
      subst heq
      exact hab (Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)
    rw [h_nodup2.count, h_nodup.count]
    by_cases ha : a ∈ List.filter φ X.toList
    · have : a ∈ Std.TreeSet.ofList (List.filter φ X.toList) compare := by
        rw [Std.TreeSet.mem_ofList]
        exact List.contains_iff_mem.mpr ha
      have : a ∈ (Std.TreeSet.ofList (List.filter φ X.toList) compare).toList := Std.TreeSet.mem_toList.mpr this
      simp [ha, this]
    · have : a ∉ Std.TreeSet.ofList (List.filter φ X.toList) compare := by
        intro h
        rw [Std.TreeSet.mem_ofList, List.contains_iff_mem] at h
        exact ha h
      have : a ∉ (Std.TreeSet.ofList (List.filter φ X.toList) compare).toList := fun h => this (Std.TreeSet.mem_toList.mp h)
      simp [ha, this]

  mem_ofList := by
    intro l x
    simp [Membership.mem, FiniteSet.mem, FiniteSet.toList, FiniteSet.ofList]
    have h1 : x ∈ (Std.TreeSet.ofList l compare).toList ↔ x ∈ (Std.TreeSet.ofList l compare) := Std.TreeSet.mem_toList
    have h2 : x ∈ (Std.TreeSet.ofList l compare) ↔ l.contains x = true := Std.TreeSet.mem_ofList
    have h3 : l.contains x = true ↔ x ∈ l := List.contains_iff_mem
    exact h1.trans (h2.trans h3)

end Iris.Std
