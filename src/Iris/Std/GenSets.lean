/-
Copyright (c) 2026 Zongyuan Liu, Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Sergei Stepanenko
-/
module

public import Iris.Std.Classes
import Batteries.Data.List.Perm
import Iris.Std.List
import Iris.Std.RocqAlias

@[expose] public section

/-! ## Abstract Set Interface

This file defines an abstract interface for (finite) sets, inspired by stdpp's `fin_sets`.

### Notation

* `x ∈ S` - Membership
* `∅` - Empty set
* `{x}` - Singleton set
* `S₁ ∪ S₂` - Union
* `S₁ ∩ S₂` - Intersection
* `S₁ ∖ S₂` - Difference (remove element)
* `S₁ ⊆ S₂` - Subset relation
* `S₁ ## S₂` - Disjoint sets
-/

namespace Iris.Std

/-- Abstract set interface.
The type constructor `S` represents a set of elements of type `A`.  -/
class Set (S : Type _) (A : outParam (Type _)) extends
  Membership A S, Singleton A S, Union S
  , Inter S, SDiff S, EmptyCollection S

/-- Laws that a set implementation must satisfy. -/
class LawfulSet (S : Type _) (A : outParam (Type _)) extends Set S A where
  /-- Set extensionality: sets with same membership are equal. -/
  ext : ∀ (X Y : S), (∀ x, x ∈ X ↔ x ∈ Y) → X = Y
  /-- Membership in empty set is always false. -/
  mem_empty : ∀ {x : A}, x ∉ (∅ : S)
  /-- Membership in singleton: true iff equal. -/
  mem_singleton : ∀ {x y : A}, x ∈ ({ y } : S) ↔ x = y
  /-- Membership in union: x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y -/
  mem_union : ∀ {X Y : S} {x : A},
    x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y)
  /-- Membership in intersection: x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y -/
  mem_inter : ∀ {X Y : S} {x : A},
    x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y)
  /-- Membership in difference: x ∈ X \ Y ↔ x ∈ X ∧ x ∉ Y -/
  mem_diff : ∀ {X Y : S} {x : A},
    x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y)
  export LawfulSet (mem_empty mem_singleton
    mem_union mem_inter mem_diff)

attribute [ext] LawfulSet.ext

section FiniteSet

variable {S : Type _} {A : Type _} [Set S A]

/-- Subset relation: `S₁` is a subset of `S₂` if every element in `S₁` is also in `S₂`. -/
instance : HasSubset S := ⟨fun S₁ S₂ => ∀ x, x ∈ S₁ → x ∈ S₂⟩

/-- Proper subset relation: `S₁` is a proper subset of `S₂` if every element in `S₁`
    is in `S₂` but they are not equal. -/
instance : HasSSubset S := ⟨fun S₁ S₂ => S₁ ≠ S₂ ∧ ∀ x, x ∈ S₁ → x ∈ S₂⟩

/-- Two sets are disjoint if they share no common elements. -/
instance : Disjoint S where
  disjoint S₁ S₂ := ∀ x, ¬(x ∈ S₁ ∧ x ∈ S₂)

class FiniteSet (S : Type _) (A : outParam (Type _)) extends LawfulSet S A where
  toList : S → List A
export FiniteSet (toList)

class LawfulFiniteSet (S : Type _) (A : outParam (Type _)) extends LawfulSet S A, FiniteSet S A where
  mem_toList {k : A} : k ∈ toList m ↔ k ∈ m
  toList_nodup : (toList m).Nodup
export LawfulFiniteSet (mem_toList toList_nodup)

end FiniteSet

class DecidableDisj (S : Type _) [LawfulSet S A] where
  decide_disj : ∀ X₁ X₂ : S, Decidable (X₁ ## X₂)

instance [LawfulSet S A] [DecidableDisj S] {X₁ X₂ : S} : Decidable (X₁ ## X₂) := DecidableDisj.decide_disj X₁ X₂

namespace LawfulSet

section GenLemmas

variable {S : Type _} {A : Type _} [LawfulSet S A]

/-- Insert an element into a set. Defined as singleton union. -/
def ins (x : A) (s : S) : S := {x} ∪ s

instance : Insert A S where
  insert := ins

/-- Membership after insert: true if equal, otherwise unchanged. -/
theorem mem_insert {s : S} {x y : A} : x ∈ (insert y s) ↔ (x = y ∨ x ∈ s) := by
  simp [insert, ins, mem_union, mem_singleton]

/-- Delete an element from a set. Defined as difference with singleton. -/
def delete (x : A) (s : S) : S := s \ {x}

/-- Membership after delete: false if equal to deleted element. -/
theorem mem_delete {s : S} {x y : A} : x ∈ (delete y s) ↔ (x ∈ s ∧ x ≠ y) := by
  simp [delete, mem_diff, mem_singleton]

/-! ### Extensionality and equality -/

/-- Two sets are equal if they are subsets of each other (antisymmetry of subset). -/
theorem eq_subset {X Y : S} : X ⊆ Y → Y ⊆ X → X = Y := by
  intro H1 H2
  ext x
  apply Iff.intro
  · apply H1 x
  · apply H2 x

/-- Proper subset is equivalent to subset plus inequality. -/
theorem ssubset_subset  {X Y : S} : (X ⊂ Y) ↔ (X ⊆ Y ∧ X ≠ Y) := by
  simp [SSubset, Subset]; grind only

/-! ### List conversion -/

/-- Helper function that extends a set `s` by inserting all elements from list `l`. -/
def ofListExtend (l : List A) (s : S) : S :=
  l.foldl (fun s x => insert x s) s

/-- Convert a list to a set by inserting all elements into the empty set. -/
abbrev ofList (l : List A) : S := ofListExtend l ∅

/-! ### Singleton lemmas -/

/-- Membership in singleton: true iff equal.  -/
theorem singleton_insert : ∀ {x : A}, { x } = insert x (∅ : S) := by
  intro x; ext p; rw [mem_singleton, mem_insert]
  simp [mem_empty]

/-! ### Insert operation -/

/-- Insert is defined as singleton union. -/
theorem insert_union : ∀ {x : A} {s : S}, insert x s = {x} ∪ s := by
  intro x s
  ext y; simp [mem_insert, mem_union, mem_singleton]

/-- Membership in insert when element differs: reduces to membership in original set. -/
theorem mem_insert_ne : ∀ {s : S} {x y : A}, x ≠ y →
    (x ∈ (insert y s) ↔ x ∈ s) := by
  intro s x y hne
  rw [mem_insert]
  simp [hne]

/-- Insert commutes with union. -/
theorem insert_union_comm {s₁ s₂ : S} {x : A} : insert x s₁ ∪ s₂ = insert x (s₁ ∪ s₂) := by
  ext y
  rw [mem_union, mem_insert, mem_insert, mem_union]
  grind

/-- Inserting an element that's already present doesn't change the set. -/
theorem insert_idem {s : S} {x : A} : x ∈ s → insert x s = s := by
  intro h; ext y; rw [mem_insert]; simp; intro hy; subst hy; exact h

/-- Double insert is idempotent. -/
theorem insert_insert {s : S} {x : A} : insert x (insert x s) = insert x s := by
  apply insert_idem; rw [mem_insert]; left; rfl

/-- Insert operations commute. -/
theorem insert_comm {s : S} {x y : A} : insert x (insert y s) = insert y (insert x s) := by
  ext z; rw [mem_insert, mem_insert, mem_insert, mem_insert]; grind

/-- Inserting into empty set yields singleton. -/
@[simp]
theorem insert_empty {x : A} : insert x (∅ : S) = {x} := by
  rw [singleton_insert]

/-- Inserting an element already in the set doesn't change membership of other elements. -/
theorem mem_insert_of_mem {s : S} {x y : A} : x ∈ s → x ∈ insert y s := by
  intro h; rw [mem_insert]; right; exact h

/-! ### Delete operation -/

/-- Membership in difference with singleton: false if equal. -/
theorem mem_diff_singleton_eq : ∀ {s : S} {x y : A}, x = y → ¬ x ∈ (s \ { y }) := by
  rintro s x y ⟨⟩
  rw [mem_diff, mem_singleton]
  rintro ⟨H1, H2⟩
  apply H2
  rfl

/-- Membership in difference with singleton: unchanged if not equal. -/
theorem mem_diff_singleton_ne :  ∀ (s : S) {x y : A}, x ≠ y → (x ∈ s ↔ x ∈ (s \ { y })) := by
  intro s x y H
  rw [mem_diff, mem_singleton]
  simp [H]

/-- Membership in difference: y ∈ X \ {x} ↔ y ∈ X ∧ y ≠ x -/
theorem mem_diff_singleton : ∀ {s : S} {x y : A},
  x ∈ (s \ { y }) ↔ (x ∈ s ∧ x ≠ y) := by
  intro s x y
  rw [mem_diff, mem_singleton]

/-- Deleting an element that's not in the set doesn't change it. -/
theorem delete_notin {s : S} {x : A} (h : x ∉ s) : delete x s = s := by
  ext y
  rw [mem_delete]
  exact ⟨fun ⟨hy, _⟩ => hy, fun hy => ⟨hy, fun heq => h (heq ▸ hy)⟩⟩

/-- Deleting an element and then inserting it back. -/
theorem insert_delete {s : S} {x : A} (h : x ∈ s) : insert x (delete x s) = s := by
  ext y
  rw [mem_insert, mem_delete]
  exact ⟨fun hh => Or.elim hh (fun heq => heq ▸ h) (fun hhy => hhy.1)
    , fun hy => Or.elim (Classical.em (y = x)) (fun heq => .inl heq) (fun hneq => .inr ⟨hy, hneq⟩)⟩

/-- Deleting an element from a set, then the result doesn't contain it. -/
theorem not_mem_delete {s : S} {x : A} : x ∉ delete x s := by
  rw [mem_delete]
  exact (·.2 rfl)

/-- Delete is idempotent. -/
theorem delete_delete {s : S} {x : A} : delete x (delete x s) = delete x s := by
  ext y
  rw [mem_delete, mem_delete]
  exact ⟨fun ⟨hhy, hne⟩ => hhy, fun hhy => ⟨hhy, hhy.2⟩⟩

/-- Deleting commutes. -/
theorem delete_comm {s : S} {x y : A} : delete x (delete y s) = delete y (delete x s) := by
  ext z
  rw [mem_delete, mem_delete, mem_delete, mem_delete]
  exact ⟨fun ⟨⟨hz, hne1⟩, hne2⟩ => ⟨⟨hz, hne2⟩, hne1⟩
    , fun ⟨⟨hz, hne1⟩, hne2⟩ => ⟨⟨hz, hne2⟩, hne1⟩⟩

/-- Deleting from empty set yields empty set. -/
@[simp]
theorem delete_empty {x : A} : delete x (∅ : S) = ∅ := by
  ext y
  simp [mem_delete, mem_empty]

/-- Delete distributes over union. -/
theorem delete_union {s₁ s₂ : S} {x : A} :
    delete x (s₁ ∪ s₂) = delete x s₁ ∪ delete x s₂ := by
  ext y
  simp only [mem_delete, mem_union]
  constructor
  · intro ⟨hh, hne⟩
    cases hh with
    | inl hh => left; exact ⟨hh, hne⟩
    | inr hh => right; exact ⟨hh, hne⟩
  · intro hh
    cases hh with
    | inl hhy => exact ⟨.inl hhy.1, hhy.2⟩
    | inr hhy => exact ⟨.inr hhy.1, hhy.2⟩

/-- Delete from singleton: empty if same element, singleton otherwise. -/
theorem delete_singleton [DecidableEq A] {x y : A} :
    delete x ({y} : S) = if x = y then ∅ else {y} := by
  by_cases h : x = y
  · subst h
    simp only [ite_true]
    ext z
    simp [mem_delete, mem_singleton, mem_empty]
  · simp only [h, ite_false]
    ext z
    rw [mem_delete, mem_singleton]
    apply Iff.intro
    · intro ⟨heq, _⟩; exact heq
    · intro heq; exact ⟨heq, fun hz => h (heq.symm.trans hz).symm⟩

/-- Deleting preserves subset relation. -/
theorem delete_subset_delete {s₁ s₂ : S} {x : A} :
    s₁ ⊆ s₂ → delete x s₁ ⊆ delete x s₂ := by
  intro hsub y hy
  rw [mem_delete] at hy ⊢
  exact ⟨hsub _ hy.1, hy.2⟩

/-- Delete is a subset of the original set. -/
theorem delete_subset {s : S} {x : A} : delete x s ⊆ s := by
  intro y hy
  rw [mem_delete] at hy
  exact hy.1

theorem delete_diff {s : S} {x : A} : delete x s = s \ {x} := by
  ext i; rw [mem_delete, mem_diff, mem_singleton]

/-! ### Union and Intersection operations -/

/-- Union is commutative. -/
@[symm]
theorem union_comm {s₁ s₂ : S} : s₁ ∪ s₂ = s₂ ∪ s₁ := by
  ext x; simp [mem_union]; grind only

/-- Intersection is commutative. -/
@[symm]
theorem inter_comm {s₁ s₂ : S} : s₁ ∩ s₂ = s₂ ∩ s₁ := by
  ext x; simp [mem_inter]; grind only

/-- Union is associative. -/
theorem union_assoc {s₁ s₂ s₃ : S} : s₁ ∪ (s₂ ∪ s₃) = s₁ ∪ s₂ ∪ s₃ := by
  ext x; simp [mem_union]; grind only

/-- Intersection is associative. -/
theorem inter_assoc {s₁ s₂ s₃ : S} : s₁ ∩ (s₂ ∩ s₃) = s₁ ∩ s₂ ∩ s₃ := by
  ext x; simp [mem_inter]; grind only

/-- Empty set is left identity for union. -/
@[simp]
theorem union_empty_left {s : S} : ∅ ∪ s = s := by
  ext x; simp [mem_union, mem_empty]

/-- Empty set is right identity for union. -/
@[simp]
theorem union_empty_right {s : S} : s ∪ ∅ = s := by
  ext x; simp [mem_union, mem_empty]

/-- Intersection with empty set is empty. -/
@[simp]
theorem inter_empty_left {s : S} : ∅ ∩ s = ∅ := by
  ext x; simp [mem_inter, mem_empty]

/-- Intersection with empty set is empty. -/
@[simp]
theorem inter_empty_right {s : S} : s ∩ ∅ = ∅ := by
  ext x; simp [mem_inter, mem_empty]

/-- Intersection distributes over union (left distributivity). -/
theorem inter_union_distrib {s₁ s₂ s₃ : S} : s₁ ∩ (s₂ ∪ s₃) = (s₁ ∩ s₂) ∪ (s₁ ∩ s₃) := by
  ext x; simp [mem_inter, mem_union]; grind only

/-- Union distributes over intersection (left distributivity). -/
theorem union_inter_distrib {s₁ s₂ s₃ : S} : s₁ ∪ (s₂ ∩ s₃) = (s₁ ∪ s₂) ∩ (s₁ ∪ s₃) := by
  ext x; simp [mem_inter, mem_union]; grind only

/-- Union is idempotent. -/
@[simp]
theorem union_idem {s : S} : s ∪ s = s := by
  ext x; rw [mem_union]; simp

/-- Intersection is idempotent. -/
@[simp]
theorem inter_idem {s : S} : s ∩ s = s := by
  ext x; rw [mem_inter]; simp

/-! ### Subset relations -/

/-- Empty set is a subset of every set. -/
@[simp]
theorem empty_subset {s : S} : ∅ ⊆ s := by
  intro y; simp [mem_empty]

/-- Insert preserves subset relation. -/
theorem insert_subset_subset {s₁ s₂ : S} {x : A} :
  s₁ ⊆ s₂ → insert x s₁ ⊆ insert x s₂ := by
  intro H y; rw [mem_insert, mem_insert]
  intro G; cases G with
  | inl G => left; assumption
  | inr G => right; apply H _ G

/-- Subset relation is reflexive. -/
@[refl]
theorem subset_refl {s : S} : s ⊆ s := by
  intro x _; assumption

/-- Subset relation is transitive. -/
theorem subset_trans {s₁ s₂ s₃ : S} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := by
  intro h1 h2 x hx; exact h2 _ (h1 _ hx)

/-! ### Disjointness -/

/-- Disjoint sets have empty intersection and vice versa. -/
theorem disjoint_intersection {X Y : S} : X ## Y ↔ X ∩ Y = ∅ := by
  simp only [Disjoint.disjoint]
  apply Iff.intro
  · intro H
    ext x; rw [mem_inter]
    simp [H, mem_empty]
  · intro H x
    rw [<-mem_inter, H]
    apply mem_empty

/-- Disjointness is symmetric.  -/
theorem disjoint_comm {s₁ s₂ : S} : s₁ ## s₂ ↔ s₂ ## s₁ := by
  simp only [Disjoint.disjoint]; apply Iff.intro <;> (intro h x ⟨hx1, hx2⟩; exact h x ⟨hx2, hx1⟩)

@[symm]
theorem disjoint_symm {s₁ s₂ : S} : s₁ ## s₂ → s₂ ## s₁ := disjoint_comm.mp

/-- Empty set is disjoint with any set (left). -/
theorem disjoint_empty_left {s : S} : ∅ ## s := by
  intro x ⟨h, _⟩; exact mem_empty h

/-- Empty set is disjoint with any set (right).  -/
theorem disjoint_empty_right {s : S} : s ## ∅ := by
  intro x ⟨_, h⟩; exact mem_empty h

/-- Singleton disjointness. -/
theorem disjoint_singleton_left {s : S} {x : A} : {x} ## s ↔ x ∉ s := by
  simp only [Disjoint.disjoint]
  apply Iff.intro
  · intro h hx; exact h x ⟨(mem_singleton.mpr rfl), hx⟩
  · intro h y ⟨hy1, hy2⟩; rw [mem_singleton] at hy1; subst hy1; exact h hy2

/-- Singleton disjointness (right). -/
theorem disjoint_singleton_right {s : S} {x : A} : s ## {x} ↔ x ∉ s := by
  rw [disjoint_comm, disjoint_singleton_left]

/-- Disjoint sets remain disjoint when taking subsets. -/
theorem disjoint_subset_left {s₁ s₂ t : S} : s₁ ⊆ s₂ → s₂ ## t → s₁ ## t := by
  intro hsub hdisj x ⟨hx1, hx2⟩
  exact hdisj x ⟨hsub _ hx1, hx2⟩

/-- Disjoint sets remain disjoint when taking subsets (right). -/
theorem disjoint_subset_right {s₁ s₂ t : S} : s₁ ⊆ s₂ → t ## s₂ → t ## s₁ := by
  intro hsub hdisj x ⟨hx1, hx2⟩
  exact hdisj x ⟨hx1, hsub _ hx2⟩

/-- Union is disjoint iff both parts are disjoint. -/
theorem disjoint_union_left {s₁ s₂ t : S} : (s₁ ∪ s₂) ## t ↔ s₁ ## t ∧ s₂ ## t := by
  simp only [Disjoint.disjoint]
  apply Iff.intro
  · intro h; apply And.intro
    · intro x ⟨hx1, hx2⟩; exact h x ⟨(mem_union.mpr (.inl hx1)), hx2⟩
    · intro x ⟨hx1, hx2⟩; exact h x ⟨(mem_union.mpr (.inr hx1)), hx2⟩
  · intro ⟨h1, h2⟩ x ⟨hx1, hx2⟩
    rw [mem_union] at hx1; cases hx1 with
    | inl hx1 => exact h1 x ⟨hx1, hx2⟩
    | inr hx1 => exact h2 x ⟨hx1, hx2⟩

/-- Union is disjoint iff both parts are disjoint (right). -/
theorem disjoint_union_right {s₁ s₂ t : S} : t ## (s₁ ∪ s₂) ↔ t ## s₁ ∧ t ## s₂ := by
  rw [disjoint_comm, disjoint_union_left, disjoint_comm (s₂ := s₁), disjoint_comm (s₂ := s₂)]

/-- Disjointness is decidable when set equality is decidable. -/
instance disjoint_dec [DecidableEq S] : DecidableDisj S where
  decide_disj := by
    intro E1 E2
    rw [disjoint_intersection]
    infer_instance

/-! ### Difference operations -/

/-- Difference with empty set is identity. -/
@[simp]
theorem diff_empty {s : S} :
  s \ ∅ = s := by
  ext x; rw [mem_diff]; simp [mem_empty]

/-- Self-difference is empty. -/
@[simp]
theorem diff_all {s : S} :
  s \ s = ∅ := by
  ext x; rw [mem_diff]; simp [mem_empty]

/-- Difference is a subset of the left set. -/
theorem diff_subset_left {s₁ s₂ : S} :
  s₁ \ s₂ ⊆ s₁ := by
  intro y G; rw [mem_diff] at G
  exact G.left

/-- Difference with disjoint set is identity. -/
theorem diff_subset_disj {s₁ s₂ : S} :
  s₁ ## s₂ → s₁ \ s₂ = s₁ := by
  intro H
  ext x; rw [mem_diff]
  rw [disjoint_intersection] at H
  apply Iff.intro
  · rintro ⟨G, _⟩; assumption
  · intro G
    by_cases hin : x ∈ s₂
    · exfalso
      apply (mem_empty (S := S) (x := x))
      rw [<-H, mem_inter]
      exact ⟨G, hin⟩
    · exact ⟨G, hin⟩

/-- A superset can be decomposed into the subset and its difference. -/
theorem diff_subset_decomp {s₁ s₂ : S} :
  s₁ ⊆ s₂ → s₂ = (s₂ \ s₁) ∪ s₁ := by
  intro H
  ext x; rw [mem_union, mem_diff]
  apply Iff.intro
  · intro G
    by_cases J : x ∈ s₁
    · right; assumption
    · left; exact ⟨G, J⟩
  · intro G
    cases G with
    | inl G =>
      exact G.left
    | inr G =>
      apply H _ G

/-- De Morgan's law: difference distributes over union. -/
theorem diff_union {s₁ s₂ s₃ : S} : s₁ \ (s₂ ∪ s₃) = (s₁ \ s₂) ∩ (s₁ \ s₃) := by
  ext x; rw [mem_diff, mem_union, mem_inter, mem_diff, mem_diff]
  grind only

/-- De Morgan's law: difference distributes over intersection. -/
theorem diff_inter {s₁ s₂ s₃ : S} : s₁ \ (s₂ ∩ s₃) = (s₁ \ s₂) ∪ (s₁ \ s₃) := by
  ext x; rw [mem_diff, mem_inter, mem_union, mem_diff, mem_diff]
  grind only

/-- Difference distributes over union (right). -/
theorem union_diff_distrib_right {s₁ s₂ s₃ : S} : (s₁ ∪ s₂) \ s₃ = (s₁ \ s₃) ∪ (s₂ \ s₃) := by
  ext x; rw [mem_diff, mem_union, mem_union, mem_diff, mem_diff]; grind only

/-- Intersection with difference. -/
theorem inter_diff {s₁ s₂ s₃ : S} : (s₁ ∩ s₂) \ s₃ = s₁ ∩ (s₂ \ s₃) := by
  ext x; rw [mem_diff, mem_inter, mem_inter, mem_diff]; grind only

/-! ### Additional subset lemmas -/

/-- A set is a subset of itself with an element inserted. -/
theorem insert_subset {s : S} {x : A} :
  s ⊆ insert x s := by
  intro y G; rw [mem_insert]
  right; assumption

/-- Left set is a subset of union. -/
theorem union_subset_left {s₁ s₂ : S} :
  s₁ ⊆ s₁ ∪ s₂ := by
  intro y G; rw [mem_union]
  left; assumption

/-- Right set is a subset of union. -/
theorem union_subset_right {s₁ s₂ : S} :
  s₂ ⊆ s₁ ∪ s₂ := by
  intro y G; rw [mem_union]
  right; assumption

/-- Intersection is a subset of left set. -/
theorem inter_subset_left {s₁ s₂ : S} :
  s₁ ∩ s₂ ⊆ s₁ := by
  intro y G; rw [mem_inter] at G
  exact G.left

/-- Intersection is a subset of right set. -/
theorem inter_subset_right {s₁ s₂ : S} :
  s₁ ∩ s₂ ⊆ s₂ := by
  intro y G; rw [mem_inter] at G
  exact G.right

/-! ### Membership and equality lemmas -/

/-- Membership is preserved by subset. -/
theorem mem_of_subset {s₁ s₂ : S} {x : A} : s₁ ⊆ s₂ → x ∈ s₁ → x ∈ s₂ := by
  intro h hx; exact h _ hx

/-- Non-membership in subset implies non-membership in original. -/
theorem not_mem_of_not_mem_subset {s₁ s₂ : S} {x : A} : s₁ ⊆ s₂ → x ∉ s₂ → x ∉ s₁ := by
  intro h hnx hx; exact hnx (h _ hx)

/-- Empty iff every element is not a member. -/
theorem eq_empty_iff {s : S} : s = ∅ ↔ ∀ x, x ∉ s := by
  apply Iff.intro
  · intro h x; subst h; exact mem_empty
  · intro h; ext x; simp [mem_empty]; exact h x

/-- Non-empty iff there exists a member. -/
theorem nonempty_iff {s : S} : s ≠ ∅ ↔ ∃ x, x ∈ s := by
  apply Iff.intro
  · intro H
    by_cases G : ∃ x, x ∈ s
    · assumption
    · exfalso
      apply H
      ext p; grind only [mem_empty]
  · rintro ⟨x, G⟩
    grind only [mem_empty]

/-- Singleton equality. -/
theorem singleton_eq_singleton {x y : A} : ({x} : S) = {y} ↔ x = y := by
  apply Iff.intro
  · intro h; have : x ∈ ({y} : S) := by rw [<-h, mem_singleton]
    rw [mem_singleton] at this; exact this
  · rintro ⟨⟩; rfl

/-- Union with subset absorption. -/
theorem union_subset_absorption {s₁ s₂ : S} : s₁ ⊆ s₂ → s₁ ∪ s₂ = s₂ := by
  intro h; ext x; rw [mem_union]; apply Iff.intro
  · intro hx; cases hx with
    | inl hx => exact h _ hx
    | inr hx => exact hx
  · intro hx; right; exact hx

/-- Intersection with subset absorption. -/
theorem inter_subset_absorption {s₁ s₂ : S} : s₁ ⊆ s₂ → s₁ ∩ s₂ = s₁ := by
  intro h; ext x; rw [mem_inter]; apply Iff.intro
  · intro ⟨hx, _⟩; exact hx
  · intro hx; exact ⟨hx, h _ hx⟩

/-! ### Predicates (setForall and setExists) -/

/-- Forall predicate on sets. -/
def setForall (P : A → Prop) (X : S) : Prop :=
  ∀ x, x ∈ X → P x

/-- Exists predicate on sets. -/
def setExists (P : A → Prop) (X : S) : Prop :=
  ∃ x, x ∈ X ∧ P x

/-- setForall holds trivially for empty set. -/
theorem setForall_empty {P : A → Prop} : setForall P (∅ : S) ↔ True := by
  simp [setForall]; intro x h; grind only [mem_empty]

/-- setForall for singleton reduces to the predicate. -/
theorem setForall_singleton {P : A → Prop} {x : A} :
  setForall P ({x} : S) ↔ P x := by
  simp [setForall]; apply Iff.intro
  · intro h; apply h; rw [mem_singleton]
  · intro h y hy; rw [mem_singleton] at hy; subst hy; exact h

/-- setForall distributes over union. -/
theorem setForall_union {P : A → Prop} {s₁ s₂ : S} :
  setForall P (s₁ ∪ s₂) ↔ setForall P s₁ ∧ setForall P s₂ := by
  simp [setForall]; apply Iff.intro
  · intro h; apply And.intro
    · intro x hx; apply h; rw [mem_union]; left; exact hx
    · intro x hx; apply h; rw [mem_union]; right; exact hx
  · intro ⟨h1, h2⟩ x hx; rw [mem_union] at hx; cases hx with
    | inl hx => exact h1 _ hx
    | inr hx => exact h2 _ hx

/-- setExists is false for empty set. -/
theorem setExists_empty {P : A → Prop} : setExists P (∅ : S) ↔ False := by
  simp [setExists, mem_empty]

/-- setExists for singleton reduces to the predicate. -/
theorem setExists_singleton {P : A → Prop} {x : A} :
  setExists P ({x} : S) ↔ P x := by
  simp [setExists]; apply Iff.intro
  · intro ⟨y, hy, hP⟩; rw [mem_singleton] at hy; subst hy; exact hP
  · intro h; exists x; apply And.intro; rw [mem_singleton]; exact h

/-- setExists distributes over union. -/
theorem setExists_union {P : A → Prop} {s₁ s₂ : S} :
  setExists P (s₁ ∪ s₂) ↔ setExists P s₁ ∨ setExists P s₂ := by
  simp [setExists]; apply Iff.intro
  · intro ⟨x, hx, hP⟩; rw [mem_union] at hx; cases hx with
    | inl hx => left; exists x
    | inr hx => right; exists x
  · grind only [mem_union]

/-- Relationship between setForall and setExists. -/
theorem setForall_not_setExists {P : A → Prop} {s : S} :
  setForall (fun x => ¬P x) s ↔ ¬setExists P s := by
  simp [setForall, setExists]

private theorem ofListExtend_nil {s : S} : ofListExtend [] s = s := by
  simp [ofListExtend]

private theorem ofListExtend_subset {s : S} {xs : List A} :
  s ⊆ ofListExtend xs s := by
  induction xs generalizing s with
  | nil =>
    intro z
    simp [ofListExtend_nil]
  | cons y ys IH =>
    intro z
    simp only [ofListExtend, List.foldl_cons]
    intro H
    apply IH
    rw [mem_insert]
    right; assumption

private theorem ofListExtend_subset_subset {s₁ s₂ : S} {xs : List A} :
  s₁ ⊆ s₂ →
  ofListExtend xs s₁ ⊆ ofListExtend xs s₂ := by
  induction xs generalizing s₁ s₂ with
  | nil =>
    intro z
    simp [ofListExtend_nil]; assumption
  | cons y ys IH =>
    intro z
    simp only [ofListExtend, List.foldl_cons]
    intro H
    apply IH
    apply insert_subset_subset z

private theorem ofListExtend_cons {s : S} {x : A} {xs : List A} :
    ofListExtend (x :: xs) s = ofListExtend xs (insert x s) := by
  simp [ofListExtend, List.foldl_cons]

private theorem ofListExtend_classify {s : S} {xs : List A} :
    ofListExtend xs s = s ∪ ofListExtend xs (∅ : S) := by
  induction xs generalizing s with
  | nil =>
    simp [ofListExtend_nil, union_empty_right]
  | cons x xs IH =>
    simp only [ofListExtend_cons]
    rw [IH]
    ext z; rw [mem_union, mem_insert]
    apply Iff.intro
    · intro G
      rw [mem_union]
      cases G with
      | inl G =>
        cases G with
        | inl G =>
          subst G
          right
          apply ofListExtend_subset
          simp [mem_singleton]
        | inr G =>
          left; assumption
      | inr G =>
        right
        apply ofListExtend_subset_subset (s₁ := ∅)
        · apply empty_subset
        · assumption
    · rw [mem_union]
      intro G
      cases G with
      | inl G =>
        left; right; assumption
      | inr G =>
        by_cases heq : z = x
        · subst heq
          left; left; rfl
        · right
          rw [IH, mem_union] at G
          cases G with
          | inl G =>
            simp [mem_singleton] at G
            exfalso; apply heq G
          | inr G =>
            assumption

private theorem ofListExtend_cons_comm {s : S} {x : A} {xs : List A} :
  ofListExtend (x :: xs) s = insert x (ofListExtend xs s) := by
  ext y
  by_cases heq : x = y
  · rw [mem_insert, ofListExtend_cons]
    subst heq
    simp only [true_or, iff_true]
    apply ofListExtend_subset
    rw [mem_insert]; left; rfl
  · simp only [mem_insert_ne (fun c => heq (Eq.symm c))]
    rw [ofListExtend_cons]
    apply Iff.intro
    · intro H
      rw [ofListExtend_classify, mem_union]; rw [ofListExtend_classify, mem_union] at H
      rw [mem_insert_ne (fun c => heq (Eq.symm c))] at H
      apply H
    · intro H
      apply ofListExtend_subset_subset (s₁ := s)
      · apply insert_subset
      · apply H

/-- Converting empty list to set yields empty set. -/
@[simp]
theorem ofList_nil : ofList [] = (∅ : S) := by
  simp [ofList]; exact ofListExtend_nil

/-- Converting a cons to a set yields insertion into converted tail. -/
@[simp]
theorem ofList_cons : ofList (x :: xs) = insert x ((ofList xs) : S) := by
  simp [ofList]; exact ofListExtend_cons_comm

/-- Membership in list corresponds to membership in converted set. -/
theorem mem_ofList {x : A} {xs : List A} : x ∈ xs ↔ x ∈ (ofList xs : S) := by
  induction xs with
  | nil =>
    simp only [ofList_nil, List.not_mem_nil]
    exact Iff.intro (fun h => h.elim) (fun h => mem_empty h)
  | cons y ys IH =>
    simp only [List.mem_cons, ofList_cons, mem_insert]
    grind only

/-- Converting concatenated lists yields union of converted lists. -/
theorem ofList_concat {xs ys : List A} : (ofList (xs ++ ys) : S) = ofList xs ∪ ofList ys := by
  ext p; simp [mem_union, <-mem_ofList, <-mem_ofList, <-mem_ofList]

end GenLemmas

end LawfulSet

namespace FiniteSet

open LawfulSet

/-- Map operation on sets. Maps a function over all elements. -/
def map {S S' : Type _} {A B : Type _}
  [FiniteSet S A] [FiniteSet S' B]
  (f : A → B) (s : S) : S' :=
  ofList (S := S') (A := B) (List.map f (toList s))

/-- Bind operation on sets. Flatmap a function over all elements. -/
def bind {S S' : Type _} {A B : Type _} [FiniteSet S A] [FiniteSet S' B]
  (f : A → S') (s : S) : S' :=
  ofList (List.flatMap (fun x => toList (f x)) (toList s))

/-- The cardinality (size) of a finite set, defined as the length of its list representation. -/
def size {S : Type _} {A : Type _} [FiniteSet S A] (s : S) : Nat :=
  (toList s).length

/-- Fold over a finite set. -/
def fold [FiniteSet S A] {β : Type _} (f : β → A → β)
    (init : β) (s : S) : β :=
  (toList s).foldl f init

def filter [FiniteSet S A] (p : A → Bool) (s : S) : S :=
  ofList ((toList s).filter p)

section FinLemmas

variable {S : Type _} {A : Type _} [inst : LawfulFiniteSet S A]

/-- Membership in `toList` corresponds to membership in the set. -/
theorem mem_toList {k : A} {m : S} : k ∈ toList m ↔ k ∈ m := by
  simp only [toList]
  exact LawfulFiniteSet.mem_toList

theorem toList_nodup {m : S} : (toList m).Nodup := by
  simp only [toList]
  exact LawfulFiniteSet.toList_nodup

/-- toList of empty set is empty. -/
theorem toList_empty : toList (∅ : S) = [] := by
  have hnodup : (toList (∅ : S)).Nodup := LawfulFiniteSet.toList_nodup
  cases h : toList (∅ : S) with
  | nil => rfl
  | cons x xs =>
    exfalso
    have : x ∈ toList (∅ : S) := by rw [h]; simp [List.mem_cons]
    rw [mem_toList] at this
    exact mem_empty this

theorem toList_singleton {x : A} : toList ({x} : S) = [x] := by
  have hnodup : (toList ({x} : S)).Nodup := LawfulFiniteSet.toList_nodup
  cases h : toList ({x} : S) with
  | nil =>
    exfalso
    have : x ∈ ({x} : S) := by rw [mem_singleton]
    rw [<-mem_toList, h] at this
    simp [List.not_mem_nil] at this
  | cons y ys =>
    have hy : y ∈ toList ({x} : S) := by rw [h]; simp [List.mem_cons]
    rw [mem_toList, mem_singleton] at hy
    cases hys : ys with
    | nil =>
      simp [hy]
    | cons z zs =>
      exfalso
      have hnodup' : (y :: z :: zs).Nodup := by rw [<-hys, <-h]; exact hnodup
      have hz : z ∈ toList ({x} : S) := by rw [h, hys]; simp [List.mem_cons]
      rw [mem_toList, mem_singleton] at hz
      rw [hy] at hnodup'
      rw [hz] at hnodup'
      rw [List.nodup_cons] at hnodup'
      simp [List.mem_cons] at hnodup'

/-- Membership in toList of union corresponds to membership in concatenated lists. -/
theorem mem_toList_union :
  ∀ x, x ∈ toList (s₁ ∪ s₂ : S) ↔ x ∈ toList s₁ ++ toList s₂ := by
  intro x
  rw [mem_toList, mem_union, List.mem_append, mem_toList, mem_toList]

/-- Converting a set to canonical form and back yields the original set. -/
theorem ofList_toList {m : S} :
  (ofList (toList m)) = m := by
  ext k
  rw [<-mem_ofList, mem_toList]

/-- Membership in mapped set. -/
theorem mem_map {S' : Type _} {B : Type _} [LawfulFiniteSet S' B] (f : A → B) (s : S) (x : B) :
  x ∈ map (S' := S') f s ↔ ∃ y, f y = x ∧ y ∈ s := by
  simp only [map, <-mem_ofList, List.mem_map, mem_toList]
  grind only

/-- Mapping over empty set yields empty set. -/
@[simp]
theorem map_empty {S' : Type _} {B : Type _} [LawfulFiniteSet S' B] (f : A → B) :
  map (S' := S') f (∅ : S) = ∅ := by
  ext x; rw [mem_map]; simp [mem_empty]

/-- Mapping identity yields original set. -/
@[simp]
theorem map_id {S' : Type _} {B : Type _} [LawfulFiniteSet S' B] (s : S) :
  map (S' := S) id s = s := by
  ext x; rw [mem_map]; simp

/-- Mapping composed functions equals composing mapped functions. -/
theorem map_comp {S' S'' : Type _} {B C : Type _}
  [LawfulFiniteSet S' B] [LawfulFiniteSet S'' C]
  (f : A → B) (g : B → C) (s : S) :
  map (S' := S'') (g ∘ f) s = map (S' := S'') g (map (S' := S') f s) := by
  ext x; rw [mem_map, mem_map]; grind [mem_map]

/-- Map distributes over union. -/
theorem map_union {S' : Type _} {B : Type _} [LawfulFiniteSet S' B]
    (f : A → B) (s₁ s₂ : S) :
  map (S' := S') f (s₁ ∪ s₂) = map f s₁ ∪ map f s₂ := by
  ext y; rw [mem_map, mem_union, mem_map, mem_map]
  apply Iff.intro
  · intro ⟨x, hf, hx⟩; rw [mem_union] at hx; cases hx with
    | inl hx => left; exists x
    | inr hx => right; exists x
  · grind only [mem_union]

/-- Map over singleton. -/
theorem map_singleton {S' : Type _} {B : Type _} [LawfulFiniteSet S' B]
    (f : A → B) (x : A) :
  map (S' := S') f ({x} : S) = {f x} := by
  ext y; rw [mem_map, mem_singleton]
  apply Iff.intro
  · intro ⟨z, hf, hz⟩; rw [mem_singleton] at hz; subst hz; exact (Eq.symm hf)
  · intro h; subst h; exists x; apply And.intro rfl; rw [mem_singleton]

/-- Map preserves subset relation. -/
theorem map_subset {S' : Type _} {B : Type _} [LawfulFiniteSet S' B]
    (f : A → B) (s₁ s₂ : S) :
  s₁ ⊆ s₂ → map (S' := S') f s₁ ⊆ map (S' := S') f s₂ := by
  intro h y hy; rw [mem_map] at hy ⊢
  obtain ⟨x, hf, hx⟩ := hy
  exists x; exact ⟨hf, h _ hx⟩

private theorem nodup_map_of_injective {B : Type _} {f : A → B} {l : List A}
    (hinj : Injective f) (hnodup : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp [List.Nodup]
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [List.nodup_cons] at hnodup ⊢
    simp only [List.mem_map]
    constructor
    · intro ⟨y, hy, heq⟩
      cases (hinj.inj _ _ heq.symm)
      exact hnodup.1 hy
    · exact ih hnodup.2

theorem toList_map_perm {S' : Type _} {B : Type _} [LawfulFiniteSet S' B]
    {f : A → B} (s : S) (hinj : Injective f) :
    (toList (map (S' := S') f s)).Perm (List.map f (toList s)) := by
  simp only [map]
  have hnodup : (List.map f (toList s)).Nodup := by
    apply nodup_map_of_injective hinj
    exact toList_nodup
  apply (List.perm_ext_iff_of_nodup toList_nodup hnodup).mpr
  intro x
  simp [mem_toList, <-mem_ofList]

/-- Permutation-equivalent lists convert to the same set. -/
theorem ofList_congr {l l' : List A} :
  List.Perm l l' → (ofList l : S) = ofList l' := by
  intro H; ext x
  rw [<-mem_ofList, <-mem_ofList]
  induction H <;> grind only [List.mem_cons]

/-- Membership in bind. -/
theorem mem_bind [LawfulFiniteSet S' B]
    (f : A → S') (X : S) (y : B) :
    y ∈ bind (S' := S') f X ↔ ∃ x, x ∈ X ∧ y ∈ (f x) := by
  simp only [bind, <-mem_ofList, List.mem_flatMap, mem_toList]

/-- Bind over empty set is empty. -/
@[simp]
theorem bind_empty [LawfulFiniteSet S' B]
    (f : A → S') :
  bind (S' := S') f (∅ : S) = ∅ := by
  ext y; rw [mem_bind]; simp [mem_empty]

/-- Bind over singleton. -/
@[simp]
theorem bind_singleton [LawfulFiniteSet S' B]
    (f : A → S') (x : A) :
  bind (S' := S') f ({x} : S) = f x := by
  ext y; rw [mem_bind]; apply Iff.intro
  · intro ⟨z, hz, hy⟩; rw [mem_singleton] at hz; subst hz; exact hy
  · intro hy; exists x; apply And.intro; rw [mem_singleton]; exact hy

/-- Bind distributes over union. -/
theorem bind_union [LawfulFiniteSet S' B]
    (f : A → S') (s₁ s₂ : S) :
  bind (S' := S') f (s₁ ∪ s₂) = bind f s₁ ∪ bind f s₂ := by
  ext y; rw [mem_bind, mem_union, mem_bind, mem_bind]
  apply Iff.intro <;> grind only [mem_union]

/-- Membership in filtered set. -/
theorem mem_filter (p : A → Bool) (s : S) (x : A) :
  x ∈ filter p s ↔ x ∈ s ∧ p x := by
  simp only [filter, <-mem_ofList, List.mem_filter, mem_toList]

/-- Filter over empty set is empty. -/
@[simp]
theorem filter_empty (p : A → Bool) :
  filter p (∅ : S) = ∅ := by
  ext x; rw [mem_filter]; simp [mem_empty]

/-- Filter over singleton. -/
theorem filter_singleton (p : A → Bool) (x : A) :
  filter p ({x} : S) = if p x then {x} else ∅ := by
  ext y
  rw [mem_filter, mem_singleton]
  by_cases hp : p x
  · grind only [mem_singleton]
  · grind only [mem_singleton, mem_empty]

/-- Filter distributes over union. -/
theorem filter_union (p : A → Bool) (s₁ s₂ : S) :
  filter p (s₁ ∪ s₂) = filter p s₁ ∪ filter p s₂ := by
  ext x
  grind only [mem_filter, mem_union, mem_union, mem_filter, mem_filter]

/-- Filter with always-true predicate is identity. -/
theorem filter_true (s : S) :
  filter (fun _ => true) s = s := by
  ext x; rw [mem_filter]; simp

/-- Filter with always-false predicate is empty. -/
theorem filter_false (s : S) :
  filter (fun _ => false) s = ∅ := by
  ext x; rw [mem_filter]; simp [mem_empty]

/-- Consecutive filters can be combined. -/
theorem filter_filter (p q : A → Bool) (s : S) :
  filter p (filter q s) = filter (fun x => p x && q x) s := by
  ext x
  rw [mem_filter, mem_filter, mem_filter]
  simp [Bool.and_eq_true]
  grind only

/-- Filter distributes over difference. -/
theorem filter_diff (p : A → Bool) (s₁ s₂ : S) :
  filter p (s₁ \ s₂) = filter p s₁ \ filter p s₂ := by
  ext x
  grind only [mem_filter, mem_diff]

/-- Filter distributes over intersection. -/
theorem filter_inter (p : A → Bool) (s₁ s₂ : S) :
  filter p (s₁ ∩ s₂) = filter p s₁ ∩ filter p s₂ := by
  ext x
  grind only [mem_filter, mem_inter]

/-- Filter over insert. -/
theorem filter_insert (p : A → Bool) (x : A) (s : S) :
  filter p (insert x s) = if p x then insert x (filter p s) else filter p s := by
  ext y
  rw [mem_filter, mem_insert]
  by_cases hp : p x
  · simp [hp, mem_insert, mem_filter]
    grind only
  · simp [hp, mem_filter]
    grind only

/-- Filter over delete. -/
theorem filter_delete (p : A → Bool) (x : A) (s : S) :
  filter p (delete x s) = delete x (filter p s) := by
  ext y
  grind only [mem_filter, mem_delete]

/-- A set has size 0 iff it is empty. -/
theorem size_empty {X : S} : size X = 0 ↔ X = ∅ := by
  simp only [size]
  apply Iff.intro
  · intro heq
    ext x; simp [mem_empty]
    rw [<-mem_toList]
    cases h : toList X with
    | nil => simp [List.not_mem_nil]
    | cons y ys =>
      exfalso
      rw [h] at heq
      simp [List.length_cons] at heq
  · intro heq; rw [heq]
    rw [toList_empty]
    simp [List.length_nil]

theorem set_choose (X : S) (h : size X ≠ 0) : ∃ x, x ∈ X := by
  unfold size at h
  cases hlist : toList X with
  | nil =>
    exfalso
    apply h
    rw [hlist]
    rfl
  | cons x xs =>
    exists x
    rw [<-mem_toList, hlist]
    simp [List.mem_cons]

theorem size_union {X Y : S} (h : X ## Y) : size X + size Y = size (X ∪ Y) := by
  simp only [size, <-List.length_append]
  have h_disj : ∀ x, x ∈ toList X → x ∉ toList Y := by
    intro x hx hy
    rw [mem_toList] at hx hy
    exact h _ ⟨hx, hy⟩

  have hnodup_X : (toList X).Nodup := LawfulFiniteSet.toList_nodup
  have hnodup_Y : (toList Y).Nodup := LawfulFiniteSet.toList_nodup
  have hnodup_XY : (toList (X ∪ Y)).Nodup := LawfulFiniteSet.toList_nodup

  have hnodup_append : (toList X ++ toList Y).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnodup_X, hnodup_Y, ?_⟩
    intro a ha b hb heq
    subst heq
    exact h_disj a ha hb

  have h_mem : ∀ z, z ∈ toList (X ∪ Y) ↔ z ∈ toList X ++ toList Y := by
    intro z
    rw [mem_toList, mem_union, List.mem_append, mem_toList, mem_toList]
  have : (toList (X ∪ Y)).length = (toList X ++ toList Y).length := by
    apply Nat.le_antisymm
    · apply List.Subperm.length_le
      apply List.subperm_of_subset hnodup_XY
      intro a ha
      rw [h_mem] at ha
      exact ha
    · apply List.Subperm.length_le
      apply List.subperm_of_subset hnodup_append
      intro a ha
      rw [mem_toList, mem_union]
      rw [List.mem_append, mem_toList, mem_toList] at ha
      exact ha

  rw [this]

/-- Proper subsets have strictly smaller size. -/
theorem size_ssubset {X Y : S} (h : X ⊂ Y) : size X < size Y := by
  have heq : Y = Y \ X ∪ X := by
    apply diff_subset_decomp
    rw [ssubset_subset] at h
    exact h.left
  rw [heq]; clear heq
  rw [<-size_union]
  · have : size (Y \ X) > 0 := by
      false_or_by_contra; rename_i G; simp only [gt_iff_lt, Nat.not_lt, Nat.le_zero_eq] at G
      rw [size_empty] at G
      rw [ssubset_subset] at h
      apply h.right
      ext x
      apply Iff.intro
      · intro J
        apply h.left _ J
      · intro J
        by_cases hin : x ∈ X
        · assumption
        · exfalso
          have : x ∈ Y \ X ↔ x ∈ (∅ : S) := by
            rw [G]
          rw [mem_diff] at this
          grind only [mem_empty]
    omega
  · rw [disjoint_intersection]
    ext p; rw [mem_inter, mem_diff]; simp [mem_empty]

/-- Size of singleton is 1. -/
theorem size_singleton {x : A} : size ({x} : S) = 1 := by
  unfold size
  rw [toList_singleton]
  rfl

/-- Size of insert when element not present. -/
theorem size_insert_not_mem {s : S} {x : A} :
  x ∉ s → size (insert x s) = size s + 1 := by
  intro h
  rw [insert_union]
  have hdisj : {x} ## s := by
    rw [disjoint_singleton_left]
    exact h
  rw [<-size_union hdisj, size_singleton]
  omega

/-- Size of insert when element already present. -/
theorem size_insert_mem {s : S} {x : A} :
  x ∈ s → size (insert x s) = size s := by
  intro h
  rw [insert_idem h]

/-- Non-empty sets have positive size. -/
theorem size_pos {s : S} : s ≠ ∅ → size s > 0 := by
  intro h; simp only [ne_eq, ← size_empty] at h; omega

/-- Subset implies size inequality. -/
theorem size_subset {s₁ s₂ : S} : s₁ ⊆ s₂ → size s₁ ≤ size s₂ := by
  intro h
  by_cases heq : s₁ = s₂
  · subst heq; apply Nat.le_refl
  · have : s₁ ⊂ s₂ := by rw [ssubset_subset]; exact ⟨h, heq⟩
    exact Nat.le_of_lt (size_ssubset this)

/-- Well-founded relation on finite sets based on proper subset. -/
theorem set_wf : WellFounded (SSubset (α := S)) := by
  apply Subrelation.wf
  · intro X Y hrel
    exact (size_ssubset hrel)
  · exact (measure (size (S := S) (A := A))).wf

/-- Induction principle for finite sets. -/
theorem set_ind {P : S → Prop}
    (hemp : P ∅)
    (hadd : ∀ x X, x ∉ X → P X → P (insert x X))
    (X : S) : P X := by
  apply WellFounded.induction set_wf X
  intro Y IH
  by_cases hempty : size Y = 0
  · rw [size_empty] at hempty
    subst hempty
    apply hemp
  · obtain ⟨x, hmem⟩ := set_choose Y hempty
    let Y' := Y \ {x}
    have hnotin : x ∉ Y' := by
      subst Y'
      simp [mem_diff, mem_singleton]
    have hPY' : P Y' := by
      apply IH
      subst Y'
      rw [ssubset_subset]
      apply And.intro
      · intro p; rw [mem_diff, mem_singleton]
        grind only
      · intro H; rw [<-H] at hmem
        rw [mem_diff, mem_singleton] at hmem
        apply hmem.right rfl
    have heq : Y =  {x} ∪ Y' := by
      ext z
      subst Y'
      rw [mem_union, mem_singleton, mem_diff, mem_singleton]
      rw [mem_diff, mem_singleton] at hnotin
      grind only
    have : P ({x} ∪ Y') := by
      rw [singleton_insert, insert_union_comm, union_empty_left]
      apply hadd
      · subst Y'; rw [mem_diff, mem_singleton]
        rintro ⟨_, H⟩; apply H rfl
      · assumption
    rw [heq]
    exact this

@[simp]
theorem fold_empty {β : Type _} {f : β → A → β} {init : β} :
    fold f init (∅ : S) = init := by
  simp only [fold, toList_empty, List.foldl_nil]

@[simp]
theorem fold_singleton {β : Type _} {f : β → A → β} {init : β} {a : A} :
    fold f init ({a} : S) = f init a := by
  simp only [fold, toList_singleton, List.foldl_cons, List.foldl_nil]

private theorem foldl_perm {β : Type _} {f : β → A → β}
    (hcomm : ∀ b x y, f (f b x) y = f (f b y) x)
    {l₁ l₂ : List A} (h : l₁.Perm l₂) (init : β) :
    l₁.foldl f init = l₂.foldl f init := by
  induction h generalizing init with
  | nil => rfl
  | cons x _ ih => simp only [List.foldl_cons]; exact ih (f init x)
  | swap x y l =>
    simp only [List.foldl_cons]
    rw [hcomm]
  | trans _ _ ih₁ ih₂ =>
    rw [ih₁ init, ih₂ init]

private theorem foldl_cons_comm {β : Type _} {f : β → A → β}
    (hcomm : ∀ b x y, f (f b x) y = f (f b y) x)
    (l : List A) (init : β) (a : A) :
    l.foldl f (f init a) = f (l.foldl f init) a := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [←ih, hcomm]

theorem toList_insert_perm {a : A} {s : S} (h : a ∉ s) :
    (toList (insert a s)).Perm (a :: toList s) := by
  apply (List.perm_ext_iff_of_nodup toList_nodup _).mpr
  · intro x
    rw [mem_toList, mem_insert, List.mem_cons, mem_toList]
  · apply List.nodup_cons.mpr
    constructor
    · rw [mem_toList]; exact h
    · exact LawfulFiniteSet.toList_nodup

theorem toList_ofList {l : List A} (H : List.Nodup l) :
  List.Perm l (toList (ofList l : S)) := by
  apply (List.perm_ext_iff_of_nodup H toList_nodup).mpr
  intro x; rw [mem_toList, <-mem_ofList]

theorem toList_union_perm {s t : S} (hdisj : s ## t) :
    (toList (s ∪ t)).Perm (toList s ++ toList t) := by
  apply (List.perm_ext_iff_of_nodup toList_nodup _).mpr
  · intro x
    rw [mem_toList, mem_union, List.mem_append, mem_toList, mem_toList]
  · apply List.nodup_append.mpr
    constructor
    · exact toList_nodup
    · constructor
      · exact toList_nodup
      · intro a ha b hb heq
        subst heq
        rw [mem_toList] at ha hb
        exact hdisj a ⟨ha, hb⟩

theorem fold_insert {β : Type _} {f : β → A → β}
    (hcomm : ∀ b x y, f (f b x) y = f (f b y) x)
    {init : β} {a : A} {s : S} (h : a ∉ s) :
    fold f init (insert a s) = f (fold f init s) a := by
  simp only [fold]
  rw [foldl_perm hcomm (toList_insert_perm h)]
  simp only [List.foldl_cons]
  rw [foldl_cons_comm hcomm]

theorem fold_union {β : Type _} {f : β → A → β}
    (hcomm : ∀ b x y, f (f b x) y = f (f b y) x)
    {init : β} {s t : S} (hdisj : s ## t) :
    fold f init (s ∪ t) = fold f (fold f init s) t := by
  simp only [fold]
  rw [foldl_perm hcomm (toList_union_perm hdisj), List.foldl_append]

/-- Membership in a finite set is decidable when element equality is decidable. -/
instance [DecidableEq A] {x : A} {s : S} : Decidable (x ∈ s) := by
  rw [<-mem_toList]
  infer_instance

/-- Two sets are equal iff their list representations are equal. -/
theorem toList_eq_iff {s₁ s₂ : S} : (toList s₁ = toList s₂) = (s₁ = s₂) := by
  ext; apply Iff.intro
  · intro heq
    ext x; rw [<-mem_toList, <-mem_toList, heq]
  · rintro ⟨⟩
    rfl

/-- Equality of finite sets is decidable when element equality is decidable. -/
instance [DecidableEq A] : DecidableEq S := by
  intro X Y
  rw [<-toList_eq_iff]
  infer_instance

end FinLemmas

end FiniteSet
end Iris.Std
