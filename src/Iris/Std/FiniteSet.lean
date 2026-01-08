/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

/-! ## Abstract Finite Set Interface

This file defines an abstract interface for finite sets, inspired by stdpp's `fin_sets`.

### Notation

* `x ∈ S` - Membership
* `∅` - Empty set
* `{x}` - Singleton set
* `S₁ ∪ S₂` - Union
* `S₁ ∩ S₂` - Intersection
* `S ∖ {x}` - Difference (remove element)
* `S₁ ⊆ S₂` - Subset relation
* `S₁.Disjoint S₂` - Disjoint sets
-/

namespace Iris.Std

/-- Abstract finite set interface.
The type `S` represents a finite set of elements of type `A`.

This corresponds to Rocq's `FinSet` class from stdpp. -/
class FiniteSet (S : Type u) (A : outParam (Type v)) where
  /-- Membership: check if an element is in the set. -/
  mem : A → S → Bool
  /-- Insert an element into the set. -/
  insert : A → S → S
  /-- Remove an element from the set (singleton difference).
      Corresponds to Rocq's `X ∖ {[ x ]}`. -/
  erase : A → S → S
  /-- The empty set. -/
  empty : S
  /-- Convert the set to a list of elements.
      Corresponds to Rocq's `elements`. -/
  toList : S → List A
  /-- Construct a set from a list of elements.
      Corresponds to Rocq's `list_to_set`. -/
  ofList : List A → S
  /-- Union of two sets. -/
  union : S → S → S
  /-- Intersection of two sets. -/
  inter : S → S → S
  /-- Difference: remove all elements of second set from first.
      `diff S₁ S₂` contains elements in `S₁` but not in `S₂`.
      Corresponds to Rocq's `S₁ ∖ S₂`. -/
  diff : S → S → S

export FiniteSet (mem insert erase toList ofList union inter diff)

namespace FiniteSet

variable {S : Type u} {A : Type v} [FiniteSet S A]

/-- Empty set instance for `∅` notation. -/
instance : EmptyCollection S := ⟨empty⟩

/-- Singleton set containing exactly one element.
    Corresponds to Rocq's `{[ x ]}` notation. -/
def singleton (x : A) : S := insert x ∅

/-- Union instance for `∪` notation. -/
instance : Union S := ⟨union⟩

/-- Intersection instance for `∩` notation. -/
instance : Inter S := ⟨inter⟩

/-- Difference instance for `\` notation. -/
instance : SDiff S := ⟨diff⟩

/-- Subset relation: `S₁` is a subset of `S₂` if every element in `S₁` is also in `S₂`.
    Corresponds to Rocq's `S₁ ⊆ S₂`. -/
def Subset (S₁ S₂ : S) : Prop := ∀ x, mem x S₁ → mem x S₂

instance : HasSubset S := ⟨Subset⟩

/-- Two sets are disjoint if they share no common elements.
    Corresponds to Rocq's `S₁ ## S₂`. -/
def Disjoint (S₁ S₂ : S) : Prop := ∀ x, ¬(mem x S₁ ∧ mem x S₂)

/-- Filter: keep only elements satisfying a predicate.
    Corresponds to Rocq's `filter φ X`. -/
def filter (φ : A → Bool) : S → S :=
  fun s => ofList ((toList s).filter φ)

end FiniteSet

/-- Membership instance for finite sets: `x ∈ s` means element `x` is in set `s`. -/
instance {S : Type u} {A : Type v} [inst : FiniteSet S A] : Membership A S :=
  ⟨fun (s : S) (x : A) => inst.mem x s⟩

/-- Helper lemma: convert getElem? evidence to List.Mem -/
theorem List.mem_of_getElem? {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) : x ∈ l := by
  have ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp h
  exact List.mem_iff_getElem.mpr ⟨i, hi, hget⟩

/-- Helper lemma: convert List.Mem to getElem? existence -/
theorem List.getElem?_of_mem {α : Type _} {l : List α} {x : α} (h : x ∈ l) : ∃ i : Nat, l[i]? = some x := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩⟩

/-- Laws that a finite set implementation must satisfy. -/
class FiniteSetLaws (S : Type u) (A : Type v) [DecidableEq A] [FiniteSet S A] where
  /-- Membership in empty set is always false. -/
  mem_empty : ∀ (x : A), FiniteSet.mem x (∅ : S) = false
  /-- Membership in singleton: true iff equal. Corresponds to Rocq's `elem_of_singleton`. -/
  mem_singleton : ∀ (x y : A), FiniteSet.mem x (FiniteSet.singleton y : S) = true ↔ x = y
  /-- Membership after insert: true if equal, otherwise unchanged. -/
  mem_insert_eq : ∀ (s : S) (x y : A), x = y → FiniteSet.mem x (FiniteSet.insert y s) = true
  /-- Membership after insert: unchanged if not equal. -/
  mem_insert_ne : ∀ (s : S) (x y : A), x ≠ y →
    FiniteSet.mem x (FiniteSet.insert y s) = FiniteSet.mem x s
  /-- Singleton as insert into empty. -/
  singleton_insert : ∀ (x : A), (FiniteSet.singleton x : S) = FiniteSet.insert x ∅
  /-- Set extensionality: sets with same membership are equal. -/
  ext : ∀ (X Y : S), (∀ x, FiniteSet.mem x X = FiniteSet.mem x Y) → X = Y
  /-- Membership after erase: false if equal, otherwise unchanged. -/
  mem_erase_eq : ∀ (s : S) (x y : A), x = y → FiniteSet.mem x (FiniteSet.erase y s) = false
  /-- Membership after erase: unchanged if not equal. -/
  mem_erase_ne : ∀ (s : S) (x y : A), x ≠ y →
    FiniteSet.mem x (FiniteSet.erase y s) = FiniteSet.mem x s
  /-- Converting to list and back preserves the set (up to permutation). -/
  toList_ofList : ∀ (l : List A) (s : S), l.Nodup → FiniteSet.ofList l = s →
    (FiniteSet.toList s).Perm l
  /-- Converting list to set and back gives a permutation of the deduplicated list. -/
  ofList_toList : ∀ (s : S),
    ∃ l', (FiniteSet.toList s).Perm l' ∧ l'.Nodup ∧ FiniteSet.ofList l' = s
  /-- Inserting into a set gives a list permutation including the new element. -/
  set_to_list_insert : ∀ (s : S) (x : A), FiniteSet.mem x s = false →
    (FiniteSet.toList (FiniteSet.insert x s)).Perm (x :: FiniteSet.toList s)
  /-- Erasing from a set gives a list permutation without the element. -/
  set_to_list_erase : ∀ (s : S) (x : A), FiniteSet.mem x s = true →
    ∃ l', (FiniteSet.toList s).Perm (x :: l') ∧
          FiniteSet.toList (FiniteSet.erase x s) = l'
  /-- Converting empty list gives empty set. -/
  ofList_nil : FiniteSet.ofList ([] : List A) = (∅ : S)
  /-- toList of empty set is the empty list. -/
  toList_empty : FiniteSet.toList (∅ : S) = []
  /-- toList of singleton set is a singleton list (up to permutation). -/
  toList_singleton : ∀ (x : A), (FiniteSet.toList (FiniteSet.singleton x : S)).Perm [x]
  /-- toList of union when disjoint (up to permutation). -/
  toList_union : ∀ (X Y : S), FiniteSet.Disjoint X Y →
    ∃ l', (FiniteSet.toList (X ∪ Y)).Perm (FiniteSet.toList X ++ l') ∧
          (FiniteSet.toList Y).Perm l'
  /-- toList of set difference (up to permutation). -/
  toList_sdiff : ∀ (X : S) (x : A), FiniteSet.mem x X = true →
    ∃ l', (FiniteSet.toList X).Perm (x :: l') ∧
          (FiniteSet.toList (FiniteSet.diff X (FiniteSet.singleton x))).Perm l'
  /-- Membership is preserved by toList. -/
  mem_toList : ∀ (X : S) (x : A), x ∈ FiniteSet.toList X ↔ FiniteSet.mem x X = true
  /-- Membership in difference: y ∈ X \ {x} ↔ y ∈ X ∧ y ≠ x -/
  mem_diff_singleton : ∀ (X : S) (x y : A),
    FiniteSet.mem y (FiniteSet.diff X (FiniteSet.singleton x)) = true ↔
    (FiniteSet.mem y X = true ∧ y ≠ x)
  /-- Subset decomposition: If Y ⊆ X, then X = Y ∪ (X \ Y) up to the disjointness condition. -/
  union_diff : ∀ (X Y : S), Y ⊆ X →
    FiniteSet.Disjoint Y (FiniteSet.diff X Y) ∧
    (∀ z, FiniteSet.mem z X = true ↔ (FiniteSet.mem z Y = true ∨ FiniteSet.mem z (FiniteSet.diff X Y) = true))
  /-- Subset relation preserved by toList: if Y ⊆ X, toList Y elements appear in toList X. -/
  toList_subset : ∀ (X Y : S), Y ⊆ X →
    ∃ l, (FiniteSet.toList Y ++ l).Perm (FiniteSet.toList X)
  /-- Membership in union: x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y -/
  mem_union : ∀ (X Y : S) (x : A),
    FiniteSet.mem x (X ∪ Y) = true ↔ (FiniteSet.mem x X = true ∨ FiniteSet.mem x Y = true)
  /-- Union is commutative for toList (up to permutation). -/
  toList_union_comm : ∀ (X Y : S),
    (FiniteSet.toList (X ∪ Y)).Perm (FiniteSet.toList (Y ∪ X))
  /-- toList of filter is related to filter over toList. -/
  toList_filter : ∀ (X : S) (φ : A → Bool),
    (FiniteSet.toList (FiniteSet.filter φ X)).Perm ((FiniteSet.toList X).filter φ)
  /-- Membership in filter: x ∈ filter φ X ↔ x ∈ X ∧ φ x = true -/
  mem_filter : ∀ (X : S) (φ : A → Bool) (x : A),
    FiniteSet.mem x (FiniteSet.filter φ X) = true ↔ (FiniteSet.mem x X = true ∧ φ x = true)
  /-- Membership in ofList: x ∈ ofList l ↔ x ∈ l -/
  mem_ofList : ∀ (l : List A) (x : A),
    FiniteSet.mem x (FiniteSet.ofList l : S) = true ↔ x ∈ l

namespace FiniteSet

variable {S : Type u} {A : Type v} [DecidableEq A] [FiniteSet S A] [FiniteSetLaws S A]

/-- Size of a finite set: number of elements. Corresponds to Rocq's `size`. -/
def size (s : S) : Nat := (toList s).length

/-- The set is finite (always true for FiniteSet). Corresponds to Rocq's `set_finite`. -/
theorem set_finite (X : S) : ∃ (l : List A), ∀ x, x ∈ l ↔ mem x X = true := by
  exists toList X
  intro x
  exact FiniteSetLaws.mem_toList X x

section Elements

/-- toList is proper: equivalent sets have permutation-equivalent lists.
    Corresponds to Rocq's `elements_proper`. -/
theorem toList_proper (X Y : S) (h : ∀ x, mem x X = mem x Y) :
    (toList X).Perm (toList Y) := by
  have : X = Y := FiniteSetLaws.ext X Y h
  rw [this]

/-- Converting list to set and back gives the original set (up to permutation).
    Corresponds to Rocq's `list_to_set_elements`. -/
theorem ofList_toList_equiv (X : S) : ∀ x, mem x (ofList (toList X) : S) = mem x X := by
  intro x
  -- Use mem_ofList and mem_toList axioms
  cases h : mem x (ofList (toList X) : S) <;> cases h' : mem x X
  · rfl
  · -- Contradiction: mem x X = true but mem x (ofList (toList X)) = false
    have : x ∈ toList X := (FiniteSetLaws.mem_toList X x).mpr h'
    have : mem x (ofList (toList X) : S) = true := (FiniteSetLaws.mem_ofList (toList X) x).mpr this
    rw [h] at this
    cases this
  · -- Contradiction: mem x (ofList (toList X)) = true but mem x X = false
    have : x ∈ toList X := (FiniteSetLaws.mem_ofList (toList X) x).mp h
    have : mem x X = true := (FiniteSetLaws.mem_toList X x).mp this
    rw [h'] at this
    cases this
  · rfl

/-- Converting a NoDup list to set and back gives a permutation.
    Corresponds to Rocq's `elements_list_to_set`. -/
theorem toList_ofList_perm (l : List A) (h : l.Nodup) :
    (toList (ofList l : S)).Perm l := by
  -- Directly use the axiom toList_ofList
  exact FiniteSetLaws.toList_ofList l (ofList l : S) h rfl

/-- Union of singleton and set when element not in set.
    Corresponds to Rocq's `elements_union_singleton`. -/
theorem toList_union_singleton (X : S) (x : A) (h : mem x X = false) :
    (toList (union (singleton x) X)).Perm (x :: toList X) := by
  -- Use the fact that {x} and X are disjoint, then use toList_union
  have hdisj : Disjoint (singleton x) X := by
    intro y
    intro ⟨h1, h2⟩
    -- y ∈ {x} means y = x
    have : y = x := (FiniteSetLaws.mem_singleton y x).mp h1
    rw [this] at h2
    rw [h] at h2
    cases h2
  -- Get the permutation from toList_union
  obtain ⟨l', hperm, hperm'⟩ := FiniteSetLaws.toList_union (singleton x) X hdisj
  -- toList (singleton x) is a permutation of [x]
  have hsing := FiniteSetLaws.toList_singleton (A := A) (S := S) x
  -- Build up the permutation step by step
  have h1 : (toList (singleton x) ++ l').Perm ([x] ++ l') :=
    List.Perm.append hsing (List.Perm.refl l')
  have h2 : ([x] ++ l').Perm ([x] ++ toList X) :=
    List.Perm.append (List.Perm.refl [x]) hperm'.symm
  exact hperm.trans (h1.trans h2)

/-- Subset relation on toList. Corresponds to Rocq's `elements_submseteq`. -/
theorem toList_submseteq (X Y : S) (h : X ⊆ Y) :
    ∀ x, x ∈ toList X → x ∈ toList Y := by
  intro x hx
  rw [FiniteSetLaws.mem_toList] at hx ⊢
  exact h x hx

end Elements

section Size

/-- Empty set has size 0. Corresponds to Rocq's `size_empty`. -/
theorem size_empty : size (∅ : S) = 0 := by
  unfold size
  rw [FiniteSetLaws.toList_empty]
  rfl

/-- Size 0 iff empty set. Corresponds to Rocq's `size_empty_iff`. -/
theorem size_empty_iff (X : S) : size X = 0 ↔ ∀ x, mem x X = false := by
  constructor
  · -- Forward: size X = 0 → ∀ x, mem x X = false
    intro hsize x
    unfold size at hsize
    -- toList X has length 0, so it must be []
    have hnil : toList X = [] := List.eq_nil_of_length_eq_zero hsize
    -- If mem x X were true, then x ∈ toList X, but toList X = []
    cases hmem : mem x X
    · rfl
    · -- Case: mem x X = true, derive contradiction
      have : x ∈ toList X := (FiniteSetLaws.mem_toList X x).mpr hmem
      rw [hnil] at this
      cases this
  · -- Backward: (∀ x, mem x X = false) → size X = 0
    intro h
    -- Show X = ∅ by extensionality, then use size_empty
    have : X = ∅ := by
      apply FiniteSetLaws.ext (A := A)
      intro x
      rw [h x, FiniteSetLaws.mem_empty]
    rw [this, size_empty]

/-- Singleton set has size 1. Corresponds to Rocq's `size_singleton`. -/
theorem size_singleton (x : A) : size (singleton x : S) = 1 := by
  unfold size
  have h := FiniteSetLaws.toList_singleton (A := A) (S := S) x
  have : [x].length = 1 := rfl
  rw [← this, ← h.length_eq]

/-- Non-empty set has positive size. Corresponds to Rocq's `set_choose`. -/
theorem set_choose (X : S) (h : size X ≠ 0) : ∃ x, mem x X = true := by
  unfold size at h
  -- If toList X has non-zero length, it must be x :: l for some x, l
  cases hlist : toList X with
  | nil =>
    -- Contradiction: list is empty but h says length ≠ 0
    rw [hlist] at h
    simp at h
  | cons x l =>
    -- x is the first element, so x ∈ toList X
    exists x
    rw [← FiniteSetLaws.mem_toList]
    rw [hlist]
    exact List.mem_cons_self ..

/-- Union of disjoint sets has size equal to sum.
    Corresponds to Rocq's `size_union`. -/
theorem size_union (X Y : S) (h : Disjoint X Y) :
    size (X ∪ Y) = size X + size Y := by
  unfold size
  obtain ⟨l', hperm, hperm'⟩ := FiniteSetLaws.toList_union X Y h
  rw [hperm.length_eq, List.length_append, hperm'.length_eq]

/-- Subset implies smaller or equal size. Corresponds to Rocq's `subseteq_size`. -/
theorem subseteq_size (X Y : S) (h : X ⊆ Y) : size X ≤ size Y := by
  have ⟨hdisj, heq⟩ := FiniteSetLaws.union_diff Y X h
  -- Y = X ∪ (Y \ X) in terms of membership, and X and Y \ X are disjoint
  -- Convert membership equality to set equality
  have hset_eq : Y = X ∪ (Y \ X) := by
    apply FiniteSetLaws.ext (A := A)
    intro z
    -- heq z says: mem z Y = true ↔ (mem z X = true ∨ mem z (Y \ X) = true)
    -- Need to show: mem z Y = mem z (X ∪ Y \ X)
    -- The latter is: mem z X = true ∨ mem z (Y \ X) = true by mem_union
    cases hmem_y : mem z Y <;> cases hmem_union : mem z (X ∪ (Y \ X))
    · rfl
    · -- Contradiction: X ∪ (Y \ X) true but Y false
      have : mem z X = true ∨ mem z (Y \ X) = true :=
        (FiniteSetLaws.mem_union X (Y \ X) z).mp hmem_union
      have : mem z Y = true := (heq z).mpr this
      rw [hmem_y] at this
      cases this
    · -- Contradiction: Y true but X ∪ (Y \ X) false
      have : mem z X = true ∨ mem z (Y \ X) = true := (heq z).mp hmem_y
      have : mem z (X ∪ (Y \ X)) = true :=
        (FiniteSetLaws.mem_union X (Y \ X) z).mpr this
      rw [hmem_union] at this
      cases this
    · rfl
  -- Now use size_union with disjointness
  rw [hset_eq]
  have hsize := size_union X (Y \ X) hdisj
  omega

/-- Proper subset implies strictly smaller size. Corresponds to Rocq's `subset_size`. -/
theorem subset_size (X Y : S) (h : X ⊆ Y) (hne : ∃ x, mem x Y = true ∧ mem x X = false) :
    size X < size Y := by
  have ⟨x, hmemY, hmemX⟩ := hne
  -- Derive: size Y = size X + size (Y \ X) from union_diff
  have ⟨hdisj, heq⟩ := FiniteSetLaws.union_diff Y X h
  have hset_eq : Y = X ∪ (Y \ X) := by
    apply FiniteSetLaws.ext (A := A)
    intro z
    cases hmem_y : mem z Y <;> cases hmem_union : mem z (X ∪ (Y \ X))
    · rfl
    · have : mem z X = true ∨ mem z (Y \ X) = true :=
        (FiniteSetLaws.mem_union X (Y \ X) z).mp hmem_union
      have : mem z Y = true := (heq z).mpr this
      rw [hmem_y] at this; cases this
    · have : mem z X = true ∨ mem z (Y \ X) = true := (heq z).mp hmem_y
      have : mem z (X ∪ (Y \ X)) = true :=
        (FiniteSetLaws.mem_union X (Y \ X) z).mpr this
      rw [hmem_union] at this; cases this
    · rfl
  have hsize_union := size_union X (Y \ X) hdisj
  have hsize_y : size Y = size X + size (Y \ X) := by
    calc size Y
      _ = size (X ∪ (Y \ X)) := by rw [← hset_eq]
      _ = size X + size (Y \ X) := hsize_union
  -- Show size (Y \ X) ≠ 0 because x ∈ Y \ X
  have hdiff : size (Y \ X) ≠ 0 := by
    intro hcontra
    have : ∀ z, mem z (Y \ X) = false := (size_empty_iff (Y \ X)).mp hcontra
    -- But x ∈ Y \ X
    have hx_in_diff : mem x (Y \ X) = true := by
      -- heq x says: mem x Y = true ↔ (mem x X = true ∨ mem x (Y \ X) = true)
      -- We have mem x Y = true and mem x X = false
      -- So mem x (Y \ X) = true
      have : mem x X = true ∨ mem x (Y \ X) = true := (heq x).mp hmemY
      cases this with
      | inl h' =>
        -- Contradiction: mem x X = true but hmemX says mem x X = false
        rw [h'] at hmemX
        cases hmemX
      | inr h => exact h
    rw [this x] at hx_in_diff
    cases hx_in_diff
  omega

/-- Size of difference. Corresponds to Rocq's `size_difference`. -/
theorem size_difference (X Y : S) (h : Y ⊆ X) :
    size (X \ Y) = size X - size Y := by
  have ⟨hdisj, heq⟩ := FiniteSetLaws.union_diff X Y h
  -- X = Y ∪ (X \ Y) and they are disjoint
  have hset_eq : X = Y ∪ (X \ Y) := by
    apply FiniteSetLaws.ext (A := A)
    intro z
    cases hmem_x : mem z X <;> cases hmem_union : mem z (Y ∪ (X \ Y))
    · rfl
    · -- Contradiction: Y ∪ (X \ Y) true but X false
      have : mem z Y = true ∨ mem z (X \ Y) = true :=
        (FiniteSetLaws.mem_union Y (X \ Y) z).mp hmem_union
      have : mem z X = true := (heq z).mpr this
      rw [hmem_x] at this
      cases this
    · -- Contradiction: X true but Y ∪ (X \ Y) false
      have : mem z Y = true ∨ mem z (X \ Y) = true := (heq z).mp hmem_x
      have : mem z (Y ∪ (X \ Y)) = true :=
        (FiniteSetLaws.mem_union Y (X \ Y) z).mpr this
      rw [hmem_union] at this
      cases this
    · rfl
  -- Use size_union
  have hsize_union := size_union Y (X \ Y) hdisj
  have : size X = size Y + size (X \ Y) := by
    calc size X
      _ = size (Y ∪ (X \ Y)) := by rw [← hset_eq]
      _ = size Y + size (X \ Y) := hsize_union
  omega

end Size

section Filter

/-- Membership in filter. Corresponds to Rocq's `elem_of_filter`. -/
theorem mem_filter' (P : A → Bool) (X : S) (x : A) :
    mem x (filter P X) = true ↔ P x = true ∧ mem x X = true := by
  have h := FiniteSetLaws.mem_filter X P x
  constructor
  · intro hf
    have ⟨h1, h2⟩ := h.mp hf
    exact ⟨h2, h1⟩
  · intro ⟨hp, hm⟩
    exact h.mpr ⟨hm, hp⟩

/-- Filter of empty set is empty. Corresponds to Rocq's `filter_empty`. -/
theorem filter_empty (P : A → Bool) : filter P (∅ : S) = ∅ := by
  apply FiniteSetLaws.ext (A := A)
  intro x
  -- Show mem x (filter P ∅) = mem x ∅ = false
  have hempty : mem x (∅ : S) = false := FiniteSetLaws.mem_empty (A := A) x
  rw [hempty]
  -- Now show mem x (filter P ∅) = false
  cases h : mem x (filter P (∅ : S))
  · rfl
  · -- Contradiction: if mem x (filter P ∅) = true, then mem x ∅ = true
    have : mem x (∅ : S) = true := (FiniteSetLaws.mem_filter (∅ : S) P x |>.mp h).1
    rw [FiniteSetLaws.mem_empty (A := A)] at this
    cases this

/-- Filter of singleton. Corresponds to Rocq's `filter_singleton`. -/
theorem filter_singleton (P : A → Bool) (x : A) :
    filter P (singleton x : S) = if P x then singleton x else ∅ := by
  apply FiniteSetLaws.ext (A := A)
  intro y
  -- Split on whether P x is true or false
  cases hpx : P x
  · -- Case: P x = false, so filter P {x} = ∅
    -- Show mem y (filter P (singleton x)) = mem y ∅ = false
    simp [hpx]
    have hempty : mem y (∅ : S) = false := FiniteSetLaws.mem_empty (A := A) y
    rw [hempty]
    cases hmem : mem y (filter P (singleton x : S))
    · rfl
    · -- Contradiction: mem y (filter P {x}) = true implies P x = true
      have ⟨hmem_sing, hpy⟩ := (FiniteSetLaws.mem_filter (singleton x : S) P y).mp hmem
      -- Also y ∈ {x}, so y = x
      have : y = x := (FiniteSetLaws.mem_singleton y x).mp hmem_sing
      rw [this] at hpy
      rw [hpx] at hpy
      cases hpy
  · -- Case: P x = true, so filter P {x} = {x}
    -- Show mem y (filter P (singleton x)) = mem y (singleton x)
    simp [hpx]
    cases hmem_filt : mem y (filter P (singleton x : S)) <;>
    cases hmem_sing : mem y (singleton x : S)
    · rfl
    · -- mem y {x} = true but mem y (filter P {x}) = false - contradiction
      -- Since y ∈ {x}, we have y = x, and P x = true, so y ∈ filter P {x}
      have : y = x := (FiniteSetLaws.mem_singleton y x).mp hmem_sing
      have : mem y (singleton x : S) = true ∧ P y = true := by
        constructor
        · exact hmem_sing
        · rw [this, hpx]
      have : mem y (filter P (singleton x : S)) = true :=
        (FiniteSetLaws.mem_filter (singleton x : S) P y).mpr this
      rw [hmem_filt] at this
      cases this
    · -- mem y (filter P {x}) = true but mem y {x} = false - contradiction
      have ⟨hmem, _⟩ := (FiniteSetLaws.mem_filter (singleton x : S) P y).mp hmem_filt
      rw [hmem_sing] at hmem
      cases hmem
    · rfl

/-- Filter distributes over union. Corresponds to Rocq's `filter_union`. -/
theorem filter_union (P : A → Bool) (X Y : S) :
    filter P (X ∪ Y) = filter P X ∪ filter P Y := by
  apply FiniteSetLaws.ext (A := A)
  intro x
  -- Show: mem x (filter P (X ∪ Y)) = mem x (filter P X ∪ filter P Y)
  -- LHS: x ∈ filter P (X ∪ Y) ↔ x ∈ X ∪ Y ∧ P x
  -- RHS: x ∈ filter P X ∪ filter P Y ↔ (x ∈ X ∧ P x) ∨ (x ∈ Y ∧ P x)
  --                                   ↔ (x ∈ X ∨ x ∈ Y) ∧ P x
  --                                   ↔ x ∈ X ∪ Y ∧ P x
  cases h_filt_union : mem x (filter P (X ∪ Y)) <;>
  cases h_union_filt : mem x (filter P X ∪ filter P Y)
  · rfl
  · -- Contradiction: RHS is true but LHS is false
    -- x ∈ filter P X ∪ filter P Y means (x ∈ filter P X) ∨ (x ∈ filter P Y)
    have : mem x (filter P X) = true ∨ mem x (filter P Y) = true :=
      (FiniteSetLaws.mem_union (filter P X) (filter P Y) x).mp h_union_filt
    cases this with
    | inl h =>
      -- x ∈ filter P X, so x ∈ X and P x, so x ∈ X ∪ Y and P x, so x ∈ filter P (X ∪ Y)
      have ⟨hmem_x, hpx⟩ := (FiniteSetLaws.mem_filter X P x).mp h
      have : mem x (X ∪ Y) = true := (FiniteSetLaws.mem_union X Y x).mpr (Or.inl hmem_x)
      have : mem x (filter P (X ∪ Y)) = true :=
        (FiniteSetLaws.mem_filter (X ∪ Y) P x).mpr ⟨this, hpx⟩
      rw [h_filt_union] at this
      cases this
    | inr h =>
      -- x ∈ filter P Y, so x ∈ Y and P x, so x ∈ X ∪ Y and P x, so x ∈ filter P (X ∪ Y)
      have ⟨hmem_y, hpx⟩ := (FiniteSetLaws.mem_filter Y P x).mp h
      have : mem x (X ∪ Y) = true := (FiniteSetLaws.mem_union X Y x).mpr (Or.inr hmem_y)
      have : mem x (filter P (X ∪ Y)) = true :=
        (FiniteSetLaws.mem_filter (X ∪ Y) P x).mpr ⟨this, hpx⟩
      rw [h_filt_union] at this
      cases this
  · -- Contradiction: LHS is true but RHS is false
    -- x ∈ filter P (X ∪ Y), so x ∈ X ∪ Y and P x
    have ⟨hmem_union, hpx⟩ := (FiniteSetLaws.mem_filter (X ∪ Y) P x).mp h_filt_union
    -- x ∈ X ∪ Y means x ∈ X or x ∈ Y
    have : mem x X = true ∨ mem x Y = true :=
      (FiniteSetLaws.mem_union X Y x).mp hmem_union
    cases this with
    | inl hmem_x =>
      -- x ∈ X and P x, so x ∈ filter P X, so x ∈ filter P X ∪ filter P Y
      have : mem x (filter P X) = true :=
        (FiniteSetLaws.mem_filter X P x).mpr ⟨hmem_x, hpx⟩
      have : mem x (filter P X ∪ filter P Y) = true :=
        (FiniteSetLaws.mem_union (filter P X) (filter P Y) x).mpr (Or.inl this)
      rw [h_union_filt] at this
      cases this
    | inr hmem_y =>
      -- x ∈ Y and P x, so x ∈ filter P Y, so x ∈ filter P X ∪ filter P Y
      have : mem x (filter P Y) = true :=
        (FiniteSetLaws.mem_filter Y P x).mpr ⟨hmem_y, hpx⟩
      have : mem x (filter P X ∪ filter P Y) = true :=
        (FiniteSetLaws.mem_union (filter P X) (filter P Y) x).mpr (Or.inr this)
      rw [h_union_filt] at this
      cases this
  · rfl

/-- Disjointness of filter and complement. Corresponds to Rocq's `disjoint_filter_complement`. -/
theorem disjoint_filter_complement (P : A → Bool) (X : S) :
    Disjoint (filter P X) (filter (fun x => !P x) X) := by
  intro x
  intro ⟨h1, h2⟩
  -- h1: mem x (filter P X) = true means P x = true
  -- h2: mem x (filter (!P) X) = true means !P x = true, i.e., P x = false
  have ⟨_, hpx_true⟩ := (FiniteSetLaws.mem_filter X P x).mp h1
  have ⟨_, hpx_false⟩ := (FiniteSetLaws.mem_filter X (fun y => !P y) x).mp h2
  -- hpx_false says !P x = true, which means P x = false
  -- But hpx_true says P x = true - contradiction
  cases hpx : P x
  · -- P x = false, but hpx_true says P x = true
    rw [hpx] at hpx_true
    cases hpx_true
  · -- P x = true, so !P x = false, but hpx_false says !P x = true
    simp [hpx] at hpx_false

end Filter

section SetInduction

/-- Well-founded relation on finite sets based on proper subset.
    Corresponds to Rocq's `set_wf`. -/
theorem set_wf : WellFounded (fun (X Y : S) => X ⊆ Y ∧ ∃ x, mem x Y = true ∧ mem x X = false) := by
  -- Well-founded because size decreases for proper subsets
  have h_sub : ∀ X Y, (X ⊆ Y ∧ ∃ x, mem x Y = true ∧ mem x X = false) → size (S := S) (A := A) X < size (S := S) (A := A) Y := by
    intro X Y ⟨hsub, x, hmemY, hmemX⟩
    exact subset_size X Y hsub ⟨x, hmemY, hmemX⟩
  apply Subrelation.wf
  · intro X Y hrel
    exact h_sub X Y hrel
  · exact (measure (size (S := S) (A := A))).wf

/-- Induction principle for finite sets.
    Corresponds to Rocq's `set_ind`. -/
theorem set_ind {P : S → Prop}
    (hemp : P ∅)
    (hadd : ∀ x X, mem x X = false → P X → P (union (singleton x) X))
    (X : S) : P X := by
  -- Use well-founded induction based on set_wf
  apply WellFounded.induction set_wf X
  intro Y IH
  by_cases hempty : size Y = 0
  · have hY_empty : ∀ x, mem x Y = false := (size_empty_iff Y).mp hempty
    have : Y = ∅ := FiniteSetLaws.ext (S := S) (A := A) Y ∅ (fun x => by rw [hY_empty x, FiniteSetLaws.mem_empty])
    subst this
    exact hemp
  · obtain ⟨x, hmem⟩ := set_choose Y hempty
    let Y' := diff Y (singleton x)
    have hnotin : mem x Y' = false := by
      cases h : mem x Y'
      · rfl
      · have ⟨_, hne⟩ := (FiniteSetLaws.mem_diff_singleton Y x x).mp h
        cases hne rfl
    have hPY' : P Y' := by
      apply IH
      exact ⟨fun z hz => (FiniteSetLaws.mem_diff_singleton Y x z).mp hz |>.1, x, hmem, hnotin⟩
    -- Show Y = {x} ∪ Y'
    have heq : Y = union (singleton x) Y' := by
      apply FiniteSetLaws.ext (A := A)
      intro z
      cases hmemz : mem z Y <;> cases hmemu : mem z (union (singleton x) Y')
      · rfl
      · have : mem z (singleton x) = true ∨ mem z Y' = true :=
          (FiniteSetLaws.mem_union (singleton x) Y' z).mp hmemu
        cases this with
        | inl h => have : z = x := (FiniteSetLaws.mem_singleton (S := S) (A := A) z x).mp h; rw [this, hmem] at hmemz; cases hmemz
        | inr h => have ⟨hmemY, _⟩ := (FiniteSetLaws.mem_diff_singleton Y x z).mp h; rw [hmemz] at hmemY; cases hmemY
      · have : mem z (singleton x : S) = true ∨ mem z Y' = true := by
          by_cases hzx : z = x
          · left; exact (FiniteSetLaws.mem_singleton (S := S) (A := A) z x).mpr hzx
          · right; exact (FiniteSetLaws.mem_diff_singleton Y x z).mpr ⟨hmemz, hzx⟩
        have : mem z (union (singleton x) Y') = true := (FiniteSetLaws.mem_union (singleton x) Y' z).mpr this
        rw [hmemu] at this; cases this
      · rfl
    have : P (union (singleton x) Y') := hadd x Y' hnotin hPY'
    rw [heq]
    exact this

end SetInduction

section Map

/-- Map operation on sets. Maps a function over all elements.
    Corresponds to Rocq's `set_map`. -/
def map {B : Type w} [DecidableEq B] [FiniteSet S A] [FiniteSet T B]
    (f : A → B) (X : S) : T :=
  ofList ((toList X).map f)

/-- Membership in mapped set. Corresponds to Rocq's `elem_of_map`. -/
theorem mem_map {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → B) (X : S) (y : B) :
    mem y (map f X : T) = true ↔ ∃ x, y = f x ∧ mem x X = true := by
  unfold map
  rw [FiniteSetLaws.mem_ofList]
  constructor
  · intro h
    have ⟨x, hmem, hx⟩ := List.mem_map.mp h
    exact ⟨x, hx.symm, (FiniteSetLaws.mem_toList X x).mp hmem⟩
  · intro ⟨x, hf, hmem⟩
    have : y ∈ List.map f (toList X) := by
      rw [List.mem_map]
      exact ⟨x, (FiniteSetLaws.mem_toList X x).mpr hmem, hf.symm⟩
    exact this

/-- Map of empty set. Corresponds to Rocq's `set_map_empty`. -/
theorem map_empty {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → B) :
    map f (∅ : S) = (∅ : T) := by
  unfold map
  rw [FiniteSetLaws.toList_empty, List.map_nil, FiniteSetLaws.ofList_nil]

/-- Map distributes over union. Corresponds to Rocq's `set_map_union`. -/
theorem map_union {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → B) (X Y : S) :
    map f (X ∪ Y : S) = (map f X ∪ map f Y : T) := by
  apply FiniteSetLaws.ext (A := B)
  intro z
  cases hmem1 : mem z (map f (X ∪ Y : S) : T) <;>
  cases hmem2 : mem z ((map f X ∪ map f Y : T))
  · rfl
  · -- Contradiction
    have := (FiniteSetLaws.mem_union (map f X : T) (map f Y : T) z).mp hmem2
    cases this with
    | inl h =>
      have ⟨x, hfx, hx⟩ := mem_map f X z |>.mp h
      have : mem z (map f (X ∪ Y : S) : T) = true := mem_map f (X ∪ Y : S) z |>.mpr
        ⟨x, hfx, (FiniteSetLaws.mem_union X Y x).mpr (Or.inl hx)⟩
      rw [hmem1] at this
      cases this
    | inr h =>
      have ⟨x, hfx, hx⟩ := mem_map f Y z |>.mp h
      have : mem z (map f (X ∪ Y : S) : T) = true := mem_map f (X ∪ Y : S) z |>.mpr
        ⟨x, hfx, (FiniteSetLaws.mem_union X Y x).mpr (Or.inr hx)⟩
      rw [hmem1] at this
      cases this
  · -- Contradiction
    have ⟨x, hfx, hx⟩ := mem_map f (X ∪ Y : S) z |>.mp hmem1
    have := (FiniteSetLaws.mem_union X Y x).mp hx
    cases this with
    | inl h =>
      have : mem z (map f X ∪ map f Y : T) = true :=
        (FiniteSetLaws.mem_union (map f X : T) (map f Y : T) z).mpr
          (Or.inl (mem_map f X z |>.mpr ⟨x, hfx, h⟩))
      rw [hmem2] at this
      cases this
    | inr h =>
      have : mem z (map f X ∪ map f Y : T) = true :=
        (FiniteSetLaws.mem_union (map f X : T) (map f Y : T) z).mpr
          (Or.inr (mem_map f Y z |>.mpr ⟨x, hfx, h⟩))
      rw [hmem2] at this
      cases this
  · rfl

/-- Map of singleton. Corresponds to Rocq's `set_map_singleton`. -/
theorem map_singleton {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → B) (x : A) :
    ∀ y, mem y (map f (singleton x : S) : T) = mem y (singleton (f x) : T) := by
  intro y
  cases h1 : mem y (map f (singleton x : S) : T) <;>
  cases h2 : mem y (singleton (f x) : T)
  · rfl
  · -- Contradiction
    have : y = f x := (FiniteSetLaws.mem_singleton y (f x)).mp h2
    rw [this] at h1
    have : mem (f x) (map f (singleton x : S) : T) = true :=
      mem_map f (singleton x : S) (f x) |>.mpr
        ⟨x, rfl, (FiniteSetLaws.mem_singleton x x).mpr rfl⟩
    rw [h1] at this
    cases this
  · -- Contradiction
    have ⟨z, hfz, hz⟩ := mem_map f (singleton x : S) y |>.mp h1
    have : z = x := (FiniteSetLaws.mem_singleton z x).mp hz
    rw [this] at hfz
    have : mem y (singleton (f x) : T) = true :=
      (FiniteSetLaws.mem_singleton y (f x)).mpr hfz
    rw [h2] at this
    cases this
  · rfl

end Map

section Bind

/-- Bind operation on sets. Flatmap a function over all elements.
    Corresponds to Rocq's `set_bind`. -/
def bind {T : Type u} [FiniteSet T A] (f : A → T) (X : S) : T :=
  ofList ((toList X).flatMap (fun x => toList (f x)))

/-- Membership in bind. Corresponds to Rocq's `elem_of_set_bind`. -/
theorem mem_bind {T : Type u} [FiniteSet T A] [FiniteSetLaws T A]
    (f : A → T) (X : S) (y : A) :
    mem y (bind f X) = true ↔ ∃ x, mem x X = true ∧ mem y (f x) = true := by
  unfold bind
  rw [FiniteSetLaws.mem_ofList]
  rw [List.mem_flatMap]
  constructor
  · intro ⟨x, hx_in, hy_in⟩
    exact ⟨x, (FiniteSetLaws.mem_toList X x).mp hx_in, (FiniteSetLaws.mem_toList (f x) y).mp hy_in⟩
  · intro ⟨x, hx, hy⟩
    exact ⟨x, (FiniteSetLaws.mem_toList X x).mpr hx, (FiniteSetLaws.mem_toList (f x) y).mpr hy⟩

/-- Bind of singleton. Corresponds to Rocq's `set_bind_singleton`. -/
theorem bind_singleton {T : Type u} [FiniteSet T A] [FiniteSetLaws T A]
    (f : A → T) (x : A) :
    ∀ y, mem y (bind (S := S) f (singleton x)) = mem y (f x) := by
  intro y
  cases h1 : mem y (bind (S := S) f (singleton x)) <;>
  cases h2 : mem y (f x)
  · rfl
  · -- Contradiction
    have : mem y (bind (S := S) f (singleton x)) = true :=
      mem_bind f (singleton x) y |>.mpr
        ⟨x, (FiniteSetLaws.mem_singleton x x).mpr rfl, h2⟩
    rw [h1] at this
    cases this
  · -- Contradiction
    have ⟨z, hz, hmem⟩ := mem_bind f (singleton x) y |>.mp h1
    have : z = x := (FiniteSetLaws.mem_singleton z x).mp hz
    rw [this] at hmem
    rw [h2] at hmem
    cases hmem
  · rfl

end Bind

section Omap

/-- Option map operation on sets. Maps a partial function, keeping only Some values.
    Corresponds to Rocq's `set_omap`. -/
def omap {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B]
    (f : A → Option B) (X : S) : T :=
  ofList ((toList X).filterMap f)

/-- Membership in omap. Corresponds to Rocq's `elem_of_set_omap`. -/
theorem mem_omap {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → Option B) (X : S) (y : B) :
    mem y (omap f X : T) = true ↔ ∃ x, mem x X = true ∧ f x = some y := by
  unfold omap
  rw [FiniteSetLaws.mem_ofList]
  rw [List.mem_filterMap]
  constructor
  · intro ⟨x, hx_in, hfx⟩
    exact ⟨x, (FiniteSetLaws.mem_toList X x).mp hx_in, hfx⟩
  · intro ⟨x, hx, hfx⟩
    exact ⟨x, (FiniteSetLaws.mem_toList X x).mpr hx, hfx⟩

/-- Omap of empty set. Corresponds to Rocq's `set_omap_empty`. -/
theorem omap_empty {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → Option B) :
    omap f (∅ : S) = (∅ : T) := by
  unfold omap
  rw [FiniteSetLaws.toList_empty, List.filterMap_nil, FiniteSetLaws.ofList_nil]

/-- Omap distributes over union. Corresponds to Rocq's `set_omap_union`. -/
theorem omap_union {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → Option B) (X Y : S) :
    ∀ z, mem z (omap f (X ∪ Y : S) : T) = mem z ((omap f X : T) ∪ (omap f Y : T)) := by
  intro z
  cases h1 : mem z (omap f (X ∪ Y : S) : T) <;>
  cases h2 : mem z ((omap f X : T) ∪ (omap f Y : T))
  · rfl
  · -- Contradiction
    have := (FiniteSetLaws.mem_union (omap f X : T) (omap f Y : T) z).mp h2
    cases this with
    | inl h =>
      have ⟨x, hx, hfx⟩ := mem_omap f X z |>.mp h
      have : mem z (omap f (X ∪ Y : S) : T) = true :=
        mem_omap f (X ∪ Y : S) z |>.mpr
          ⟨x, (FiniteSetLaws.mem_union X Y x).mpr (Or.inl hx), hfx⟩
      rw [h1] at this
      cases this
    | inr h =>
      have ⟨x, hx, hfx⟩ := mem_omap f Y z |>.mp h
      have : mem z (omap f (X ∪ Y : S) : T) = true :=
        mem_omap f (X ∪ Y : S) z |>.mpr
          ⟨x, (FiniteSetLaws.mem_union X Y x).mpr (Or.inr hx), hfx⟩
      rw [h1] at this
      cases this
  · -- Contradiction
    have ⟨x, hx, hfx⟩ := mem_omap f (X ∪ Y : S) z |>.mp h1
    have := (FiniteSetLaws.mem_union X Y x).mp hx
    cases this with
    | inl h =>
      have : mem z ((omap f X : T) ∪ (omap f Y : T)) = true :=
        (FiniteSetLaws.mem_union (omap f X : T) (omap f Y : T) z).mpr
          (Or.inl (mem_omap f X z |>.mpr ⟨x, h, hfx⟩))
      rw [h2] at this
      cases this
    | inr h =>
      have : mem z ((omap f X : T) ∪ (omap f Y : T)) = true :=
        (FiniteSetLaws.mem_union (omap f X : T) (omap f Y : T) z).mpr
          (Or.inr (mem_omap f Y z |>.mpr ⟨x, h, hfx⟩))
      rw [h2] at this
      cases this
  · rfl

/-- Omap of singleton when function returns Some. -/
theorem omap_singleton_some {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → Option B) (x : A) (y : B) (h : f x = some y) :
    ∀ z, mem z (omap f (singleton x : S) : T) = mem z (singleton y : T) := by
  intro z
  cases h1 : mem z (omap f (singleton x : S) : T) <;>
  cases h2 : mem z (singleton y : T)
  · rfl
  · -- Contradiction
    have : z = y := (FiniteSetLaws.mem_singleton z y).mp h2
    rw [this] at h1
    have : mem y (omap f (singleton x : S) : T) = true :=
      mem_omap f (singleton x : S) y |>.mpr
        ⟨x, (FiniteSetLaws.mem_singleton x x).mpr rfl, h⟩
    rw [h1] at this
    cases this
  · -- Contradiction: mem z (omap f {x}) = true but f x = some y and mem z {y} = false
    have ⟨w, hw, hfw⟩ := mem_omap f (singleton x : S) z |>.mp h1
    have wx : w = x := (FiniteSetLaws.mem_singleton w x).mp hw
    rw [wx] at hfw
    -- hfw : f x = some z, but we know f x = some y
    rw [h] at hfw
    -- Now hfw : some y = some z, so y = z
    cases hfw
    -- But now we have mem y (singleton y) = false, contradiction
    have : mem y (singleton y : T) = true := (FiniteSetLaws.mem_singleton y y).mpr rfl
    rw [h2] at this
    cases this
  · rfl

/-- Omap of singleton when function returns None. -/
theorem omap_singleton_none {B : Type w} {T : Type u} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (f : A → Option B) (x : A) (h : f x = none) :
    omap f (singleton x : S) = (∅ : T) := by
  apply FiniteSetLaws.ext (A := B)
  intro z
  cases h1 : mem z (omap f (singleton x : S) : T) <;>
  cases h2 : mem z (∅ : T)
  · rfl
  · -- Contradiction: mem z ∅ = true
    rw [FiniteSetLaws.mem_empty] at h2
    cases h2
  · -- Contradiction: mem z (omap f {x}) = true but f x = none
    have ⟨w, hw, hfw⟩ := mem_omap f (singleton x : S) z |>.mp h1
    have : w = x := (FiniteSetLaws.mem_singleton w x).mp hw
    rw [this] at hfw
    rw [h] at hfw
    cases hfw
  · rfl

end Omap

section DecisionProcedures

/-- Forall predicate on sets. Corresponds to Rocq's `set_Forall`. -/
def setForall (P : A → Prop) (X : S) : Prop :=
  ∀ x, mem x X = true → P x

/-- Exists predicate on sets. Corresponds to Rocq's `set_Exists`. -/
def setExists (P : A → Prop) (X : S) : Prop :=
  ∃ x, mem x X = true ∧ P x

end DecisionProcedures

end FiniteSet

end Iris.Std
