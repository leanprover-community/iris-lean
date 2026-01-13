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
class FiniteSet (A : outParam (Type v)) (S : Type u) where
  /-- The empty set. -/
  empty : S
  /-- Convert the set to a list of elements.
      Corresponds to Rocq's `elements`. -/
  toList : S → List A
  /-- Construct a set from a list of elements.
      Corresponds to Rocq's `list_to_set`. -/
  ofList : List A → S

export FiniteSet (empty toList ofList)

namespace FiniteSet

variable {A : Type v} {S : Type u} [DecidableEq A] [FiniteSet A S]

/-- Membership: check if an element is in the set. -/
def mem : A → S → Bool := fun x s => (toList s).contains x
/-- Insert an element into the set. -/
def insert : A → S → S := fun x s => ofList (x :: toList s)
/-- Remove an element from the set (singleton difference).
      Corresponds to Rocq's `X ∖ {[ x ]}`. -/
def erase : A → S → S := fun x s => ofList ((toList s).filter (fun y => decide (y ≠ x)))
/-- Union of two sets. -/
def union : S → S → S := fun s₁ s₂ => ofList (toList s₁ ++ toList s₂)
/-- Intersection of two sets. -/
def inter : S → S → S := fun s₁ s₂ => ofList ((toList s₁).filter (fun x => mem x s₂))
/-- Difference: remove all elements of second set from first.
      `diff S₁ S₂` contains elements in `S₁` but not in `S₂`.
      Corresponds to Rocq's `S₁ ∖ S₂`. -/
def diff : S → S → S := fun s₁ s₂ => ofList ((toList s₁).filter (fun x => !mem x s₂))

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

/-- Membership instance for finite sets: `x ∈ s` means element `x` is in set `s`. -/
instance : Membership A S where
  mem s x := FiniteSet.mem (A := A) x s = true

/-- Subset relation: `S₁` is a subset of `S₂` if every element in `S₁` is also in `S₂`.
    Corresponds to Rocq's `S₁ ⊆ S₂`. -/
def Subset (S₁ S₂ : S) : Prop := ∀ x, x ∈ S₁ → x ∈ S₂

instance : HasSubset S := ⟨Subset⟩

/-- Two sets are disjoint if they share no common elements.
    Corresponds to Rocq's `S₁ ## S₂`. -/
def Disjoint (S₁ S₂ : S) : Prop := ∀ x, ¬(x ∈ S₁ ∧ x ∈ S₂)

/-- Set equivalence: two sets are equivalent if they have the same elements.
    Corresponds to Rocq's `X ≡ Y`. -/
def SetEquiv (X Y : S) : Prop := ∀ x, x ∈ X ↔ x ∈ Y

/-- Notation for set equivalence -/
infix:50 " ≡ " => SetEquiv

/-- Set equivalence is reflexive -/
theorem setEquiv_refl : ∀ (X : S), X ≡ X := by
  intro X x
  rfl

/-- Set equivalence is symmetric -/
theorem setEquiv_symm : ∀ (X Y : S), X ≡ Y → Y ≡ X := by
  intro X Y h x
  exact (h x).symm

/-- Set equivalence is transitive -/
theorem setEquiv_trans : ∀ (X Y Z : S), X ≡ Y → Y ≡ Z → X ≡ Z := by
  intro X Y Z hxy hyz x
  exact Iff.trans (hxy x) (hyz x)

/-- Set equivalence is an equivalence relation -/
instance : Equivalence (@SetEquiv A S _ _) where
  refl := setEquiv_refl
  symm := fun {X Y} hxy => setEquiv_symm X Y hxy
  trans := fun {X Y Z} hxy hyz => setEquiv_trans X Y Z hxy hyz

/-- Corresponds to Rocq's `filter φ X`. -/
def filter (φ : A → Bool) : S → S :=
  fun s => ofList ((toList s).filter φ)

/-- Corresponds to Rocq's `set_bind`. -/
def bind  {B : Type w} {S' : Type u} [FiniteSet B S'] (f : A → S') (X : S) : S' :=
  ofList ((toList X).flatMap (fun x => toList (f x)))

/-- Corresponds to Rocq's `set_omap`. -/
def omap {B : Type w} {S' : Type u} [DecidableEq B] [FiniteSet B S']
    (f : A → Option B) (X : S) : S' :=
  ofList ((toList X).filterMap f)

/-- Corresponds to Rocq's `set_Forall`. -/
def setForall (P : A → Prop) (X : S) : Prop :=
  ∀ x, x ∈ X → P x

/-- Corresponds to Rocq's `set_Exists`. -/
def setExists (P : A → Prop) (X : S) : Prop :=
  ∃ x, x ∈ X ∧ P x

/-- Corresponds to Rocq's `size`. -/
def size (s : S) : Nat := (toList s).length

end FiniteSet

/-- Helper: x ∈ s is definitionally equal to mem x s = true -/
@[simp] theorem mem_iff_mem {A : Type v} {S : Type u} [DecidableEq A] [FiniteSet A S] (x : A) (s : S) :
    x ∈ s ↔ FiniteSet.mem x s = true := Iff.rfl

/-- Helper lemma: convert getElem? evidence to List.Mem -/
theorem List.mem_of_getElem? {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) : x ∈ l := by
  have ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp h
  exact List.mem_iff_getElem.mpr ⟨i, hi, hget⟩

/-- Helper lemma: convert List.Mem to getElem? existence -/
theorem List.getElem?_of_mem {α : Type _} {l : List α} {x : α} (h : x ∈ l) : ∃ i : Nat, l[i]? = some x := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩⟩

/-- Laws that a finite set implementation must satisfy. -/
class FiniteSetLaws (A : Type v) (S : Type u) [DecidableEq A] [FiniteSet A S] where
  /-- Membership in empty set is always false. -/
  mem_empty : ∀ (x : A), x ∉ (∅ : S)
  /-- Converting to list and back preserves the set (up to permutation). -/
  toList_ofList : ∀ (l : List A) (s : S), l.Nodup → FiniteSet.ofList l = s →
    (FiniteSet.toList s).Perm l
  /-- Corresponds to Rocq's `NoDup_elements`. -/
  toList_nodup (X : S) : (toList X).Nodup
  /-- Inserting into a set gives a list permutation including the new element. -/
  set_to_list_insert : ∀ (s : S) (x : A), x ∉ s →
    (FiniteSet.toList (FiniteSet.insert x s)).Perm (x :: FiniteSet.toList s)
  /-- Erasing from a set gives a list permutation without the element. -/
  set_to_list_erase : ∀ (s : S) (x : A), x ∈ s →
    ∃ l', (FiniteSet.toList s).Perm (x :: l') ∧
          FiniteSet.toList (FiniteSet.erase x s) = l'
  /-- Converting empty list gives empty set. -/
  ofList_nil : FiniteSet.ofList ([] : List A) = (∅ : S)
  /-- toList of empty set is the empty list. -/
  toList_empty : FiniteSet.toList (∅ : S) = []
  /-- Membership is preserved by toList. -/
  mem_toList : ∀ (X : S) (x : A), x ∈ FiniteSet.toList X ↔ x ∈ X
  /-- toList of filter is related to filter over toList. -/
  toList_filter : ∀ (X : S) (φ : A → Bool),
    (FiniteSet.toList (FiniteSet.filter φ X)).Perm ((FiniteSet.toList X).filter φ)
  /-- Membership in ofList: x ∈ ofList l ↔ x ∈ l -/
  mem_ofList : ∀ (l : List A) (x : A),
    x ∈ (FiniteSet.ofList l : S) ↔ x ∈ l

namespace FiniteSet

variable {A : Type v} {S : Type u} [DecidableEq A] [FiniteSet A S] [FiniteSetLaws A S]

/-- Membership in singleton: true iff equal. Corresponds to Rocq's `elem_of_singleton`. -/
theorem mem_singleton (x y : A) : x ∈ (FiniteSet.singleton y : S) ↔ x = y := by
  unfold singleton insert
  constructor
  · intro h
    -- h : x ∈ ofList (y :: toList ∅)
    have h1 : x ∈ (y :: toList (∅ : S)) := (FiniteSetLaws.mem_ofList _ x).mp h
    simp [FiniteSetLaws.toList_empty] at h1
    exact h1
  · intro h
    have : x ∈ (y :: toList (∅ : S)) := by simp [FiniteSetLaws.toList_empty, h]
    exact (FiniteSetLaws.mem_ofList _ x).mpr this

/-- Membership after insert: true if equal, otherwise unchanged. -/
theorem mem_insert_eq (s : S) (x y : A) (h : x = y) : x ∈ (FiniteSet.insert y s) := by
  unfold insert
  have : x ∈ (y :: toList s) := by simp [h]
  exact (FiniteSetLaws.mem_ofList _ x).mpr this

/-- Membership after insert: unchanged if not equal. -/
theorem mem_insert_ne (s : S) (x y : A) (h : x ≠ y) : x ∈ (FiniteSet.insert y s) ↔ x ∈ s := by
  unfold insert
  constructor
  · intro hmem
    have h1 : x ∈ (y :: toList s) := (FiniteSetLaws.mem_ofList _ x).mp hmem
    cases h1 with
    | head => exact absurd rfl h
    | tail _ h' => exact (FiniteSetLaws.mem_toList s x).mp h'
  · intro hmem
    have h1 : x ∈ toList s := (FiniteSetLaws.mem_toList s x).mpr hmem
    have : x ∈ (y :: toList s) := List.Mem.tail y h1
    exact (FiniteSetLaws.mem_ofList _ x).mpr this

/-- Singleton as insert into empty. -/
theorem singleton_insert (x : A) : (FiniteSet.singleton x : S) = FiniteSet.insert x ∅ := by
  rfl

/-- Membership after erase: false if equal, otherwise unchanged. -/
theorem mem_erase_eq (s : S) (x y : A) (h : x = y) : x ∉ (FiniteSet.erase y s) := by
  intro hmem
  unfold erase at hmem
  have h1 : x ∈ (toList s).filter (fun z => decide (z ≠ y)) :=
    (FiniteSetLaws.mem_ofList _ x).mp hmem
  have h2 : x ∈ toList s ∧ decide (x ≠ y) = true := List.mem_filter.mp h1
  simp [h] at h2

/-- Membership after erase: unchanged if not equal. -/
theorem mem_erase_ne (s : S) (x y : A) (h : x ≠ y) :
    x ∈ (FiniteSet.erase y s) ↔ x ∈ s := by
  unfold erase
  constructor
  · intro hmem
    have h1 : x ∈ (toList s).filter (fun z => decide (z ≠ y)) :=
      (FiniteSetLaws.mem_ofList _ x).mp hmem
    have h2 : x ∈ toList s := (List.mem_filter.mp h1).1
    exact (FiniteSetLaws.mem_toList s x).mp h2
  · intro hmem
    have h1 : x ∈ toList s := (FiniteSetLaws.mem_toList s x).mpr hmem
    have h2 : decide (x ≠ y) = true := by simp [h]
    have : x ∈ (toList s).filter (fun z => decide (z ≠ y)) :=
      List.mem_filter.mpr ⟨h1, h2⟩
    exact (FiniteSetLaws.mem_ofList _ x).mpr this

/-- toList of singleton set is a singleton list (up to permutation). -/
theorem toList_singleton (x : A) : (FiniteSet.toList (FiniteSet.singleton x : S)).Perm [x] := by
  unfold singleton insert
  -- toList (ofList (x :: toList ∅)) should be a permutation of [x]
  have h_empty : toList (∅ : S) = [] := FiniteSetLaws.toList_empty
  have h_nodup : [x].Nodup := by simp
  have h_eq : ofList [x] = (ofList (x :: toList (∅ : S)) : S) := by simp [h_empty]
  rw [← h_eq]
  exact FiniteSetLaws.toList_ofList [x] (ofList [x]) h_nodup rfl


  /-- Converting list to set and back gives a permutation of the deduplicated list. -/
  theorem ofList_toList : ∀ (s : S),
    FiniteSet.ofList (FiniteSet.toList s) ≡ s := by
  intro s x
  constructor
  · intro h
    have : x ∈ toList s := (FiniteSetLaws.mem_ofList (toList s) x).mp h
    exact (FiniteSetLaws.mem_toList s x).mp this
  · intro h
    have : x ∈ toList s := (FiniteSetLaws.mem_toList s x).mpr h
    exact (FiniteSetLaws.mem_ofList (toList s) x).mpr this

/-- toList of union when disjoint (up to permutation). -/
theorem toList_union (X Y : S) (h : FiniteSet.Disjoint X Y) :
    ∃ l', (FiniteSet.toList (X ∪ Y)).Perm (FiniteSet.toList X ++ l') ∧
          (FiniteSet.toList Y).Perm l' := by
  -- Use toList Y as l'
  exists toList Y
  constructor
  · -- Show toList (X ∪ Y) ~ toList X ++ toList Y
    show (toList (union X Y)).Perm (toList X ++ toList Y)
    -- union X Y = ofList (toList X ++ toList Y) by definition
    unfold union
    -- Now we need: toList (ofList (toList X ++ toList Y)) ~ toList X ++ toList Y
    -- Get nodup property for toList X and toList Y
    have hnodupX := @FiniteSetLaws.toList_nodup A S _ _ _ X
    have hnodupY := @FiniteSetLaws.toList_nodup A S _ _ _ Y
    -- Since X and Y are disjoint, toList X ++ toList Y is nodup
    have hconcat_nodup : (toList X ++ toList Y).Nodup := by
      apply List.nodup_append.mpr
      constructor
      · exact hnodupX
      constructor
      · exact hnodupY
      · intro a ha b hb hab
        subst hab
        have hmemX : a ∈ X := (FiniteSetLaws.mem_toList X a).mp ha
        have hmemY : a ∈ Y := (FiniteSetLaws.mem_toList Y a).mp hb
        exact h a ⟨hmemX, hmemY⟩
    -- Apply toList_ofList axiom
    exact @FiniteSetLaws.toList_ofList A S _ _ _ (toList X ++ toList Y) (ofList (toList X ++ toList Y)) hconcat_nodup rfl
  · -- Show toList Y ~ toList Y
    exact List.Perm.refl _

/-- Membership in difference: y ∈ X \ {x} ↔ y ∈ X ∧ y ≠ x -/
theorem mem_diff_singleton (X : S) (x y : A) :
    y ∈ (FiniteSet.diff X (FiniteSet.singleton x)) ↔ (y ∈ X ∧ y ≠ x) := by
  unfold diff
  constructor
  · intro h
    have h1 : y ∈ (toList X).filter (fun z => !mem z (singleton x : S)) :=
      (FiniteSetLaws.mem_ofList _ y).mp h
    have ⟨h2, h3⟩ := List.mem_filter.mp h1
    have h4 : y ∈ X := (FiniteSetLaws.mem_toList X y).mp h2
    -- h3 : !mem y (singleton x : S) = true, so mem y (singleton x : S) = false
    have h5 : ¬(y ∈ (singleton x : S)) := by
      intro hy
      have : mem y (singleton x : S) = true := hy
      simp [this] at h3
    have h7 : y ≠ x := by
      intro heq
      apply h5
      rw [heq]
      exact (mem_singleton x x).mpr rfl
    exact ⟨h4, h7⟩
  · intro ⟨h1, h2⟩
    have h3 : y ∈ toList X := (FiniteSetLaws.mem_toList X y).mpr h1
    have h4 : ¬(y ∈ (singleton x : S)) := by
      intro h
      have : y = x := (mem_singleton y x).mp h
      exact h2 this
    have h5 : mem y (singleton x : S) = false := by
      cases h : mem y (singleton x : S)
      · rfl
      · exact absurd h h4
    have h6 : (fun z => !mem z (singleton x : S)) y = true := by
      simp [h5]
    have : y ∈ (toList X).filter (fun z => !mem z (singleton x : S)) :=
      List.mem_filter.mpr ⟨h3, h6⟩
    exact (FiniteSetLaws.mem_ofList _ y).mpr this

/-- Membership in union: x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y -/
theorem mem_union (X Y : S) (x : A) :
    x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) := by
  show mem x (union X Y) = true ↔ _
  unfold union
  constructor
  · intro h
    have h1 : x ∈ (toList X ++ toList Y) := (FiniteSetLaws.mem_ofList _ x).mp h
    have : x ∈ toList X ∨ x ∈ toList Y := List.mem_append.mp h1
    cases this with
    | inl h => exact Or.inl ((FiniteSetLaws.mem_toList X x).mp h)
    | inr h => exact Or.inr ((FiniteSetLaws.mem_toList Y x).mp h)
  · intro h
    cases h with
    | inl h =>
      have h1 : x ∈ toList X := (FiniteSetLaws.mem_toList X x).mpr h
      have : x ∈ (toList X ++ toList Y) := List.mem_append.mpr (Or.inl h1)
      exact (FiniteSetLaws.mem_ofList _ x).mpr this
    | inr h =>
      have h1 : x ∈ toList Y := (FiniteSetLaws.mem_toList Y x).mpr h
      have : x ∈ (toList X ++ toList Y) := List.mem_append.mpr (Or.inr h1)
      exact (FiniteSetLaws.mem_ofList _ x).mpr this

/-- Subset decomposition: If Y ⊆ X, then X = Y ∪ (X \ Y) up to the disjointness condition. -/
theorem union_diff (X Y : S) (h : Y ⊆ X) :
    FiniteSet.Disjoint Y (FiniteSet.diff X Y) ∧
    (X ≡ Y ∪ (FiniteSet.diff X Y)) := by
  constructor
  · -- Disjoint Y (X \ Y)
    intro z
    intro ⟨hz_in_Y, hz_in_diff⟩
    -- hz_in_diff : z ∈ X \ Y, so by diff definition z ∉ Y
    unfold diff at hz_in_diff
    have h1 : z ∈ (toList X).filter (fun w => !mem w Y) :=
      (FiniteSetLaws.mem_ofList _ z).mp hz_in_diff
    have ⟨_, h3⟩ := List.mem_filter.mp h1
    have h4 : ¬(z ∈ Y) := by
      intro hz
      have : mem z Y = true := hz
      simp [this] at h3
    exact h4 hz_in_Y
  · -- X ≡ Y ∪ (X \ Y)
    intro z
    constructor
    · intro hz_in_X
      -- If z ∈ X, either z ∈ Y or z ∈ X \ Y
      cases hz : mem z Y
      · -- z ∉ Y, so z ∈ X \ Y
        have : z ∈ diff X Y := by
          unfold diff
          have h1 : z ∈ toList X := (FiniteSetLaws.mem_toList X z).mpr hz_in_X
          have h2 : (fun w => !mem w Y) z = true := by simp [hz]
          have : z ∈ (toList X).filter (fun w => !mem w Y) :=
            List.mem_filter.mpr ⟨h1, h2⟩
          exact (FiniteSetLaws.mem_ofList _ z).mpr this
        exact (mem_union Y (diff X Y) z).mpr (Or.inr this)
      · -- z ∈ Y
        have : z ∈ Y := hz
        exact (mem_union Y (diff X Y) z).mpr (Or.inl this)
    · intro hz_in_union
      have : z ∈ Y ∨ z ∈ diff X Y := (mem_union Y (diff X Y) z).mp hz_in_union
      cases this with
      | inl h' => exact h z h'
      | inr h' =>
        unfold diff at h'
        have h1 : z ∈ (toList X).filter (fun w => !mem w Y) :=
          (FiniteSetLaws.mem_ofList _ z).mp h'
        have ⟨h2, _⟩ := List.mem_filter.mp h1
        exact (FiniteSetLaws.mem_toList X z).mp h2

/-- Membership in filter: x ∈ filter φ X ↔ x ∈ X ∧ φ x = true -/
theorem mem_filter (X : S) (φ : A → Bool) (x : A) :
    x ∈ (FiniteSet.filter φ X) ↔ (x ∈ X ∧ φ x = true) := by
  unfold filter
  constructor
  · intro h
    have h1 : x ∈ (toList X).filter φ := (FiniteSetLaws.mem_ofList _ x).mp h
    have ⟨h2, h3⟩ : x ∈ toList X ∧ φ x = true := List.mem_filter.mp h1
    exact ⟨(FiniteSetLaws.mem_toList X x).mp h2, h3⟩
  · intro ⟨h1, h2⟩
    have h3 : x ∈ toList X := (FiniteSetLaws.mem_toList X x).mpr h1
    have : x ∈ (toList X).filter φ := List.mem_filter.mpr ⟨h3, h2⟩
    exact (FiniteSetLaws.mem_ofList _ x).mpr this

/-- Corresponds to Rocq's `set_finite`. -/
theorem set_finite (X : S) : ∃ (l : List A), ∀ x, x ∈ l ↔ x ∈ X := by
  exists toList X
  intro x
  exact FiniteSetLaws.mem_toList X x

section Elements


/-- Corresponds to Rocq's `NoDup_Permutation`. -/
theorem list_perm_of_mem_eq_nodup (l₁ l₂ : List A) (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ := by
  apply List.perm_iff_count.mpr
  intro a
  rw [h1.count, h2.count]
  simp only [hmem]

/-- Corresponds to Rocq's `elements_proper`. -/
theorem toList_proper (X Y : S) (h : X ≡ Y) :
    (toList X).Perm (toList Y) := by
  have hX := @FiniteSetLaws.toList_nodup A S _ _ _ X
  have hY := @FiniteSetLaws.toList_nodup A S _ _ _ Y
  apply list_perm_of_mem_eq_nodup (toList X) (toList Y) hX hY
  intro x
  constructor
  · intro hx
    have : x ∈ X := (FiniteSetLaws.mem_toList X x).mp hx
    have : x ∈ Y := (h x).mp this
    exact (FiniteSetLaws.mem_toList Y x).mpr this
  · intro hy
    have : x ∈ Y := (FiniteSetLaws.mem_toList Y x).mp hy
    have : x ∈ X := (h x).mpr this
    exact (FiniteSetLaws.mem_toList X x).mpr this

/-- Corresponds to Rocq's `list_to_set_elements`. -/
theorem ofList_toList_equiv (X : S) : ∀ x, x ∈ (ofList (toList X) : S) ↔ x ∈ X := by
  intro x
  constructor
  · intro h
    have : x ∈ toList X := (FiniteSetLaws.mem_ofList (toList X) x).mp h
    exact (FiniteSetLaws.mem_toList X x).mp this
  · intro h
    have : x ∈ toList X := (FiniteSetLaws.mem_toList X x).mpr h
    exact (FiniteSetLaws.mem_ofList (toList X) x).mpr this

/-- Corresponds to Rocq's `elements_list_to_set`. -/
theorem toList_ofList_perm (l : List A) (h : l.Nodup) :
    (toList (ofList l : S)).Perm l := by
  exact FiniteSetLaws.toList_ofList l (ofList l : S) h rfl

/-- Corresponds to Rocq's `elements_union_singleton`. -/
theorem toList_union_singleton (X : S) (x : A) (h : x ∉ X) :
    (toList (union (singleton x) X)).Perm (x :: toList X) := by
  have hdisj : Disjoint (singleton x) X := by
    intro y
    intro ⟨h1, h2⟩
    have : y = x := (mem_singleton y x).mp h1
    rw [this] at h2
    exact h h2
  obtain ⟨l', hperm, hperm'⟩ := toList_union (singleton x) X hdisj
  have hsing := toList_singleton (A := A) (S := S) x
  have h1 : (toList (singleton x) ++ l').Perm ([x] ++ l') :=
    List.Perm.append hsing (List.Perm.refl l')
  have h2 : ([x] ++ l').Perm ([x] ++ toList X) :=
    List.Perm.append (List.Perm.refl [x]) hperm'.symm
  exact hperm.trans (h1.trans h2)

/-- Union is commutative for toList (up to permutation). -/
theorem toList_union_comm (X Y : S) :
    (FiniteSet.toList (X ∪ Y)).Perm (FiniteSet.toList (Y ∪ X)) := by
  -- Show that union X Y ≡ union Y X, then use toList_proper
  have hequiv : union X Y ≡ union Y X := by
    intro z
    constructor
    · intro h
      have : z ∈ X ∨ z ∈ Y := (mem_union X Y z).mp h
      have : z ∈ Y ∨ z ∈ X := this.symm
      exact (mem_union Y X z).mpr this
    · intro h
      have : z ∈ Y ∨ z ∈ X := (mem_union Y X z).mp h
      have : z ∈ X ∨ z ∈ Y := this.symm
      exact (mem_union X Y z).mpr this
  exact toList_proper (union X Y) (union Y X) hequiv

/-- toList of set difference (up to permutation). -/
theorem toList_sdiff (X : S) (x : A) (h : FiniteSet.mem x X = true) :
    ∃ l', (FiniteSet.toList X).Perm (x :: l') ∧
          (FiniteSet.toList (FiniteSet.diff X (FiniteSet.singleton x))).Perm l' := by
  have h' : x ∈ X := h
  have herase := FiniteSetLaws.set_to_list_erase X x h'
  obtain ⟨l', hperm, heq⟩ := herase
  have hmem_eq : ∀ y, y ∈ erase x X ↔ y ∈ diff X (singleton x) := by
    intro y
    constructor
    · intro hy
      cases heq_y : decide (y = x)
      · -- y ≠ x
        have hne : y ≠ x := by
          intro heq
          subst heq
          simp at heq_y
        have : y ∈ X := (mem_erase_ne X y x hne).mp hy
        exact (mem_diff_singleton X x y).mpr ⟨this, hne⟩
      · simp at heq_y
        have : y ∉ erase x X := mem_erase_eq X y x heq_y
        exact absurd hy this
    · intro hy
      have ⟨hy_in_X, hy_ne⟩ := (mem_diff_singleton X x y).mp hy
      exact (mem_erase_ne X y x hy_ne).mpr hy_in_X
  exists l'
  constructor
  · exact hperm
  · rw [← heq]
    apply List.Perm.symm
    apply toList_proper
    intro y
    exact hmem_eq y

  /-- Corresponds to Rocq's `elements_submseteq`  -/
  theorem toList_subset : ∀ (X Y : S), Y ⊆ X →
    ∃ l, (FiniteSet.toList Y ++ l).Perm (FiniteSet.toList X) := by
    intro X Y h
    -- Use union_diff to decompose X into Y ∪ (X \ Y)
    have ⟨hdisj, hequiv⟩ := union_diff X Y h
    -- Get the permutation from toList_union
    obtain ⟨l', hperm, hperm'⟩ := toList_union Y (diff X Y) hdisj
    -- Use l' as the witness
    exists l'
    -- Show (toList Y ++ l') ~ toList X
    -- We know toList (Y ∪ (X \ Y)) ~ toList Y ++ l' from hperm
    -- and toList X ~ toList (Y ∪ (X \ Y)) from hequiv
    have h1 : (toList X).Perm (toList (Y ∪ (diff X Y))) :=
      toList_proper X (Y ∪ (diff X Y)) hequiv
    have h2 : (toList (Y ∪ (diff X Y))).Perm (toList Y ++ l') := hperm
    exact (h1.trans h2).symm

end Elements

section Size

/-- Corresponds to Rocq's `size_empty`. -/
theorem size_empty : size (∅ : S) = 0 := by
  unfold size
  rw [FiniteSetLaws.toList_empty]
  rfl

/-- Corresponds to Rocq's `size_empty_iff`. -/
theorem size_empty_iff (X : S) : size X = 0 ↔ ∀ x, x ∉ X := by
  constructor
  · intro hsize x
    unfold size at hsize
    have hnil : toList X = [] := List.eq_nil_of_length_eq_zero hsize
    intro hmem
    have : x ∈ toList X := (FiniteSetLaws.mem_toList X x).mpr hmem
    rw [hnil] at this
    cases this
  · intro hempty
    unfold size
    cases hlist : toList X with
    | nil => rfl
    | cons x xs =>
      have : x ∈ toList X := by rw [hlist]; exact List.mem_cons_self ..
      have : x ∈ X := (FiniteSetLaws.mem_toList X x).mp this
      exact absurd this (hempty x)

/-- Corresponds to Rocq's `size_singleton`. -/
theorem size_singleton (x : A) : size (singleton x : S) = 1 := by
  unfold size
  have h := toList_singleton (A := A) (S := S) x
  have : [x].length = 1 := rfl
  rw [← this, ← h.length_eq]

/-- Corresponds to Rocq's `set_choose`. -/
theorem set_choose (X : S) (h : size X ≠ 0) : ∃ x, x ∈ X := by
  unfold size at h
  cases hlist : toList X with
  | nil =>
    rw [hlist] at h
    simp at h
  | cons x l =>
    exists x
    have : x ∈ toList X := by rw [hlist]; exact List.mem_cons_self ..
    exact (FiniteSetLaws.mem_toList X x).mp this

/-- Corresponds to Rocq's `size_union`. -/
theorem size_union (X Y : S) (h : Disjoint X Y) :
    size (X ∪ Y) = size X + size Y := by
  unfold size
  obtain ⟨l', hperm, hperm'⟩ := toList_union X Y h
  rw [hperm.length_eq, List.length_append, hperm'.length_eq]

/-- Subset implies smaller or equal size. Corresponds to Rocq's `subseteq_size`. -/
theorem subseteq_size (X Y : S) (h : X ⊆ Y) : size X ≤ size Y := by
  have ⟨hdisj, heq⟩ := union_diff Y X h
  -- Y = X ∪ (Y \ X) in terms of membership, and X and Y \ X are disjoint
  -- We can use toList_proper to show Y and X ∪ (Y \ X) have the same size
  -- Use toList_proper to get that the lists have the same length
  have hperm := toList_proper Y (X ∪ (Y \ X)) heq
  have hsize_eq : size Y = size (X ∪ (Y \ X)) := by
    unfold size
    exact hperm.length_eq
  rw [hsize_eq]
  have hsize := size_union X (Y \ X) hdisj
  omega

/-- Proper subset implies strictly smaller size. Corresponds to Rocq's `subset_size`. -/
theorem subset_size (X Y : S) (h : X ⊆ Y) (hne : ∃ x, x ∈ Y ∧ x ∉ X) :
    size X < size Y := by
  have ⟨x, hmemY, hmemX⟩ := hne
  -- Derive: size Y = size X + size (Y \ X) from union_diff
  have ⟨hdisj, heq⟩ := union_diff Y X h
  have hsize_union := size_union X (Y \ X) hdisj
  have hsize_y : size Y = size X + size (Y \ X) := by
    have hperm := toList_proper Y (X ∪ (Y \ X)) heq
    calc size Y
      _ = size (X ∪ (Y \ X)) := by unfold size; exact hperm.length_eq
      _ = size X + size (Y \ X) := hsize_union
  -- Show size (Y \ X) ≠ 0 because x ∈ Y \ X
  have hdiff : size (Y \ X) ≠ 0 := by
    intro hcontra
    have hnotmem : ∀ z, z ∉ (Y \ X) := (size_empty_iff (Y \ X)).mp hcontra
    have : ∀ z, mem z (Y \ X) = false := fun z => by
      cases h : mem z (Y \ X)
      · rfl
      · have : z ∈ (Y \ X) := h
        exact absurd this (hnotmem z)
    -- But x ∈ Y \ X
    have hx_in_diff : mem x (Y \ X) = true := by
      -- heq x says: x ∈ Y ↔ x ∈ (X ∪ (Y \ X))
      -- We have x ∈ Y and ¬(x ∈ X)
      -- So x ∈ (Y \ X)
      have h1 : x ∈ (X ∪ (Y \ X)) := (heq x).mp hmemY
      have h2 : x ∈ X ∨ x ∈ (Y \ X) := (mem_union X (Y \ X) x).mp h1
      cases h2 with
      | inl h' =>
        -- Contradiction: x ∈ X but hmemX says ¬(x ∈ X)
        exact absurd h' hmemX
      | inr h => exact h
    rw [this x] at hx_in_diff
    cases hx_in_diff
  omega

/-- Size of difference. Corresponds to Rocq's `size_difference`. -/
theorem size_difference (X Y : S) (h : Y ⊆ X) :
    size (X \ Y) = size X - size Y := by
  have ⟨hdisj, heq⟩ := union_diff X Y h
  -- X = Y ∪ (X \ Y) and they are disjoint
  -- Use size_union
  have hsize_union := size_union Y (X \ Y) hdisj
  have : size X = size Y + size (X \ Y) := by
    have hperm := toList_proper X (Y ∪ (X \ Y)) heq
    calc size X
      _ = size (Y ∪ (X \ Y)) := by unfold size; exact hperm.length_eq
      _ = size Y + size (X \ Y) := hsize_union
  omega

end Size

section Filter

/-- Membership in filter. Corresponds to Rocq's `elem_of_filter`. -/
theorem mem_filter' (P : A → Bool) (X : S) (x : A) :
    x ∈ (filter P X) ↔ P x = true ∧ x ∈ X := by
  have h := mem_filter X P x
  constructor
  · intro hf
    have ⟨h1, h2⟩ := h.mp hf
    exact ⟨h2, h1⟩
  · intro ⟨hp, hm⟩
    exact h.mpr ⟨hm, hp⟩

/-- Filter of empty set is empty. Corresponds to Rocq's `filter_empty`. -/
theorem filter_empty (P : A → Bool) : filter P (∅ : S) ≡ ∅ := by
  intro x
  constructor
  · intro h
    -- If x ∈ filter P ∅, then x ∈ ∅, contradiction
    have : x ∈ (∅ : S) := (mem_filter (∅ : S) P x).mp h |>.1
    exact absurd this (FiniteSetLaws.mem_empty (A := A) x)
  · intro h
    -- If x ∈ ∅, that's a contradiction
    exact absurd h (FiniteSetLaws.mem_empty (A := A) x)

/-- Filter of singleton. Corresponds to Rocq's `filter_singleton`. -/
theorem filter_singleton (P : A → Bool) (x : A) :
    filter P (singleton x : S) ≡ if P x then singleton x else ∅ := by
  intro y
  -- Split on whether P x is true or false
  split
  · -- Case: P x = true, so filter P {x} ≡ {x}
    rename_i hpx
    constructor
    · intro h
      -- If y ∈ filter P {x}, then y ∈ {x}
      exact (mem_filter (singleton x : S) P y).mp h |>.1
    · intro h
      -- If y ∈ {x}, then y = x and P y = P x = true, so y ∈ filter P {x}
      have : y = x := (mem_singleton y x).mp h
      have : P y = true := by rw [this, hpx]
      exact (mem_filter (singleton x : S) P y).mpr ⟨h, this⟩
  · -- Case: P x = false, so filter P {x} ≡ ∅
    rename_i hpx
    constructor
    · intro h
      -- If y ∈ filter P {x}, then y ∈ {x} and P y = true
      have ⟨hmem_sing, hpy⟩ := (mem_filter (singleton x : S) P y).mp h
      -- Also y ∈ {x}, so y = x
      have : y = x := (mem_singleton (S := S) (A := A) y x).mp hmem_sing
      -- But then P x = P y = true, contradicting hpx
      subst this
      exact False.elim (hpx hpy)
    · intro h
      -- If y ∈ ∅, that's a contradiction
      exact absurd h (FiniteSetLaws.mem_empty (A := A) y)

/-- Filter distributes over union. Corresponds to Rocq's `filter_union`. -/
theorem filter_union (P : A → Bool) (X Y : S) :
    filter P (X ∪ Y) ≡ filter P X ∪ filter P Y := by
  intro x
  constructor
  · intro h
    -- x ∈ filter P (X ∪ Y), so x ∈ X ∪ Y and P x
    have ⟨hmem_union, hpx⟩ := (mem_filter (X ∪ Y) P x).mp h
    -- x ∈ X ∪ Y means x ∈ X or x ∈ Y
    have : x ∈ X ∨ x ∈ Y := (mem_union X Y x).mp hmem_union
    cases this with
    | inl hmem_x =>
      -- x ∈ X and P x, so x ∈ filter P X, so x ∈ filter P X ∪ filter P Y
      have : x ∈ filter P X := (mem_filter X P x).mpr ⟨hmem_x, hpx⟩
      exact (mem_union (filter P X) (filter P Y) x).mpr (Or.inl this)
    | inr hmem_y =>
      -- x ∈ Y and P x, so x ∈ filter P Y, so x ∈ filter P X ∪ filter P Y
      have : x ∈ filter P Y := (mem_filter Y P x).mpr ⟨hmem_y, hpx⟩
      exact (mem_union (filter P X) (filter P Y) x).mpr (Or.inr this)
  · intro h
    -- x ∈ filter P X ∪ filter P Y means (x ∈ filter P X) ∨ (x ∈ filter P Y)
    have : x ∈ filter P X ∨ x ∈ filter P Y :=
      (mem_union (filter P X) (filter P Y) x).mp h
    cases this with
    | inl h =>
      -- x ∈ filter P X, so x ∈ X and P x, so x ∈ X ∪ Y and P x, so x ∈ filter P (X ∪ Y)
      have ⟨hmem_x, hpx⟩ := (mem_filter X P x).mp h
      have : x ∈ X ∪ Y := (mem_union X Y x).mpr (Or.inl hmem_x)
      exact (mem_filter (X ∪ Y) P x).mpr ⟨this, hpx⟩
    | inr h =>
      -- x ∈ filter P Y, so x ∈ Y and P x, so x ∈ X ∪ Y and P x, so x ∈ filter P (X ∪ Y)
      have ⟨hmem_y, hpx⟩ := (mem_filter Y P x).mp h
      have : x ∈ X ∪ Y := (mem_union X Y x).mpr (Or.inr hmem_y)
      exact (mem_filter (X ∪ Y) P x).mpr ⟨this, hpx⟩

/-- Disjointness of filter and complement. Corresponds to Rocq's `disjoint_filter_complement`. -/
theorem disjoint_filter_complement (P : A → Bool) (X : S) :
    Disjoint (filter P X) (filter (fun x => !P x) X) := by
  intro x
  intro ⟨h1, h2⟩
  -- h1: mem x (filter P X) = true means P x = true
  -- h2: mem x (filter (!P) X) = true means !P x = true, i.e., P x = false
  have ⟨_, hpx_true⟩ := (mem_filter X P x).mp h1
  have ⟨_, hpx_false⟩ := (mem_filter X (fun y => !P y) x).mp h2
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
theorem set_wf : WellFounded (fun (X Y : S) => X ⊆ Y ∧ ∃ x, x ∈ Y ∧ x ∉ X) := by
  -- Well-founded because size decreases for proper subsets
  have h_sub : ∀ X Y, (X ⊆ Y ∧ ∃ x, x ∈ Y ∧ x ∉ X) → size (S := S) (A := A) X < size (S := S) (A := A) Y := by
    intro X Y ⟨hsub, x, hmemY, hmemX⟩
    exact subset_size X Y hsub ⟨x, hmemY, hmemX⟩
  apply Subrelation.wf
  · intro X Y hrel
    exact h_sub X Y hrel
  · exact (measure (size (S := S) (A := A))).wf

/-- Corresponds to Rocq's `set_ind`. -/
theorem set_ind {P : S → Prop}
    (proper : ∀ X Y, X ≡ Y → P X → P Y)
    (hemp : P ∅)
    (hadd : ∀ x X, x ∉ X → P X → P (union (singleton x) X))
    (X : S) : P X := by
  -- Use well-founded induction based on set_wf
  apply WellFounded.induction set_wf X
  intro Y IH
  -- Case split on whether Y is empty
  cases hsize : size Y with
  | zero =>
    -- Y is empty, so use hemp
    have hempty_equiv : ∀ x, x ∉ Y := (size_empty_iff Y).mp hsize
    -- Show P Y by using proper to transfer from ∅
    have hY_equiv : ∅ ≡ Y := by
      intro x
      constructor
      · intro h
        exact absurd h (FiniteSetLaws.mem_empty x)
      · intro h
        exact absurd h (hempty_equiv x)
    exact proper ∅ Y hY_equiv hemp
  | succ n =>
    -- Y is non-empty, so pick an element x ∈ Y
    have ⟨x, hx⟩ := set_choose Y (by omega)
    -- Let Y' = Y \ {x}
    let Y' := diff Y (singleton x)
    -- Show that Y' is a proper subset of Y
    have hsub : Y' ⊆ Y := by
      intro z hz
      have ⟨hz_in_Y, _⟩ := (mem_diff_singleton Y x z).mp hz
      exact hz_in_Y
    have hproper : ∃ y, y ∈ Y ∧ y ∉ Y' := by
      exists x
      constructor
      · exact hx
      · intro hcontra
        have ⟨_, hne⟩ := (mem_diff_singleton Y x x).mp hcontra
        exact hne rfl
    -- Apply IH to Y'
    have hP_Y' : P Y' := IH Y' ⟨hsub, hproper⟩
    -- Show x ∉ Y'
    have hx_notin : x ∉ Y' := by
      intro hcontra
      have ⟨_, hne⟩ := (mem_diff_singleton Y x x).mp hcontra
      exact hne rfl
    -- Apply hadd
    have hP_union : P (union (singleton x) Y') := hadd x Y' hx_notin hP_Y'
    -- Show Y ≡ union (singleton x) Y' using union_diff
    have hY_equiv : union (singleton x) Y' ≡ Y := by
      intro z
      -- Use the union_diff theorem
      have hsub_singleton : singleton x ⊆ Y := by
        intro w hw
        have : w = x := (mem_singleton w x).mp hw
        rw [this]
        exact hx
      have ⟨_, heq⟩ := union_diff Y (singleton x) hsub_singleton
      -- heq shows Y ≡ singleton x ∪ (Y \ singleton x)
      -- Y' = diff Y (singleton x), so this is exactly what we need
      exact (heq z).symm
    -- Use proper to transfer P from union (singleton x) Y' to Y
    exact proper (union (singleton x) Y') Y hY_equiv hP_union

end SetInduction

section Map

/-- Map operation on sets. Maps a function over all elements.
    Corresponds to Rocq's `set_map`. -/
def map {B : Type w} [DecidableEq B] [FiniteSet A S] [FiniteSet B S']
    (f : A → B) (X : S) : S' :=
  ofList ((toList X).map f)

/-- Membership in mapped set. Corresponds to Rocq's `elem_of_map`. -/
theorem mem_map {B : Type w} {S' : Type u} [DecidableEq B] [FiniteSet B S'] [FiniteSetLaws B S']
    (f : A → B) (X : S) (y : B) :
    y ∈ (map f X : S') ↔ ∃ x, y = f x ∧ x ∈ X := by
  unfold map
  have h_ofList := FiniteSetLaws.mem_ofList (A := B) (S := S') (List.map f (toList X)) y
  constructor
  · intro h
    have : y ∈ (ofList (List.map f (toList X)) : S') := h
    have : y ∈ List.map f (toList X) := h_ofList.mp this
    have ⟨x, hmem, hx⟩ := List.mem_map.mp this
    exact ⟨x, hx.symm, (FiniteSetLaws.mem_toList X x).mp hmem⟩
  · intro ⟨x, hf, hmem⟩
    have : y ∈ List.map f (toList X) := by
      rw [List.mem_map]
      exact ⟨x, (FiniteSetLaws.mem_toList X x).mpr hmem, hf.symm⟩
    have : y ∈ (ofList (List.map f (toList X)) : S') := h_ofList.mpr this
    exact this

/-- Map of empty set. Corresponds to Rocq's `set_map_empty`. -/
theorem map_empty {B : Type w} {S' : Type u} [DecidableEq B] [FiniteSet B S'] [FiniteSetLaws B S']
    (f : A → B) :
    map f (∅ : S) = (∅ : S') := by
  unfold map
  rw [FiniteSetLaws.toList_empty, List.map_nil, FiniteSetLaws.ofList_nil]

/-- Map distributes over union. Corresponds to Rocq's `set_map_union`. -/
theorem map_union {B : Type w} {S' : Type u} [DecidableEq B] [FiniteSet B S'] [FiniteSetLaws B S']
    (f : A → B) (X Y : S) :
    map f (X ∪ Y : S) ≡ (map f X ∪ map f Y : S') := by
  intro z
  constructor
  · intro h
    -- z ∈ map f (X ∪ Y), so ∃ x ∈ X ∪ Y such that z = f x
    have ⟨x, hfx, hx⟩ := mem_map f (X ∪ Y : S) z |>.mp h
    have := (mem_union X Y x).mp hx
    cases this with
    | inl h =>
      -- x ∈ X, so z = f x ∈ map f X, so z ∈ map f X ∪ map f Y
      exact (mem_union (map f X : S') (map f Y : S') z).mpr
        (Or.inl (mem_map f X z |>.mpr ⟨x, hfx, h⟩))
    | inr h =>
      -- x ∈ Y, so z = f x ∈ map f Y, so z ∈ map f X ∪ map f Y
      exact (mem_union (map f X : S') (map f Y : S') z).mpr
        (Or.inr (mem_map f Y z |>.mpr ⟨x, hfx, h⟩))
  · intro h
    -- z ∈ map f X ∪ map f Y means z ∈ map f X or z ∈ map f Y
    have := (mem_union (map f X : S') (map f Y : S') z).mp h
    cases this with
    | inl h =>
      -- z ∈ map f X, so ∃ x ∈ X such that z = f x, so z ∈ map f (X ∪ Y)
      have ⟨x, hfx, hx⟩ := mem_map (A := A) (S := S) (S' := S') f X z |>.mp h
      exact mem_map (A := A) (S := S) (S' := S') f (X ∪ Y : S) z |>.mpr
        ⟨x, hfx, (mem_union X Y x).mpr (Or.inl hx)⟩
    | inr h =>
      -- z ∈ map f Y, so ∃ x ∈ Y such that z = f x, so z ∈ map f (X ∪ Y)
      have ⟨x, hfx, hx⟩ := mem_map (A := A) (S := S) (S' := S') f Y z |>.mp h
      exact mem_map (A := A) (S := S) (S' := S') f (X ∪ Y : S) z |>.mpr
        ⟨x, hfx, (mem_union X Y x).mpr (Or.inr hx)⟩

/-- Map of singleton. Corresponds to Rocq's `set_map_singleton`. -/
theorem map_singleton {B : Type w} {S' : Type u} [DecidableEq B] [FiniteSet B S'] [FiniteSetLaws B S']
    (f : A → B) (x : A) :
    (map f (singleton x : S) : S') ≡ (singleton (f x) : S') := by
  intro y
  constructor
  · intro h
    -- y ∈ map f {x}, so ∃ z ∈ {x} such that y = f z
    have ⟨z, hfz, hz⟩ := mem_map f (singleton x : S) y |>.mp h
    -- z ∈ {x} means z = x
    have : z = x := (mem_singleton z x).mp hz
    rw [this] at hfz
    -- So y = f x, meaning y ∈ {f x}
    exact (mem_singleton y (f x)).mpr hfz
  · intro h
    -- y ∈ {f x} means y = f x
    have : y = f x := (mem_singleton y (f x)).mp h
    rw [this]
    -- f x ∈ map f {x} because x ∈ {x}
    exact mem_map f (singleton x : S) (f x) |>.mpr
      ⟨x, rfl, (mem_singleton x x).mpr rfl⟩

end Map

section Bind
variable {B : Type _} {S' : Type u} [DecidableEq B] [FiniteSet B S'] [FiniteSetLaws B S']

/-- Membership in bind. Corresponds to Rocq's `elem_of_set_bind`. -/
theorem mem_bind (f : A → S') (X : S) (y : B) :
     y ∈ (bind f X) ↔ ∃ x, x ∈ X ∧ y ∈ (f x) := by
  unfold bind
  rw [FiniteSetLaws.mem_ofList]
  rw [List.mem_flatMap]
  constructor
  · intro ⟨x, hx_in, hy_in⟩
    exact ⟨x, (FiniteSetLaws.mem_toList X x).mp hx_in, (FiniteSetLaws.mem_toList (f x) y).mp hy_in⟩
  · intro ⟨x, hx, hy⟩
    exact ⟨x, (FiniteSetLaws.mem_toList X x).mpr hx, (FiniteSetLaws.mem_toList (f x) y).mpr hy⟩

/-- Bind of singleton. Corresponds to Rocq's `set_bind_singleton`. -/
theorem bind_singleton (f : A → S') (x : A) :
    ∀ y, y ∈ (bind f (singleton (S := S) x)) ↔ y ∈ (f x) := by
  intro y
  constructor
  · intro h
    have ⟨z, hz, hmem⟩ := (mem_bind f (singleton x) y).mp h
    have : z = x := (mem_singleton z x).mp hz
    rw [this] at hmem
    exact hmem
  · intro h
    exact (mem_bind f (singleton x) y).mpr ⟨x, (mem_singleton x x).mpr rfl, h⟩

end Bind

section Omap
variable {B : Type w} {S' : Type u} [DecidableEq B] [FiniteSet B S'] [FiniteSetLaws B S']

/-- Membership in omap. Corresponds to Rocq's `elem_of_set_omap`. -/
theorem mem_omap
    (f : A → Option B) (X : S) (y : B) :
    y ∈ (omap f X : S') ↔ ∃ x, x ∈ X ∧ f x = some y := by
  unfold omap
  rw [FiniteSetLaws.mem_ofList]
  rw [List.mem_filterMap]
  constructor
  · intro ⟨x, hx_in, hfx⟩
    exact ⟨x, (FiniteSetLaws.mem_toList X x).mp hx_in, hfx⟩
  · intro ⟨x, hx, hfx⟩
    exact ⟨x, (FiniteSetLaws.mem_toList X x).mpr hx, hfx⟩

/-- Omap of empty set. Corresponds to Rocq's `set_omap_empty`. -/
theorem omap_empty (f : A → Option B) : omap f (∅ : S) = (∅ : S') := by
  unfold omap
  rw [FiniteSetLaws.toList_empty, List.filterMap_nil, FiniteSetLaws.ofList_nil]

/-- Omap distributes over union. Corresponds to Rocq's `set_omap_union`. -/
theorem omap_union (f : A → Option B) (X Y : S) :
    ∀ z, z ∈ (omap f (X ∪ Y : S) : S') ↔ z ∈ ((omap f X : S') ∪ (omap f Y : S')) := by
  intro z
  constructor
  · intro h
    have ⟨x, hx, hfx⟩ := (mem_omap f (X ∪ Y : S) z).mp h
    have : x ∈ X ∨ x ∈ Y := (mem_union X Y x).mp hx
    cases this with
    | inl hx_in_X =>
      have : z ∈ (omap f X : S') := (mem_omap f X z).mpr ⟨x, hx_in_X, hfx⟩
      exact (mem_union (omap f X : S') (omap f Y : S') z).mpr (Or.inl this)
    | inr hx_in_Y =>
      have : z ∈ (omap f Y : S') := (mem_omap f Y z).mpr ⟨x, hx_in_Y, hfx⟩
      exact (mem_union (omap f X : S') (omap f Y : S') z).mpr (Or.inr this)
  · intro h
    have : z ∈ (omap f X : S') ∨ z ∈ (omap f Y : S') :=
      (mem_union (omap f X : S') (omap f Y : S') z).mp h
    cases this with
    | inl hz_in_X =>
      have ⟨x, hx, hfx⟩ := (mem_omap f X z).mp hz_in_X
      have : x ∈ (X ∪ Y) := (mem_union X Y x).mpr (Or.inl hx)
      exact (mem_omap f (X ∪ Y : S) z).mpr ⟨x, this, hfx⟩
    | inr hz_in_Y =>
      have ⟨x, hx, hfx⟩ := (mem_omap f Y z).mp hz_in_Y
      have : x ∈ (X ∪ Y) := (mem_union X Y x).mpr (Or.inr hx)
      exact (mem_omap f (X ∪ Y : S) z).mpr ⟨x, this, hfx⟩

/-- Omap of singleton when function returns Some. -/
theorem omap_singleton_some (f : A → Option B) (x : A) (y : B) (h : f x = some y) :
    ∀ z, mem z (omap f (singleton x : S) : S') = mem z (singleton y : S') := by
  intro z
  cases h1 : mem z (omap f (singleton x : S) : S') <;>
  cases h2 : mem z (singleton y : S')
  · rfl
  · -- Contradiction
    have : z = y := (mem_singleton z y).mp h2
    rw [this] at h1
    have : mem y (omap f (singleton x : S) : S') = true :=
      mem_omap f (singleton x : S) y |>.mpr
        ⟨x, (mem_singleton x x).mpr rfl, h⟩
    rw [h1] at this
    cases this
  · -- Contradiction: mem z (omap f {x}) = true but f x = some y and mem z {y} = false
    have ⟨w, hw, hfw⟩ := mem_omap f (singleton x : S) z |>.mp h1
    have wx : w = x := (mem_singleton w x).mp hw
    rw [wx] at hfw
    -- hfw : f x = some z, but we know f x = some y
    rw [h] at hfw
    -- Now hfw : some y = some z, so y = z
    cases hfw
    -- But now we have mem y (singleton y) = false, contradiction
    have : mem y (singleton y : S') = true := (mem_singleton y y).mpr rfl
    rw [h2] at this
    cases this
  · rfl

/-- Omap of singleton when function returns None. -/
theorem omap_singleton_none (f : A → Option B) (x : A) (h : f x = none) :
    omap f (singleton x : S) ≡ (∅ : S') := by
  intro z
  constructor
  · intro h1
    -- z ∈ omap f {x}, so ∃ w ∈ {x} such that f w = some z
    have ⟨w, hw, hfw⟩ := mem_omap f (singleton x : S) z |>.mp h1
    -- w ∈ {x} means w = x
    have : w = x := (mem_singleton w x).mp hw
    -- So f x = some z, but h says f x = none - contradiction
    rw [this] at hfw
    rw [h] at hfw
    cases hfw
  · intro h2
    -- z ∈ ∅ is a contradiction
    exact absurd h2 (FiniteSetLaws.mem_empty (A := B) z)

end Omap

end FiniteSet

end Iris.Std
