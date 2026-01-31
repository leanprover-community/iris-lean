/-
Copyright (c) 2026 Zongyuan Liu, Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Markus de Medeiros
-/

import Iris.Std.List

/-! ## Partial Map Base Abstraction

This file defines the base abstraction for partial maps (maps from keys to optional values).
Both `FiniteMap` and `Heap` extend this base interface.

The type `M` represents a partial map from keys of type `K` to values of type `V`.
-/

namespace Iris.Std

/-- Base typeclass for partial maps: maps from keys `K` to optional values `V`. -/
class PartialMap (K : outParam (Type u)) (M : Type u' → Type _) where
  /-- Lookup a key in the map, returning `none` if not present. -/
  get? : M V → K → Option V
  /-- Insert or update a key-value pair. -/
  insert : M V → K → V → M V
  /-- Remove a key from the map. -/
  delete : M V → K → M V
  /-- The empty map. -/
  empty : M V

export PartialMap (get? insert delete empty)

namespace PartialMap

variable {K : Type u} {V : Type u'} {M : Type u' → Type _} [PartialMap K M]

/-- Singleton map containing exactly one key-value pair. -/
def singleton (k : K) (v : V) : M V := insert empty k v

/-- Two maps have disjoint domains. -/
def disjoint (m₁ m₂ : M V) : Prop := ∀ k, ¬((get? m₁ k).isSome ∧ (get? m₂ k).isSome)

/-- Submap relation: `m₁` is a submap of `m₂` if every key-value pair in `m₁` is also in `m₂`. -/
def submap (m₁ m₂ : M V) : Prop := ∀ k v, get? m₁ k = some v → get? m₂ k = some v

instance : HasSubset (M V) := ⟨submap⟩

-- /-- Union of two maps (left-biased: values from `m₁` take precedence).
--     Note: This requires an implementation-specific definition.
--     FiniteMap provides a concrete implementation using toList. -/
-- noncomputable def union (m₁ m₂ : M V) : M V := Classical.choice ⟨m₁⟩
--
-- noncomputable instance : Union (M V) := ⟨union⟩

/-- Membership: a key is in the map if it has a value. -/
def mem (m : M V) (k : K) : Prop := (get? m k).isSome

/-- Universal quantification over map entries. -/
def Forall (P : K → V → Prop) (m : M V) : Prop :=
  ∀ k v, get? m k = some v → P k v

end PartialMap

/-- Empty instance for partial maps. -/
instance {K : Type u} {M : Type u' → Type _} [PartialMap K M] :
    EmptyCollection (M V) := ⟨PartialMap.empty⟩

/-- Membership instance for partial maps: `k ∈ m` means the key `k` is in the map `m`. -/
instance {K : Type u} {M : Type u' → Type _} [inst : PartialMap K M] :
    Membership K (M V) := ⟨fun (m : M V) (k : K) => (inst.get? m k).isSome⟩

/-- Notation for singleton map: `{[k := v]}` -/
scoped syntax "{[" term " := " term "]}" : term

scoped macro_rules
  | `({[$k := $v]}) => `(PartialMap.singleton $k $v)

/-- Notation for map disjointness: `m₁ ##ₘ m₂` -/
scoped infix:50 " ##ₘ " => PartialMap.disjoint

/-- Laws that a partial map implementation must satisfy. -/
class PartialMapLaws (K : outParam (Type u)) (M : Type u' → Type _)
    [DecidableEq K] [PartialMap K M] where
  ext : ∀ (m₁ m₂ : M V), (∀ i, get? m₁ i = get? m₂ i) → m₁ = m₂
  get?_empty : ∀ k, get? (empty : M V) k = none
  get?_insert_same : ∀ (m : M V) k v, get? (insert m k v) k = some v
  get?_insert_ne : ∀ (m : M V) k k' v, k ≠ k' → get? (insert m k v) k' = get? m k'
  get?_delete_same : ∀ (m : M V) k, get? (delete m k) k = none
  get?_delete_ne : ∀ (m : M V) k k', k ≠ k' → get? (delete m k) k' = get? m k'

export PartialMapLaws (ext
  get?_empty
  get?_insert_same get?_insert_ne
  get?_delete_same get?_delete_ne)

namespace PartialMapLaws

variable {K : Type u} {V : Type u'} {M : Type u' → Type _}
variable [DecidableEq K] [PartialMap K M] [PartialMapLaws K M]

theorem get?_insert (m : M V) (k k' : K) (v : V) :
    get? (insert m k v) k' = if k = k' then some v else get? m k' := by
  split
  · next h => rw [h, get?_insert_same]
  · next h => exact get?_insert_ne m k k' v h

theorem get?_delete (m : M V) (k k' : K) :
    get? (delete m k) k' = if k = k' then none else get? m k' := by
  split
  · next h => rw [h, get?_delete_same]
  · next h => exact get?_delete_ne m k k' h

theorem get?_insert_delete (m : M V) (k k' : K) (v : V) :
    get? (insert (delete m k) k v) k' = get? (insert m k v) k' := by
  by_cases h : k = k'
  · simp [h, get?_insert_same]
  · simp [get?_insert_ne _ _ _ _ h, get?_delete_ne _ _ _ h]

/-- Singleton lookup for equal keys. -/
theorem get?_singleton_same (k : K) (v : V) :
    get? ({[k := v]} : M V) k = some v := by
  simp [PartialMap.singleton, get?_insert_same]

/-- Singleton lookup for different keys. -/
theorem get?_singleton_ne (k k' : K) (v : V) (h : k ≠ k') :
    get? ({[k := v]} : M V) k' = none := by
  simp [PartialMap.singleton, get?_insert_ne _ _ _ _ h, get?_empty]

/-- Singleton lookup general case. -/
theorem get?_singleton (k k' : K) (v : V) :
    get? ({[k := v]} : M V) k' = if k = k' then some v else none := by
  split
  · next h => rw [h, get?_singleton_same]
  · next h => exact get?_singleton_ne k k' v h

theorem empty_subset (m : M V) : (∅ : M V) ⊆ m := by
  intro k v h
  have : get? (∅ : M V) k = none := get?_empty k
  rw [this] at h
  cases h

theorem disjoint_empty_left (m : M V) : (∅ : M V) ##ₘ m := by
  intro k ⟨h₁, _⟩
  have : get? (∅ : M V) k = none := get?_empty k
  rw [this] at h₁
  cases h₁

theorem get?_insert_some (m : M V) (i j : K) (x y : V) :
    get? (insert m i x) j = some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ get? m j = some y) := by
  rw [get?_insert]
  split <;> simp_all

theorem get?_insert_isSome (m : M V) (i j : K) (x : V) :
    (get? (insert m i x) j).isSome ↔ i = j ∨ (i ≠ j ∧ (get? m j).isSome) := by
  rw [get?_insert]
  split <;> simp_all

theorem get?_insert_none (m : M V) (i j : K) (x : V) :
    get? (insert m i x) j = none ↔ get? m j = none ∧ i ≠ j := by
  rw [get?_insert]
  split <;> simp_all

theorem get?_delete_some (m : M V) (i j : K) (y : V) :
    get? (delete m i) j = some y ↔ i ≠ j ∧ get? m j = some y := by
  rw [get?_delete]
  split <;> simp_all

theorem get?_delete_isSome (m : M V) (i j : K) :
    (get? (delete m i) j).isSome ↔ i ≠ j ∧ (get? m j).isSome := by
  rw [get?_delete]
  split <;> simp_all

theorem get?_delete_none (m : M V) (i j : K) :
    get? (delete m i) j = none ↔ i = j ∨ get? m j = none := by
  rw [get?_delete]
  split <;> simp_all

theorem insert_delete_cancel (m : M V) (i : K) (x : V) :
    get? m i = some x → insert (delete m i) i x = m := by
  intro h
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_insert_same, h]
  · simp [get?_insert_ne _ _ _ _ hij, get?_delete_ne _ _ _ hij]

theorem delete_insert_cancel (m : M V) (i : K) (x : V) :
    get? m i = none → delete (insert m i x) i = m := by
  intro h
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_delete_same, h]
  · simp [get?_delete_ne _ _ _ hij, get?_insert_ne _ _ _ _ hij]

/-- Empty map is characterized by all lookups returning none. -/
theorem eq_empty_iff (m : M V) : m = ∅ ↔ ∀ k, get? m k = none := by
  constructor
  · intro h k
    rw [h]
    exact get?_empty k
  · intro h
    apply PartialMapLaws.ext (M := M) (K := K) (V := V)
    intro k
    rw [h k]
    exact (get?_empty k).symm

theorem delete_delete_same (m : M V) (i : K) :
    delete (delete m i) i = delete m i := by
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_delete_same]
  · simp [get?_delete_ne _ _ _ hij]

theorem delete_delete_comm (m : M V) (i j : K) :
    delete (delete m i) j = delete (delete m j) i := by
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k <;> simp [get?_delete, *]

theorem insert_insert_same (m : M V) (i : K) (x y : V) :
    insert (insert m i x) i y = insert m i y := by
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    rw [get?_insert_same, get?_insert_same]
  · rw [get?_insert_ne _ _ _ _ hij, get?_insert_ne _ _ _ _ hij, get?_insert_ne _ _ _ _ hij]

theorem insert_delete (m : M V) (i : K) (x : V) :
    insert (delete m i) i x = insert m i x := by
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    rw [get?_insert_same, get?_insert_same]
  · rw [get?_insert_ne _ _ _ _ hij, get?_delete_ne _ _ _ hij, get?_insert_ne _ _ _ _ hij]

theorem insert_insert_comm (m : M V) (i j : K) (x y : V) :
    i ≠ j → insert (insert m i x) j y = insert (insert m j y) i x := by
  intro hij
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk; exact absurd rfl hij
  · subst hik; simp [get?_insert, hjk]
  · subst hjk; simp [get?_insert, hik]
  · simp [get?_insert, hik, hjk]

theorem delete_insert_of_ne (m : M V) (i j : K) (x : V) :
    i ≠ j → delete (insert m i x) j = insert (delete m j) i x := by
  intro hij
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik hjk; exact absurd rfl hij
  · subst hik; simp [get?_insert, get?_delete, hjk]
  · subst hjk; simp [get?_insert, get?_delete, hik]
  · simp [get?_insert, get?_delete, hik, hjk]

set_option  pp.notation false
theorem delete_empty_eq' (i : K) :
    delete (∅ : M V) i = ∅ := by
  apply ext (M := M) (K := K) (V := V)
  intro j
  by_cases h : i = j
  · rw [h, get?_delete_same]
    simp only [EmptyCollection.emptyCollection]
    rw [get?_empty]
  · rw [get?_delete_ne _ _ _ h]

theorem delete_of_get? (m : M V) (i : K) :
    get? m i = none → delete m i = m := by
  intro h
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_delete_same, h]
  · simp [get?_delete_ne _ _ _ hij]

theorem insert_get?' (m : M V) (i : K) (x : V) :
    get? m i = some x → insert m i x = m := by
  intro h
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  by_cases hij : i = j
  · subst hij
    simp [get?_insert_same, h]
  · simp [get?_insert_ne _ _ _ _ hij]

omit [DecidableEq K] [PartialMapLaws K M] in
theorem insert_empty (i : K) (x : V) :
    insert (∅ : M V) i x = {[i := x]} := rfl

theorem insert_ne_empty (m : M V) (i : K) (x : V) :
    insert m i x ≠ ∅ := by
  intro h
  have := eq_empty_iff (insert m i x) |>.mp h i
  simp [get?_insert_same] at this

theorem delete_subset_self (m : M V) (i : K) : delete m i ⊆ m := by
  intro k v h
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at h
  · simp [get?_delete_ne _ _ _ hik] at h
    exact h

theorem subset_insert (m : M V) (i : K) (x : V) :
    get? m i = none → m ⊆ insert m i x := by
  intro hi k v hk
  by_cases hik : i = k
  · subst hik
    simp [hi] at hk
  · simp [get?_insert_ne _ _ _ _ hik, hk]

theorem delete_subset_delete (m₁ m₂ : M V) (i : K) :
    m₁ ⊆ m₂ → delete m₁ i ⊆ delete m₂ i := by
  intro hsub k v hk
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at hk
  · simp [get?_delete_ne _ _ _ hik] at hk ⊢
    exact hsub k v hk

theorem insert_subset_insert (m₁ m₂ : M V) (i : K) (x : V) :
    m₁ ⊆ m₂ → insert m₁ i x ⊆ insert m₂ i x := by
  intro hsub k v hk
  by_cases hik : i = k
  · subst hik
    simp [get?_insert_same] at hk
    simp [get?_insert_same, hk]
  · simp [get?_insert_ne _ _ _ _ hik] at hk
    simp [get?_insert_ne _ _ _ _ hik]
    exact hsub k v hk

theorem singleton_ne_empty (i : K) (x : V) :
    {[i := x]} ≠ (∅ : M V) := insert_ne_empty ∅ i x

theorem delete_singleton_same (i : K) (x : V) :
    delete ({[i := x]} : M V) i = ∅ := by
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro j
  rw [get?_delete]
  split
  · next heq => exact (get?_empty j).symm
  · next hne =>
    have : get? ({[i := x]} : M V) j = none := get?_singleton_ne i j x hne
    rw [this]
    exact (get?_empty j).symm

theorem delete_singleton_of_ne (i j : K) (x : V) :
    i ≠ j → delete ({[j := x]} : M V) i = {[j := x]} := by
  intro hij
  apply PartialMapLaws.ext (M := M) (K := K) (V := V)
  intro k
  rw [get?_delete]
  split
  · next heq =>
    rw [heq] at hij
    rw [get?_singleton_ne j k x hij.symm]
  · next hne =>
    rfl

theorem forall_empty (P : K → V → Prop) : PartialMap.Forall P (∅ : M V) := by
  intro k v h
  have : get? (∅ : M V) k = none := get?_empty k
  rw [this] at h
  cases h

omit [DecidableEq K] [PartialMapLaws K M] in
theorem forall_mono (P Q : K → V → Prop) (m : M V) :
    PartialMap.Forall P m → (∀ k v, P k v → Q k v) → PartialMap.Forall Q m := by
  intro hp himpl k v hget
  apply himpl
  apply hp k v hget

theorem forall_insert_of_forall (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    PartialMap.Forall P (insert m i x) → P i x := by
  intro hfa
  apply hfa
  apply get?_insert_same m i x

theorem forall_of_forall_insert (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    get? m i = none → PartialMap.Forall P (insert m i x) → PartialMap.Forall P m := by
  intro hi hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [hi] at hget
  · apply hfa k v
    simp [get?_insert_ne _ _ _ _ hik, hget]

theorem forall_insert (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    P i x → PartialMap.Forall P m → PartialMap.Forall P (insert m i x) := by
  intro hpix hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [get?_insert_same] at hget
    rw [← hget]
    assumption
  · apply hfa
    simp [get?_insert_ne _ _ _ _ hik] at hget
    assumption

theorem forall_insert_iff (P : K → V → Prop) (m : M V) (i : K) (x : V) :
    get? m i = none → (PartialMap.Forall P (insert m i x) ↔ P i x ∧ PartialMap.Forall P m) := by
  intro hi
  constructor
  · intro hfa
    exact ⟨forall_insert_of_forall P m i x hfa, forall_of_forall_insert P m i x hi hfa⟩
  · intro ⟨hpix, hfa⟩
    exact forall_insert P m i x hpix hfa

theorem forall_singleton (P : K → V → Prop) (i : K) (x : V) :
    PartialMap.Forall P ({[i := x]} : M V) ↔ P i x := by
  constructor
  · intro hfa
    apply hfa i x (get?_singleton_same i x)
  · intro hpix k v hget
    simp [get?_singleton] at hget
    obtain ⟨rfl, rfl⟩ := hget
    exact hpix

theorem forall_delete (P : K → V → Prop) (m : M V) (i : K) :
    PartialMap.Forall P m → PartialMap.Forall P (delete m i) := by
  intro hfa k v hget
  by_cases hik : i = k
  · subst hik
    rw [get?_delete_same] at hget
    cases hget
  · rw [get?_delete_ne _ _ _ hik] at hget
    exact hfa k v hget

omit [DecidableEq K] [PartialMapLaws K M] in
theorem disjoint_iff (m₁ m₂ : M V) :
    m₁ ##ₘ m₂ ↔ ∀ k, get? m₁ k = none ∨ get? m₂ k = none := by
  constructor
  · intro hdisj k
    by_cases h1 : (get? m₁ k).isSome
    · by_cases h2 : (get? m₂ k).isSome
      · exact absurd ⟨h1, h2⟩ (hdisj k)
      · simp only [Option.not_isSome_iff_eq_none] at h2; right; assumption
    · simp only [Option.not_isSome_iff_eq_none] at h1; left; assumption
  · intro h k ⟨hs1, hs2⟩
    cases h k with
    | inl h1 => simp [h1] at hs1
    | inr h2 => simp [h2] at hs2

theorem disjoint_insert_left (m₁ m₂ : M V) (i : K) (x : V) :
    get? m₂ i = none →
    m₁ ##ₘ m₂ →
    insert m₁ i x ##ₘ m₂ := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [get?_insert_ne _ _ _ _ hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_insert_right (m₁ m₂ : M V) (i : K) (x : V) :
    get? m₁ i = none →
    m₁ ##ₘ m₂ →
    m₁ ##ₘ insert m₂ i x := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [get?_insert_ne _ _ _ _ hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_delete_left (m₁ m₂ : M V) (i : K) :
    m₁ ##ₘ m₂ → delete m₁ i ##ₘ m₂ := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at hs1
  · simp [get?_delete_ne _ _ _ hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_delete_right (m₁ m₂ : M V) (i : K) :
    m₁ ##ₘ m₂ → m₁ ##ₘ delete m₂ i := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_same] at hs2
  · simp [get?_delete_ne _ _ _ hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_singleton_left (m : M V) (i : K) (x : V) :
    get? m i = none → {[i := x]} ##ₘ m := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [PartialMap.singleton, get?_insert_ne _ _ _ _ hik, get?_empty] at hs1

theorem disjoint_singleton_right (m : M V) (i : K) (x : V) :
    get? m i = none → m ##ₘ {[i := x]} := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [PartialMap.singleton, get?_insert_ne _ _ _ _ hik, get?_empty] at hs2

end PartialMapLaws

namespace PartialMap

variable {K : Type v} {M : Type u → _} [PartialMap K M]

/-- Submap is reflexive. -/
theorem subset_refl (m : M V) : m ⊆ m := fun _ _ h => h

/-- Submap is transitive. -/
theorem subset_trans {m₁ m₂ m₃ : M V} (h₁ : m₁ ⊆ m₂) (h₂ : m₂ ⊆ m₃) : m₁ ⊆ m₃ :=
  fun k v hm₁ => h₂ k v (h₁ k v hm₁)

/-- Disjointness is symmetric. -/
theorem disjoint_comm {m₁ m₂ : M V} (h : disjoint m₁ m₂) : disjoint m₂ m₁ :=
  fun k ⟨h₂, h₁⟩ => h k ⟨h₁, h₂⟩

theorem disjoint_empty_right [DecidableEq K] [PartialMapLaws K M] (m : M V) :
    m ##ₘ (∅ : M V) :=
  disjoint_comm (PartialMapLaws.disjoint_empty_left (K := K) m)

end PartialMap

end Iris.Std
