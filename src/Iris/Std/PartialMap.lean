/-
Copyright (c) 2026 Zongyuan Liu, Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Markus de Medeiros
-/

import Iris.Std.List

/-! ## Partial Maps

This file defines the base abstraction for partial maps (maps from keys to optional values).
Both `FiniteMap` and `Heap` extend this base interface.

The type `M` represents a partial map from keys of type `K` to values of type `V`.

## Implementation Note

This class does not re-use the GetElem? class from the standard library, because
of the validity predicate `valid`.

Additionally, this class is only defined for containers which can hold elements of
any given type (ie. containers of the type `Type _ → Type _`). The reason for this is
that the resource algebra cosntruction only applies to these types anyways.

The PartialMap interface does not require that the representation of a partial map
be unique, ie. all constructions reason extensionally about the get? function rather
than intensionally about map equalities. PartialMaps are free to be non-uniquely represented.
-/
namespace Iris.Std

/-- Base typeclass for partial maps: maps from keys `K` to optional values `V`. -/
class PartialMap (M : Type _ → Type _) (K : outParam (Type _)) where
  get? : M V → K → Option V
  insert : M V → K → V → M V
  delete : M V → K → M V
  empty : M V
export PartialMap (get? insert delete empty)

namespace PartialMap

variable {K V M} [PartialMap M K]

instance : EmptyCollection (M V) := ⟨PartialMap.empty⟩

/-- Singleton map containing exactly one key-value pair. -/
def singleton (k : K) (v : V) : M V := insert empty k v

/-- Two maps have disjoint domains. -/
def disjoint (m₁ m₂ : M V) : Prop := ∀ k, ¬((get? m₁ k).isSome ∧ (get? m₂ k).isSome)

/-- Submap relation: `m₁` is a submap of `m₂` if every key-value pair in `m₁` is also in `m₂`. -/
def submap (m₁ m₂ : M V) : Prop := ∀ k v, get? m₁ k = some v → get? m₂ k = some v

instance : HasSubset (M V) := ⟨submap⟩

/-- Membership: a key is in the map if it has a value. -/
def mem (m : M V) (k : K) : Prop := (get? m k).isSome

instance : Membership K (M V) := ⟨fun m k => (get? m k).isSome⟩

/-- Universal quantification over map entries. -/
def all (P : K → V → Prop) (m : M V) : Prop :=
  ∀ k v, get? m k = some v → P k v

/-- Two PartalMaps are pointwise equivalent. -/
@[simp] def equiv (m1 m2 : M V) : Prop := ∀ k, get? m1 k = get? m2 k

instance instEquivTrans : Trans equiv (@equiv K V M _) equiv := ⟨by simp_all⟩

scoped syntax term " ≡ₘ " term : term
scoped macro_rules
  | `($m₁ ≡ₘ $m₂) => `(PartialMap.equiv $m₁ $m₂)

end PartialMap

/-- Iris notation for singleton map: `{[k := v]}` -/
scoped syntax "{[" term " := " term "]}" : term
scoped macro_rules
  | `({[$k := $v]}) => `(PartialMap.singleton $k $v)

/-- Iris notation for map disjointness: `m₁ ##ₘ m₂` -/
scoped infix:50 " ##ₘ " => PartialMap.disjoint

/-- Laws that a partial map implementation must satisfy. -/
class LawfulPartialMap (M : Type _ → Type _) (K : outParam (Type _)) [PartialMap M K] where
  get?_empty k : get? (empty : M V) k = none
  get?_insert_eq {m : M V} {k k' v} : k = k' → get? (insert m k v) k' = some v
  get?_insert_ne {m : M V} {k k' v} : k ≠ k' → get? (insert m k v) k' = get? m k'
  get?_delete_eq {m : M V} {k k'} : k = k' → get? (delete m k) k' = none
  get?_delete_ne {m : M V} {k k'} : k ≠ k' → get? (delete m k) k' = get? m k'
export LawfulPartialMap (get?_empty get?_insert_eq get?_insert_ne get?_delete_eq get?_delete_ne)

namespace PartialMap

variable {K : Type v} {M : Type u → _} [PartialMap M K]

/-- Submap is reflexive. -/
theorem subset_refl (m : M V) : m ⊆ m := fun _ _ h => h

/-- Submap is transitive. -/
theorem subset_trans {m₁ m₂ m₃ : M V} (h₁ : m₁ ⊆ m₂) (h₂ : m₂ ⊆ m₃) : m₁ ⊆ m₃ :=
  fun k v hm₁ => h₂ k v (h₁ k v hm₁)

/-- Disjointness is symmetric. -/
theorem disjoint_comm {m₁ m₂ : M V} (h : disjoint m₁ m₂) : disjoint m₂ m₁ :=
  fun k ⟨h₂, h₁⟩ => h k ⟨h₁, h₂⟩

theorem forall_mono (P Q : K → V → Prop) {m : M V} :
    PartialMap.all P m → (∀ k v, P k v → Q k v) → PartialMap.all Q m :=
  fun hp himpl k v hget => himpl k v (hp k v hget)

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

end PartialMap

class ExtensionalPartialMap (M : Type _ → Type _) (K : outParam (Type _)) extends PartialMap M K where
  equiv_iff_eq {m₁ m₂ : M V} : PartialMap.equiv m₁ m₂ ↔ m₁ = m₂

namespace LawfulPartialMap

open PartialMap

variable {K V : Type _} {M : Type _ → Type _}
variable [PartialMap M K] [LawfulPartialMap M K]

theorem get?_insert [DecidableEq K] {m : M V} {k k' : K} {v : V} :
    get? (insert m k v) k' = if k = k' then some v else get? m k' := by
  split <;> rename_i h
  · exact get?_insert_eq h
  · exact get?_insert_ne h

theorem get?_delete [DecidableEq K] {m : M V} {k k' : K} :
    get? (delete m k) k' = if k = k' then none else get? m k' := by
  split <;> rename_i h
  · exact get?_delete_eq h
  · exact get?_delete_ne h

theorem get?_insert_delete_same {m : M V} {k k' : K} {v : V} :
    get? (insert (delete m k) k v) k' = get? (insert m k v) k' := by
  by_cases h : k = k'
  · simp [h, get?_insert_eq]
  · simp [get?_insert_ne h, get?_delete_ne h]

theorem get?_singleton_eq {k k' : K} {v : V} (h : k = k') : get? ({[k := v]} : M V) k' = some v := by
  simp [PartialMap.singleton, get?_insert_eq h]

theorem get?_singleton_ne {k k' : K} {v : V} (h : k ≠ k') : get? ({[k := v]} : M V) k' = none := by
  simp [PartialMap.singleton, get?_insert_ne h, get?_empty]

theorem get?_singleton [DecidableEq K] {k k' : K} {v : V} :
    get? ({[k := v]} : M V) k' = if k = k' then some v else none := by
  split <;> rename_i h
  · exact get?_singleton_eq h
  · exact get?_singleton_ne h

/-- Value at a key after insert must equal the inserted value. -/
theorem get?_insert_rev {m : M V} {i : K} {x y : V} :
    get? (insert m i x) i = some y → x = y := by
  simp [get?_insert_eq rfl]

theorem empty_subset (m : M V) : (∅ : M V) ⊆ m := by
  intro k v H
  simp [show get? (∅ : M V) k = none from get?_empty (M := M) k] at H

theorem disjoint_empty_left (m : M V) : (∅ : M V) ##ₘ m := by
  intro k ⟨h₁, _⟩
  simp [show get? (∅ : M V) k = none from get?_empty k] at h₁

theorem disjoint_empty_right (m : M V) : m ##ₘ (∅ : M V) := by
  intro k ⟨_, h₂⟩
  simp [show get? (∅ : M V) k = none from get?_empty k] at h₂

open Classical in
theorem get?_insert_some_iff {m : M V} {i j : K} {x y : V} :
    get? (insert m i x) j = some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ get? m j = some y) := by
  rw [get?_insert]; split <;> simp_all

open Classical in
theorem get?_insert_none_iff {m : M V} {i j : K} {x : V} :
    get? (insert m i x) j = none ↔ get? m j = none ∧ i ≠ j := by
  rw [get?_insert]; split <;> simp_all

open Classical in
theorem get?_delete_some_iff {m : M V} {i j : K} {y : V} :
    get? (delete m i) j = some y ↔ i ≠ j ∧ get? m j = some y := by
  rw [get?_delete]; split <;> simp_all

open Classical in
theorem get?_delete_none_iff {m : M V} {i j : K} :
    get? (delete m i) j = none ↔ i = j ∨ get? m j = none := by
  rw [get?_delete]; split <;> simp_all

theorem insert_delete_cancel {m : M V} {i : K} {v : V} (H : get? m i = some v) :
    insert (delete m i) i v ≡ₘ m := by
  intros j
  by_cases h : i = j
  · rw [get?_insert_eq h, ← H, h]
  · rw [get?_insert_ne h, get?_delete_ne h]

theorem delete_insert_cancel {m : M V} {i : K} {x : V} (H : get? m i = none) :
    delete (insert m i x) i ≡ₘ m := by
  intro j
  by_cases h : i = j
  · rw [get?_delete_eq h, ← H, h]
  · rw [get?_delete_ne h, get?_insert_ne h]

theorem eq_empty_iff {m : M V} : (m ≡ₘ ∅) ↔ ∀ k, get? m k = none :=
  ⟨fun h k => (h k) ▸ get?_empty k, fun h k => (h k) ▸ (get?_empty k).symm⟩

theorem delete_delete {m : M V} {i : K} :
    delete (delete m i) i ≡ₘ delete m i := by
  intro j
  by_cases h : i = j
  · rw [get?_delete_eq h, get?_delete_eq h]
  · rw [get?_delete_ne h]

theorem delete_delete_comm {m : M V} {i j : K} :
    delete (delete m i) j ≡ₘ delete (delete m j) i := by
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · rw [get?_delete_eq hik, get?_delete_eq hjk]
  · rw [get?_delete_eq hik, get?_delete_ne hjk, get?_delete_eq hik]
  · rw [get?_delete_ne hik, get?_delete_eq hjk, get?_delete_eq hjk]
  · rw [get?_delete_ne hik, get?_delete_ne hjk, get?_delete_ne hik, get?_delete_ne hjk]

theorem insert_insert_same {m : M V} {i : K} {x y : V} :
    insert (insert m i x) i y ≡ₘ insert m i y := by
  intro j
  by_cases h : i = j
  · rw [get?_insert_eq h, get?_insert_eq h]
  · rw [get?_insert_ne h, get?_insert_ne h, get?_insert_ne h]

theorem insert_delete {m : M V} {i : K} {x : V} :
    insert (delete m i) i x ≡ₘ insert m i x := by
  intro j
  by_cases h : i = j
  · rw [get?_insert_eq h, get?_insert_eq h]
  · rw [get?_insert_ne h, get?_delete_ne h, get?_insert_ne h]

theorem insert_insert_comm {m : M V} {i j : K} {x y : V} (H : i ≠ j) :
    insert (insert m i x) j y ≡ₘ insert (insert m j y) i x := by
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · rw [hik, hjk] at H; exact False.elim (H rfl)
  · rw [get?_insert_ne hjk, get?_insert_eq hik, get?_insert_eq hik]
  · rw [get?_insert_eq hjk, get?_insert_ne hik, get?_insert_eq hjk]
  · rw [get?_insert_ne hjk, get?_insert_ne hik, get?_insert_ne hik, get?_insert_ne hjk]

theorem delete_insert_of_ne {m : M V} {i j : K} {x : V} (H : i ≠ j) :
    delete (insert m i x) j ≡ₘ insert (delete m j) i x := by
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · rw [hik, hjk] at H; exact False.elim (H rfl)
  · rw [get?_insert_eq hik, get?_delete_ne hjk, get?_insert_eq hik]
  · rw [get?_insert_ne hik, get?_delete_eq hjk, get?_delete_eq hjk]
  · rw [get?_delete_ne hjk, get?_insert_ne hik, get?_insert_ne hik, get?_delete_ne hjk]

theorem delete_empty {i : K} : delete (empty : M V) i ≡ₘ empty := by
  intro j
  by_cases h : i = j
  · rw [get?_delete_eq h, get?_empty]
  · rw [get?_delete_ne h, get?_empty]

theorem delete_of_get? {m : M V} {i : K} (H : get? m i = none) : delete m i ≡ₘ m := by
  intro j
  by_cases h : i = j
  · rw [get?_delete_eq h, ← H, h]
  · rw [get?_delete_ne h]

theorem insert_get? {m : M V} {i : K} {x : V} (H : get? m i = some x) :
    insert m i x ≡ₘ m := by
  intro j
  by_cases h : i = j
  · rw [get?_insert_eq h, ← H, h]
  · rw [get?_insert_ne h]

theorem insert_ne_empty {m : M V} {i : K} {x : V} : ¬(insert m i x ≡ₘ empty) := by
  intro h
  have : get? (insert m i x) i = none := (h i) ▸ get?_empty i
  rw [get?_insert_eq rfl] at this
  cases this

theorem delete_subset_self {m : M V} {i : K} : delete m i ⊆ m := by
  intro k v h
  by_cases hik : i = k
  · rw [get?_delete_eq hik] at h
    cases h
  · rw [get?_delete_ne hik] at h
    exact h

theorem subset_insert {m : M V} {i : K} {x : V} (H : get? m i = none) :
    m ⊆ insert m i x := by
  intro k v hk
  by_cases h : i = k
  · rw [h] at H
    rw [H] at hk
    cases hk
  · rw [get?_insert_ne h]
    exact hk

theorem delete_subset_delete {m₁ m₂ : M V} {i : K} (H : m₁ ⊆ m₂) : delete m₁ i ⊆ delete m₂ i := by
  intro k v hk
  by_cases h : i = k
  · rw [get?_delete_eq h] at hk
    cases hk
  · rw [get?_delete_ne h] at hk ⊢
    exact H k v hk

theorem insert_subset_insert {m₁ m₂ : M V} {i : K} {x : V} (H : m₁ ⊆ m₂) :
    insert m₁ i x ⊆ insert m₂ i x := by
  intro k v hk
  by_cases h : i = k
  · rw [get?_insert_eq h] at hk ⊢
    exact hk
  · rw [get?_insert_ne h] at hk ⊢
    exact H k v hk

theorem singleton_ne_empty {i : K} {x : V} : ¬({[i := x]} ≡ₘ (∅ : M V)) := insert_ne_empty

theorem delete_singleton_eq {i : K} {x : V} : delete ({[i := x]} : M V) i ≡ₘ empty := by
  intro j
  by_cases h : i = j
  · rw [get?_delete_eq h, get?_empty]
  · rw [get?_delete_ne h, get?_singleton_ne h, get?_empty]

theorem delete_singleton_ne {i j : K} {x : V} (H : i ≠ j) :
    delete ({[j := x]} : M V) i ≡ₘ {[j := x]} := by
  intro k
  by_cases h : i = k
  · rw [get?_delete_eq h, get?_singleton_ne (h ▸ H.symm)]
  · rw [get?_delete_ne h]

theorem forall_empty (P : K → V → Prop) : PartialMap.all P (empty : M V) := by
  intro k v h
  rw [get?_empty k] at h
  cases h

theorem forall_insert_of_forall (P : K → V → Prop) {m : M V} {i : K} {x : V} :
    PartialMap.all P (insert m i x) → P i x :=
  fun hfa => hfa _ _ (get?_insert_eq rfl)

theorem forall_of_forall_insert (P : K → V → Prop) {m : M V} {i : K} {x : V} :
    get? m i = none → PartialMap.all P (insert m i x) → PartialMap.all P m := by
  intro hi hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [hi] at hget
  · apply hfa k v
    simp [get?_insert_ne hik, hget]

theorem forall_insert (P : K → V → Prop) {m : M V} {i : K} {x : V} :
    P i x → PartialMap.all P m → PartialMap.all P (insert m i x) := by
  intro hpix hfa k v hget
  by_cases hik : i = k
  · subst hik
    simp [get?_insert_eq] at hget
    rw [← hget]
    assumption
  · apply hfa
    simp [get?_insert_ne hik] at hget
    assumption

theorem forall_insert_iff (P : K → V → Prop) {m : M V} {i : K} {x : V} (hi : get? m i = none) :
    (PartialMap.all P (insert m i x) ↔ P i x ∧ PartialMap.all P m) :=
  ⟨fun hfa => ⟨forall_insert_of_forall P hfa, forall_of_forall_insert P hi hfa⟩,
   fun ⟨hpix, hfa⟩ => forall_insert P hpix hfa⟩

theorem forall_singleton (P : K → V → Prop) {i : K} {x : V} :
    PartialMap.all P ({[i := x]} : M V) ↔ P i x := by
  constructor
  · exact fun hfa => hfa i x (get?_singleton_eq rfl)
  · intro hpix k v hget
    by_cases h : i = k
    · simp [get?_singleton_eq h] at hget
      exact hget ▸ h ▸ hpix
    · simp [get?_singleton_ne h] at hget

theorem forall_delete (P : K → V → Prop) {m : M V} {i : K} :
    PartialMap.all P m → PartialMap.all P (delete m i) := by
  intro hfa k v hget
  by_cases hik : i = k
  · simp [get?_delete_eq hik] at hget
  · rw [get?_delete_ne hik] at hget
    exact hfa k v hget

theorem disjoint_insert_left {m₁ m₂ : M V} {i : K} {x : V} :
    get? m₂ i = none →
    m₁ ##ₘ m₂ →
    insert m₁ i x ##ₘ m₂ := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [get?_insert_ne hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_insert_right {m₁ m₂ : M V} {i : K} {x : V} :
    get? m₁ i = none →
    m₁ ##ₘ m₂ →
    m₁ ##ₘ insert m₂ i x := by
  intro hi hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [get?_insert_ne hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_delete_left {m₁ m₂ : M V} {i : K} :
    m₁ ##ₘ m₂ → delete m₁ i ##ₘ m₂ := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_eq] at hs1
  · simp [get?_delete_ne hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_delete_right {m₁ m₂ : M V} {i : K} :
    m₁ ##ₘ m₂ → m₁ ##ₘ delete m₂ i := by
  intro hdisj k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_eq] at hs2
  · simp [get?_delete_ne hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_singleton_left {m : M V} {i : K} {x : V} :
    get? m i = none → {[i := x]} ##ₘ m := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [PartialMap.singleton, get?_insert_ne hik, get?_empty] at hs1

theorem disjoint_singleton_right {m : M V} {i : K} {x : V} :
    get? m i = none → m ##ₘ {[i := x]} := by
  intro hi k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [PartialMap.singleton, get?_insert_ne hik, get?_empty] at hs2

end LawfulPartialMap

end Iris.Std
