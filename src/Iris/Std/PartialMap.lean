import Batteries.Data.List.Perm
import Iris.Std.FromMathlib

/-
Copyright (c) 2026 Zongyuan Liu, Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Markus de Medeiros
-/

/-! ## Partial Maps

This file defines the base abstraction for partial maps (maps from keys to optional values).
Both `FiniteMap` and `Heap` extend this base interface.

The type `M` represents a partial map from keys of type `K` to values of type `V`.

## Implementation Note

This class does not re-use the GetElem? class from the standard library, because
of the validity predicate `valid`.

Additionally, this class is only defined for containers which can hold elements of
any given type (ie. containers of the type `Type _ → Type _`). The reason for this
is that the resource algebra construction only applies to these types anyways.

The PartialMap interface does not require that the representation of a partial map
be unique, ie. all constructions reason extensionally about the get? function rather
than intensionally about map equalities. PartialMaps are free to be non-uniquely
represented.
-/
namespace Iris.Std

/-- Base typeclass for partial maps: maps from keys `K` to optional values `V`. -/
class PartialMap (M : Type _ → Type _) (K : outParam (Type _)) where
  get? : M V → K → Option V
  insert : M V → K → V → M V
  delete : M V → K → M V
  empty : M V
  bindAlter : (K → V → Option V') → M V → M V'
  merge (op : K → V → V → V) : M V → M V → M V
export PartialMap (get? insert delete empty bindAlter merge)

/-- A FiniteMap is a PartialMap with a toList operation. Like in Stdpp, the order in
which the elements are passed into the list is unspecified. -/
class FiniteMap M K extends PartialMap M K where
  toList : M V → List (K × V)
export FiniteMap (toList)

/-- RepFunMap: The map T is capable of representing all partial functions out of
K. -/
class RepFunMap (T : Type _ → Type _) (K : outParam (Type _)) [PartialMap T K] where
  of_fun : (K → Option V) → T V
  get_of_fun (f : K → Option V) (k : K) : get? (of_fun f) k = f k
export RepFunMap (of_fun get_of_fun)

/-- IsoFunStore: The map T is isomorphic to the type of functions out of `K`. In
other words, equality of T is the same as equality of functions, so the CMRA on
these partial functions is leibniz. -/
class IsoFunMap (T : Type _ → Type _) (K : outParam (Type _)) [PartialMap T K]
  extends RepFunMap T K where
  of_fun_get {t : T V} : of_fun (get? t) = t
export IsoFunMap (of_fun_get)

@[ext]
theorem IsoFunMap.ext [PartialMap T K] [IsoFunMap T K] {t1 t2 : T V}
    (h : ∀ k, get? t1 k = get? t2 k) : t1 = t2 := by
  rw [← of_fun_get (t := t1), ← of_fun_get (t := t2)]
  congr 1
  funext k
  exact h k

/-- An AllocHeap is a heap which can allocate elements under some condition. -/
class Heap (M : Type _ → Type _) (K : outParam (Type _)) extends PartialMap M K where
  notFull : M V → Prop
  fresh {m : M V} : notFull m → K
  get?_fresh {m : M V} {H : notFull m} : get? m (fresh H) = none
export Heap (notFull fresh get?_fresh)

/-- An UnboundedHeap is a heap which can allocate an unbounded number of elements starting at empty. -/
class UnboundedHeap (M : Type _ → Type _) (K : outParam (Type _)) extends Heap M K where
  notFull_empty : notFull (empty : M V)
  notFull_insert_fresh {m : M V} {H : notFull m} : notFull (insert m (fresh H) v)
export UnboundedHeap (notFull_empty notFull_insert_fresh)

namespace PartialMap

variable {K} {V : Type u} {M} [PartialMap M K]

/-- The empty partial map can be written as `∅`. -/
instance : EmptyCollection (M V) := ⟨PartialMap.empty⟩

/-- Singleton map containing exactly one key-value pair. -/
def singleton (k : K) (v : V) : M V := insert empty k v

/-- Two maps have disjoint domains. -/
def disjoint (m₁ m₂ : M V) : Prop := ∀ k, ¬((get? m₁ k).isSome ∧ (get? m₂ k).isSome)

/-- Submap relation: `m₁` is a submap of `m₂` if every key-value pair in `m₁` is also in `m₂`. -/
def submap (m₁ m₂ : M V) : Prop := ∀ k v, get? m₁ k = some v → get? m₂ k = some v

/-- Construct a map from a list of key-value pairs. Later entries override earlier ones. -/
def ofList (l : List (K × V)) : M V :=
  l.foldr (fun (k, v) acc => insert acc k v) empty

/-- Partial maps support the subset relation `⊆` via the submap relation. -/
instance : HasSubset (M V) := ⟨submap⟩

/-- Membership: a key is in the map if it has a value. -/
def mem (m : M V) (k : K) : Prop := (get? m k).isSome

/-- Keys can be tested for membership in partial maps using `∈`. -/
instance : Membership K (M V) := ⟨fun m k => (get? m k).isSome⟩

/-- Universal quantification over map entries. -/
def all (P : K → V → Prop) (m : M V) : Prop :=
  ∀ k v, get? m k = some v → P k v

/-- The domain of a heap is the set of keys that map to .some values. -/
def dom (m : M V) : K → Prop := fun k => (get? m k).isSome

-- Should this be part of the typeclass, or should we use this derived one?
@[simp] def union : M V → M V → M V := merge (fun _ v _ => v)

/-- Partial maps support the union operation `∪`, with left-biased merge. -/
instance : Union (M V) := ⟨union⟩

/-- Map a function over all values in the map. -/
def map (f : V → V') : M V → M V' :=
  bindAlter (fun _ v => some (f v))

/-- Filter and map: apply a function that can optionally drop entries. -/
def filterMap (f : V → Option V) : M V → M V :=
  bindAlter (fun _ v => f v)

/-- Filter entries by a predicate on key-value pairs. -/
def filter (φ : K → V → Bool) : M V → M V :=
  bindAlter (fun k v => if φ k v then some v else none)

/-- Difference: remove all keys in `m₂` from `m₁`. -/
def difference (m₁ m₂ : M V) : M V :=
  bindAlter (fun k v => if (get? m₂ k).isSome then none else some v) m₁

def zipWith (f : V → V' → V'') (m₁ : M V) (m₂ : M V') : M V'' :=
  bindAlter (fun k v => (get? m₂ k).bind fun v' => some <| f v v') m₁

def zip {V' : Type u} (m₁ : M V) (m₂ : M V') : M (V × V') :=
  zipWith (fun x y => (x, y)) m₁ m₂

/-- Partial maps support the set difference operation `\` via difference. -/
instance : SDiff (M V) := ⟨difference⟩

/-- Two PartialMaps are pointwise equivalent. -/
@[simp] def equiv (m1 m2 : M V) : Prop := ∀ k, get? m1 k = get? m2 k

/-- Pointwise equivalence is transitive. -/
instance instEquivTrans : Trans equiv (@equiv K V M _) equiv := ⟨by simp_all⟩

scoped infix:50 " ≡ₘ " => PartialMap.equiv

/-- Iris notation for singleton map: `{[k := v]}` -/
scoped syntax "{[" term " := " term "]}" : term
scoped macro_rules
  | `({[$k := $v]}) => `(PartialMap.singleton $k $v)

/-- Iris notation for map disjointness: `m₁ ##ₘ m₂` -/
scoped infix:50 " ##ₘ " => PartialMap.disjoint

/-- Submap is reflexive. -/
theorem subset_refl (m : M V) : m ⊆ m := fun _ _ h => h

/-- Submap is transitive. -/
theorem subset_trans {m₁ m₂ m₃ : M V} (h₁ : m₁ ⊆ m₂) (h₂ : m₂ ⊆ m₃) : m₁ ⊆ m₃ :=
  fun k v hm₁ => h₂ k v (h₁ k v hm₁)

/-- Disjointness is symmetric. -/
theorem disjoint_comm {m₁ m₂ : M V} (h : disjoint m₁ m₂) : disjoint m₂ m₁ :=
  fun k ⟨h₂, h₁⟩ => h k ⟨h₁, h₂⟩

theorem all_mono (P Q : K → V → Prop) {m : M V}
    (hp : PartialMap.all P m) (himpl : ∀ k v, P k v → Q k v) :
    PartialMap.all Q m :=
  fun k v hget => himpl k v (hp k v hget)

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

/-- An association list has no duplicate keys -/
def NoDupKeys (L : List (K × A)) : Prop := L.map (·.1) |>.Nodup

class ExtensionalPartialMap (M : Type _ → Type _) (K : outParam (Type _))
    extends PartialMap M K where
  equiv_iff_eq {m₁ m₂ : M V} : PartialMap.equiv m₁ m₂ ↔ m₁ = m₂

/-- Laws that a partial map implementation must satisfy. -/
class LawfulPartialMap (M : Type _ → Type _) (K : outParam (Type _))
    extends PartialMap M K where
  get?_empty k : get? (empty : M V) k = none
  get?_insert_eq {m : M V} {k k' v} : k = k' → get? (insert m k v) k' = some v
  get?_insert_ne {m : M V} {k k' v} : k ≠ k' → get? (insert m k v) k' = get? m k'
  get?_delete_eq {m : M V} {k k'} : k = k' → get? (delete m k) k' = none
  get?_delete_ne {m : M V} {k k'} : k ≠ k' → get? (delete m k) k' = get? m k'
  get?_bindAlter {m : M V} {f : K → V → Option V'} :
      get? (bindAlter f m) k = (get? m k).bind (f k)
  get?_merge :
      get? (merge op m₁ m₂) k = Option.merge (op k) (get? m₁ k) (get? m₂ k)
export LawfulPartialMap (get?_empty get?_insert_eq get?_insert_ne get?_delete_eq
  get?_delete_ne get?_bindAlter get?_merge)

class LawfulFiniteMap M K extends LawfulPartialMap M K, FiniteMap M K where
  toList_empty : toList (∅ : M V) = []
  toList_noDupKeys : NoDupKeys (toList (m : M V))
  toList_get : (k, v) ∈ toList m ↔ get? m k = some v
export LawfulFiniteMap (toList_empty toList_noDupKeys toList_get)

namespace FiniteMap

variable {K V : Type _} {M : Type _ → Type _} [FiniteMap M K]

def mapFold {A : Type _} (f : K → V → A → A) (a : A) (m : M V) : A :=
  List.foldl (fun a' ⟨k, v⟩ => f k v a') a (toList (K := K) m)

end FiniteMap

namespace LawfulPartialMap

open PartialMap

variable {K V : Type _} {M : Type _ → Type _} [LawfulPartialMap M K]

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

theorem get?_singleton_eq {k k' : K} {v : V} (h : k = k') :
  get? ({[k := v]} : M V) k' = some v := by
  simp [PartialMap.singleton, get?_insert_eq h]

theorem get?_singleton_ne {k k' : K} {v : V} (h : k ≠ k') :
  get? ({[k := v]} : M V) k' = none := by
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
  intro k v h
  simp [show get? (∅ : M V) k = none from get?_empty (M := M) k] at h

theorem disjoint_empty_left (m : M V) : (∅ : M V) ##ₘ m := by
  intro k ⟨h₁, _⟩
  simp [show get? (∅ : M V) k = none from get?_empty k] at h₁

theorem disjoint_empty_right (m : M V) : m ##ₘ (∅ : M V) := by
  intro k ⟨_, h₂⟩
  simp [show get? (∅ : M V) k = none from get?_empty k] at h₂

theorem get?_insert_some_iff [DecidableEq K] {m : M V} {i j : K} {x y : V} :
    get? (insert m i x) j = some y
    ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ get? m j = some y) := by
  rw [get?_insert]; split <;> simp_all

theorem get?_insert_none_iff [DecidableEq K] {m : M V} {i j : K} {x : V} :
    get? (insert m i x) j = none ↔ get? m j = none ∧ i ≠ j := by
  rw [get?_insert]; split <;> simp_all

theorem get?_delete_some_iff [DecidableEq K] {m : M V} {i j : K} {y : V} :
    get? (delete m i) j = some y ↔ i ≠ j ∧ get? m j = some y := by
  rw [get?_delete]; split <;> simp_all

theorem get?_delete_none_iff [DecidableEq K] {m : M V} {i j : K} :
    get? (delete m i) j = none ↔ i = j ∨ get? m j = none := by
  rw [get?_delete]; split <;> simp_all

theorem insert_delete_cancel {m : M V} {i : K} {v : V} (h : get? m i = some v) :
    insert (delete m i) i v ≡ₘ m := by
  intros j
  by_cases hij : i = j
  · rw [get?_insert_eq hij, ← h, hij]
  · rw [get?_insert_ne hij, get?_delete_ne hij]

theorem delete_insert_cancel {m : M V} {i : K} {x : V} (h : get? m i = none) :
    delete (insert m i x) i ≡ₘ m := by
  intro j
  by_cases hij : i = j
  · rw [get?_delete_eq hij, ← h, hij]
  · rw [get?_delete_ne hij, get?_insert_ne hij]

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

theorem insert_insert_comm {m : M V} {i j : K} {x y : V} (h : i ≠ j) :
    insert (insert m i x) j y ≡ₘ insert (insert m j y) i x := by
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · rw [hik, hjk] at h; exact False.elim (h rfl)
  · rw [get?_insert_ne hjk, get?_insert_eq hik, get?_insert_eq hik]
  · rw [get?_insert_eq hjk, get?_insert_ne hik, get?_insert_eq hjk]
  · rw [get?_insert_ne hjk, get?_insert_ne hik, get?_insert_ne hik, get?_insert_ne hjk]

theorem delete_insert_of_ne {m : M V} {i j : K} {x : V} (h : i ≠ j) :
    delete (insert m i x) j ≡ₘ insert (delete m j) i x := by
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k
  · rw [hik, hjk] at h; exact False.elim (h rfl)
  · rw [get?_insert_eq hik, get?_delete_ne hjk, get?_insert_eq hik]
  · rw [get?_insert_ne hik, get?_delete_eq hjk, get?_delete_eq hjk]
  · rw [get?_delete_ne hjk, get?_insert_ne hik, get?_insert_ne hik, get?_delete_ne hjk]

theorem delete_empty {i : K} : delete (empty : M V) i ≡ₘ empty := by
  intro j
  by_cases h : i = j
  · rw [get?_delete_eq h, get?_empty]
  · rw [get?_delete_ne h, get?_empty]

theorem delete_of_get? {m : M V} {i : K} (h : get? m i = none) : delete m i ≡ₘ m := by
  intro j
  by_cases hij : i = j
  · rw [get?_delete_eq hij, ← h, hij]
  · rw [get?_delete_ne hij]

theorem insert_get? {m : M V} {i : K} {x : V} (h : get? m i = some x) :
    insert m i x ≡ₘ m := by
  intro j
  by_cases hij : i = j
  · rw [get?_insert_eq hij, ← h, hij]
  · rw [get?_insert_ne hij]

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

theorem subset_insert {m : M V} {i : K} {x : V} (h : get? m i = none) :
    m ⊆ insert m i x := by
  intro k v hk
  by_cases hik : i = k
  · rw [hik] at h
    rw [h] at hk
    cases hk
  · rw [get?_insert_ne hik]
    exact hk

theorem delete_subset_delete {m₁ m₂ : M V} {i : K} (h : m₁ ⊆ m₂) :
  delete m₁ i ⊆ delete m₂ i := by
  intro k v hk
  by_cases hik : i = k
  · rw [get?_delete_eq hik] at hk
    cases hk
  · rw [get?_delete_ne hik] at hk ⊢
    exact h k v hk

theorem insert_subset_insert {m₁ m₂ : M V} {i : K} {x : V} (h : m₁ ⊆ m₂) :
    insert m₁ i x ⊆ insert m₂ i x := by
  intro k v hk
  by_cases hik : i = k
  · rw [get?_insert_eq hik] at hk ⊢
    exact hk
  · rw [get?_insert_ne hik] at hk ⊢
    exact h k v hk

theorem singleton_ne_empty {i : K} {x : V} : ¬({[i := x]} ≡ₘ (∅ : M V))
  := insert_ne_empty

theorem delete_singleton_eq {i : K} {x : V} :
  delete ({[i := x]} : M V) i ≡ₘ empty := by
  intro j
  by_cases h : i = j
  · rw [get?_delete_eq h, get?_empty]
  · rw [get?_delete_ne h, get?_singleton_ne h, get?_empty]

theorem delete_singleton_ne {i j : K} {x : V} (h : i ≠ j) :
    delete ({[j := x]} : M V) i ≡ₘ {[j := x]} := by
  intro k
  by_cases hik : i = k
  · rw [get?_delete_eq hik, get?_singleton_ne (hik ▸ h.symm)]
  · rw [get?_delete_ne hik]

theorem all_empty (P : K → V → Prop) : PartialMap.all P (empty : M V) := by
  intro k v h
  rw [get?_empty k] at h
  cases h

theorem all_insert_of_all (P : K → V → Prop) {m : M V} {i : K} {x : V}
    (h : PartialMap.all P (insert m i x)) : P i x :=
  h _ _ (get?_insert_eq rfl)

theorem all_of_all_insert (P : K → V → Prop) {m : M V} {i : K} {x : V}
    (hi : get? m i = none) (h : PartialMap.all P (insert m i x)) :
    PartialMap.all P m := by
  intro k v hget
  by_cases hik : i = k
  · subst hik
    simp [hi] at hget
  · apply h k v
    simp [get?_insert_ne hik, hget]

theorem all_insert (P : K → V → Prop) {m : M V} {i : K} {x : V}
    (hpix : P i x) (h : PartialMap.all P m) : PartialMap.all P (insert m i x) := by
  intro k v hget
  by_cases hik : i = k
  · subst hik
    simp [get?_insert_eq] at hget
    rw [← hget]
    assumption
  · apply h
    simp [get?_insert_ne hik] at hget
    assumption

theorem all_insert_iff (P : K → V → Prop) {m : M V} {i : K} {x : V}
    (hi : get? m i = none) :
    (PartialMap.all P (insert m i x) ↔ P i x ∧ PartialMap.all P m) :=
  ⟨fun h => ⟨all_insert_of_all P h, all_of_all_insert P hi h⟩,
   fun ⟨hpix, h⟩ => all_insert P hpix h⟩

theorem all_singleton (P : K → V → Prop) {i : K} {x : V} :
    PartialMap.all P ({[i := x]} : M V) ↔ P i x := by
  constructor
  · exact fun h => h i x (get?_singleton_eq rfl)
  · intro hpix k v hget
    by_cases h : i = k
    · simp [get?_singleton_eq h] at hget
      exact hget ▸ h ▸ hpix
    · simp [get?_singleton_ne h] at hget

theorem all_delete (P : K → V → Prop) {m : M V} {i : K}
    (h : PartialMap.all P m) : PartialMap.all P (delete m i) := by
  intro k v hget
  by_cases hik : i = k
  · simp [get?_delete_eq hik] at hget
  · rw [get?_delete_ne hik] at hget
    exact h k v hget

theorem disjoint_insert_left {m₁ m₂ : M V} {i : K} {x : V}
    (hi : get? m₂ i = none) (hdisj : m₁ ##ₘ m₂) : insert m₁ i x ##ₘ m₂ := by
  intro k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [get?_insert_ne hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_insert_right {m₁ m₂ : M V} {i : K} {x : V}
    (hi : get? m₁ i = none) (hdisj : m₁ ##ₘ m₂) : m₁ ##ₘ insert m₂ i x := by
  intro k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [get?_insert_ne hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_delete_left {m₁ m₂ : M V} {i : K}
    (hdisj : m₁ ##ₘ m₂) : delete m₁ i ##ₘ m₂ := by
  intro k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_eq] at hs1
  · simp [get?_delete_ne hik] at hs1
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_delete_right {m₁ m₂ : M V} {i : K}
    (hdisj : m₁ ##ₘ m₂) : m₁ ##ₘ delete m₂ i := by
  intro k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [get?_delete_eq] at hs2
  · simp [get?_delete_ne hik] at hs2
    exact hdisj k ⟨hs1, hs2⟩

theorem disjoint_singleton_left {m : M V} {i : K} {x : V}
    (hi : get? m i = none) : {[i := x]} ##ₘ m := by
  intro k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs2
  · simp [PartialMap.singleton, get?_insert_ne hik, get?_empty] at hs1

theorem disjoint_singleton_right {m : M V} {i : K} {x : V}
    (hi : get? m i = none) : m ##ₘ {[i := x]} := by
  intro k ⟨hs1, hs2⟩
  by_cases hik : i = k
  · subst hik
    simp [hi] at hs1
  · simp [PartialMap.singleton, get?_insert_ne hik, get?_empty] at hs2

theorem get?_insert_isSome [DecidableEq K] {m : M V} {i j : K} {x : V} :
    (get? (insert m i x) j).isSome ↔ i = j ∨ (i ≠ j ∧ (get? m j).isSome) := by
  rw [get?_insert]
  split <;> simp_all

theorem get?_delete_isSome [DecidableEq K] {m : M V} {i j : K} :
    (get? (delete m i) j).isSome ↔ i ≠ j ∧ (get? m j).isSome := by
  rw [get?_delete]
  split <;> simp_all

theorem get?_difference {m₁ m₂ : M V} {k : K} :
    get? (m₁ \ m₂) k = if (get? m₂ k).isSome then none else get? m₁ k := by
  simp only [SDiff.sdiff, PartialMap.difference, get?_bindAlter]
  cases hm2 : get? m₂ k <;> cases hm1 : get? m₁ k <;> simp

theorem disjoint_difference_right {m₁ m₂ : M V} :
    m₂ ##ₘ (m₁ \ m₂) := by
  intro k ⟨h_in_m2, h_in_diff⟩
  rw [get?_difference] at h_in_diff
  simp only [h_in_m2, ↓reduceIte] at h_in_diff
  cases h_in_diff

theorem union_difference_cancel {m₁ m₂ : M V} (h : m₂ ⊆ m₁) :
    union m₂ (m₁ \ m₂) ≡ₘ m₁ := by
  intro k
  simp only [PartialMap.union, get?_merge, get?_difference]
  cases hm2 : get? m₂ k with
  | none =>
    cases get? m₁ k <;> simp [Option.merge]
  | some v =>
    simp [Option.merge]
    exact (h k v hm2).symm

theorem get?_union {m₁ m₂ : M V} {k : K} :
    get? (union m₁ m₂) k = (get? m₁ k).orElse (fun _ => get? m₂ k) := by
  simp only [PartialMap.union, get?_merge]
  cases get? m₁ k <;> cases get? m₂ k <;> simp [Option.merge, Option.orElse]

theorem get?_union_none {m₁ m₂ : M V} {i : K} :
    get? (union m₁ m₂) i = none ↔ get? m₁ i = none ∧ get? m₂ i = none := by
  rw [get?_union]
  cases h1 : get? m₁ i <;> cases h2 : get? m₂ i <;> simp [Option.orElse]

theorem union_insert_left {m₁ m₂ : M V} {i : K} {x : V} :
    insert (union m₁ m₂) i x ≡ₘ union (insert m₁ i x) m₂ := by
  intro k
  by_cases hik : i = k
  · subst hik
    cases h : get? m₂ i <;> simp [get?_insert_eq rfl, PartialMap.union
                                , get?_merge, Option.merge, h]
  · simp [get?_insert_ne hik, PartialMap.union, get?_merge]

theorem get?_map {f : V → V'} {m : M V} {k : K} :
    get? (PartialMap.map f m) k = (get? m k).map f := by
  simp only [PartialMap.map, get?_bindAlter]
  cases get? m k <;> simp

theorem map_id {m : M V} :
    PartialMap.map id m ≡ₘ m := by
  intro k
  rw [get?_map]
  cases get? m k <;> simp

theorem get?_filterMap {f : V → Option V} {m : M V} {k : K} :
    get? (filterMap f m) k = (get? m k).bind f := by
  simp [filterMap, get?_bindAlter]

theorem get?_filter {φ : K → V → Bool} {m : M V} {k : K} :
    get? (filter φ m) k
    = (get? m k).bind (fun v => if φ k v then some v else none) := by
  simp [Option.bind, filter, get?_bindAlter]

theorem get?_zipWith {f : V → V' → V''} {m₁ : M V} {m₂ : M V'} {k : K} :
    get? (zipWith f m₁ m₂) k
    = (get? m₁ k).bind fun v₁ => (get? m₂ k).map fun v₂ => f v₁ v₂ := by
  simp [zipWith, get?_bindAlter]
  cases h1 : get? m₁ k <;> cases h2 : get? m₂ k <;> simp [Option.bind]

theorem get?_zip {m₁ : M V} {m₂ : M V'} {k : K} :
    get? (zip m₁ m₂) k = (get? m₁ k).bind fun v₁ => (get? m₂ k).map fun v₂ => (v₁, v₂) := by
  simp [zip, zipWith, get?_bindAlter]
  cases h1 : get? m₁ k <;> cases h2 : get? m₂ k <;> simp [Option.bind]

theorem map_zipWith_right {f : V → V' → V''} {g : V''' → V'}
    {m₁ : M V} {m₂ : M V'''} :
    PartialMap.map (fun (v, w) => f v (g w)) (zip m₁ m₂) ≡ₘ
      zipWith f m₁ (PartialMap.map g m₂) := by
  intro k
  simp [get?_map, get?_zip, get?_zipWith]
  cases get? m₁ k <;> cases get? m₂ k <;> simp [Option.bind, Option.map]

theorem map_zipWith_left {f : V → V' → V''} {g : V''' → V}
    {m₁ : M V'''} {m₂ : M V'} :
    PartialMap.map (fun (w, v) => f (g w) v) (zip m₁ m₂) ≡ₘ
      zipWith f (PartialMap.map g m₁) m₂ := by
  intro k
  simp [get?_map, get?_zip, get?_zipWith]
  cases get? m₁ k <;> cases get? m₂ k <;> simp [Option.bind, Option.map]

theorem zipWith_insert {f : V → V' → V''} {m₁ : M V} {m₂ : M V'} {k : K}
    {v : V} {v' : V'} :
    zipWith f (insert m₁ k v) (insert m₂ k v') ≡ₘ
      insert (zipWith f m₁ m₂) k (f v v') := by
  intro k'
  by_cases h : k = k'
  · subst h
    simp [get?_zipWith, get?_insert_eq rfl]
  · simp [get?_zipWith, get?_insert_ne h]

theorem zipWith_delete {f : V → V' → V''} {m₁ : M V} {m₂ : M V'} {k : K} :
    zipWith f (delete m₁ k) (delete m₂ k) ≡ₘ delete (zipWith f m₁ m₂) k := by
  intro k'
  by_cases h : k = k'
  · subst h
    simp [get?_zipWith, get?_delete_eq rfl]
  · simp [get?_zipWith, get?_delete_ne h]

theorem zipWith_comm {f : V → V' → V''} {m₁ : M V} {m₂ : M V'} :
    (∀ v v', f v v' = f v v') →
    zipWith f m₁ m₂ ≡ₘ zipWith f m₁ m₂ := by
  intro _; intro _; rfl

theorem zip_comm {m₁ : M V} {m₂ : M V'} :
    PartialMap.map Prod.swap (zip m₁ m₂) ≡ₘ zip m₂ m₁ := by
  intro k
  simp [get?_map, get?_zip]
  cases get? m₁ k <;> cases get? m₂ k <;> simp [Option.bind, Option.map]

theorem zip_map {f : V → V'} {g : V → V''} {m : M V} :
    zip (PartialMap.map f m) (PartialMap.map g m) ≡ₘ
      PartialMap.map (fun v => (f v, g v)) m := by
  intro k
  simp [zip, get?_map, zipWith, get?_bindAlter]
  cases get? m k <;> simp [Option.bind, Option.map]

theorem zip_fst_snd {m : M (V × V')} :
    zip (PartialMap.map Prod.fst m) (PartialMap.map Prod.snd m) ≡ₘ m := by
  intro k
  simp [zip, zipWith, get?_map, get?_bindAlter]
  cases h : get? m k <;> simp [Option.bind, Option.map]

theorem isSome_zipWith {f : V → V' → V''} {m₁ : M V} {m₂ : M V'} {k : K} :
    (get? (zipWith f m₁ m₂) k).isSome ↔
      (get? m₁ k).isSome ∧ (get? m₂ k).isSome := by
  rw [get?_zipWith]
  cases h1 : get? m₁ k <;> cases h2 : get? m₂ k <;> simp

theorem zip_empty_left {m : M V'} :
    zip (empty : M V) m ≡ₘ empty := by
  intro k
  simp only [zip, zipWith, get?_bindAlter, get?_empty, Option.bind]

theorem zip_empty_right {m : M V} :
    zip m (empty : M V') ≡ₘ empty := by
  intro k
  simp only [zip, zipWith, get?_bindAlter, get?_empty, Option.bind]
  cases h : get? m k <;> simp

theorem zip_insert {m₁ : M V} {m₂ : M V'} {k : K} {v : V} {v' : V'} :
    zip (insert m₁ k v) (insert m₂ k v') ≡ₘ insert (zip m₁ m₂) k (v, v') := by
  intro k'
  by_cases h : k = k'
  · subst h
    simp [get?_zip, get?_insert_eq rfl]
  · simp [get?_zip, get?_insert_ne h]

theorem zip_delete {m₁ : M V} {m₂ : M V'} {k : K} :
    zip (delete m₁ k) (delete m₂ k) ≡ₘ delete (zip m₁ m₂) k := by
  intro k'
  by_cases h : k = k'
  · subst h
    simp [get?_zip, get?_delete_eq rfl]
  · simp [get?_zip, get?_delete_ne h]

theorem isSome_zip {m₁ : M V} {m₂ : M V'} {k : K} :
    (get? (zip m₁ m₂) k).isSome ↔ (get? m₁ k).isSome ∧ (get? m₂ k).isSome := by
  rw [get?_zip]
  cases h1 : get? m₁ k <;> cases h2 : get? m₂ k <;> simp

theorem ofList_cons {L : List (K × V)} :
  ofList (M := M) ((k, v) :: L) = insert (ofList L) k v :=
  rfl

theorem noDupKeys_cons {L : List (K × V)} : NoDupKeys (h :: L) → NoDupKeys L := by
  unfold NoDupKeys
  grind

theorem noDupKeys_inj {L : List (K × V)} (Hdup : NoDupKeys L) (Hin : (k, v) ∈ L)
    (Hin' : (k, v') ∈ L) : v = v' := by
  induction L with
  | nil => cases Hin
  | cons h t IH =>
    obtain ⟨k₀, v₀⟩ := h
    simp [NoDupKeys, List.map_cons] at Hdup
    obtain ⟨hnotin, ht⟩ := Hdup
    simp at Hin Hin'
    cases Hin with
    | inl heq =>
      cases Hin' with
      | inl heq' => exact heq.2.trans heq'.2.symm
      | inr hmem => grind
    | inr hmem =>
      cases Hin' with
      | inl heq' => grind
      | inr hmem' => exact IH ht hmem hmem'

theorem get?_ofList_some [DecidableEq K] {L : List (K × V)}
    (Hin : (k, v) ∈ L) (Hdup : NoDupKeys L) : get? (ofList (M := M) L) k = some v := by
  induction L
  · simp at Hin
  rename_i h t IH
  obtain ⟨k', v'⟩ := h
  rw [ofList_cons]
  rcases List.eq_or_mem_of_mem_cons Hin with ⟨rfl, rfl⟩|Hin'
  · rw [get?_insert_eq rfl]
  · rw [get?_insert_some_iff]
    by_cases Hk : k' = k
    · exact .inl ⟨Hk, (noDupKeys_inj Hdup Hin (Hk ▸ List.mem_cons_self)).symm⟩
    · exact .inr ⟨Ne.intro Hk, IH Hin' (noDupKeys_cons Hdup)⟩

theorem get?_ofList_none {L : List (K × V)}
    (Hin : ¬ ∃ v, (k, v) ∈ L) (Hdup : NoDupKeys L) :
    get? (ofList (M := M) L) k = none  := by
  induction L
  · simp [ofList, get?_empty]
  rename_i h t IH
  obtain ⟨k', v'⟩ := h
  rw [ofList_cons]
  by_cases h : k' = k
  · exact (Hin ⟨v', h ▸ List.mem_cons_self⟩).elim
  · rw [get?_insert_ne h]
    exact IH (by grind) (noDupKeys_cons Hdup)

end LawfulPartialMap

namespace LawfulFiniteMap

variable {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]

open FiniteMap LawfulFiniteMap PartialMap LawfulPartialMap

theorem mapFold_empty {f : K → V → A → A} :
  mapFold f a (∅ : M V) = a := by
  simp only [mapFold, Std.toList, toList_empty (M := M) (K := K) (V := V)]
  rfl

-- TODO: These should be theorems
-- NOTE: This one is not provable without P respecting equivalence
-- mapFold_ind {P : M A → Prop}:
--   P ∅ →
--   (∀ i x m,
--     get? m i = none →
--     (∀ A' B (f : K → A' → B → B) (g : A → A') b x',
--       mapFold f b (insert (PartialMap.map g m) i x') =
--         f i x' (mapFold f b (PartialMap.map g m))) →
--     P m →
--     P (insert m i x)) →
--   ∀ m, P m

theorem toList_get?_none {m : M V} :
  (∀ v, (k, v) ∉ toList (K := K) m) ↔ get? m k = none := by
  constructor
  · intro Hn
    refine Option.eq_none_iff_forall_ne_some.mpr ?_
    exact fun v' Hsome => Hn v' <| toList_get.mpr Hsome
  · intro Hn v Hk
    cases Hn ▸ toList_get.mp Hk

theorem NoDupKeys_noDup {L : List (K × V)} : NoDupKeys L → L.Nodup := by
  refine fun H => FromMathlib.List.Nodup.of_map (fun x => x.fst) ?_
  exact H

theorem nodup_toList {m : M V} : (toList (K := K) m).Nodup :=
  NoDupKeys_noDup toList_noDupKeys

theorem ofList_toList [DecidableEq K] {m : M V} :
    PartialMap.equiv (ofList (toList (K := K) m)) m := by
  intro k
  rcases h : get? m k with _|v
  · refine get?_ofList_none ?_ toList_noDupKeys
    intro ⟨v, Hk⟩
    cases h ▸ toList_get.mp Hk
  · exact get?_ofList_some (toList_get.mpr h) toList_noDupKeys

@[elab_as_elim]
theorem induction_on [DecidableEq K] {P : M V → Prop}
    (hequiv : ∀ m₁ m₂, PartialMap.equiv m₁ m₂ → P m₁ → P m₂)
    (hemp : P PartialMap.empty)
    (hins : ∀ i x m, get? m i = none → P m → P (PartialMap.insert m i x))
    (m : M V) : P m := by
  apply hequiv _ _ ofList_toList
  suffices ∀ l, NoDupKeys l → P (ofList l) from this _ toList_noDupKeys
  intro l hnd
  induction l with
  | nil => simpa [ofList] using hemp
  | cons kv rest ih =>
    rw [ofList_cons]
    apply hins kv.1 kv.2
    · refine get?_ofList_none (M := M) ?_ (noDupKeys_cons hnd)
      intro ⟨v, hv⟩
      exact (List.nodup_cons.mp hnd).1
        (List.mem_map_of_mem (f := Prod.fst) (a := (kv.1, v)) hv)
    · exact ih (noDupKeys_cons hnd)

theorem mem_of_mem_ofList [DecidableEq K] {l : List (K × V)} {i : K} {x : V}
    (H : get? (ofList l : M V) i = some x) : (i, x) ∈ l := by
  induction l
  · simp [ofList, get?_empty] at H
  · rename_i h t IH
    obtain ⟨k, v⟩ := h
    rw [ofList_cons] at H
    by_cases He : k = i
    · subst He
      rw [get?_insert_eq rfl] at H
      obtain ⟨rfl⟩ := H
      exact List.mem_cons_self
    · rw [get?_insert_ne He] at H
      exact List.mem_cons_of_mem (k, v) (IH H)

theorem toList_ofList [DecidableEq K] {l : List (K × V)} (Hdup : NoDupKeys l) :
    (toList (M := M) (K := K) (ofList l : M V)).Perm l := by
  refine (List.perm_ext_iff_of_nodup nodup_toList ?_).mpr fun ⟨k, v⟩ => ⟨?_, ?_⟩
  · exact NoDupKeys_noDup Hdup
  · exact (mem_of_mem_ofList <| toList_get.mp ·)
  · exact (toList_get.mpr <| get?_ofList_some · Hdup)

theorem toList_perm_of_get?_eq {m₁ m₂ : M V} (h : ∀ k, get? m₁ k = get? m₂ k) :
    (toList (M := M) (K := K) m₁).Perm (toList (M := M) (K := K) m₂) := by
  refine (List.perm_ext_iff_of_nodup nodup_toList nodup_toList).mpr fun ⟨k, v⟩ => ⟨?_, ?_⟩
  · intro H
    refine toList_get.mpr ?_
    rw [← h k]
    exact toList_get.mp H
  · intro H
    refine toList_get.mpr ?_
    rw [h k]
    exact toList_get.mp H

theorem toList_insert {m : M V} {k : K} {v : V} (h : get? m k = none) :
    (toList (M := M) (K := K) (insert m k v)).Perm ((k, v) :: toList (M := M) (K := K) m) := by
  refine (List.perm_ext_iff_of_nodup nodup_toList ?_).mpr fun ⟨k', v'⟩ => ⟨?_, ?_⟩
  · refine  List.nodup_cons.mpr ⟨?_, nodup_toList⟩
    exact fun H => Option.some_ne_none _ (h ▸ toList_get.mp H).symm
  · intro H
    have H' := toList_get.mp H
    by_cases He : k = k'
    · rw [get?_insert_eq He] at H'
      obtain ⟨rfl⟩ := H'
      rw [He]
      exact List.mem_cons_self
    · refine List.mem_cons_of_mem (k, v) ?_
      refine toList_get.mpr ?_
      rw [get?_insert_ne He] at H'
      exact H'
  · intro H
    cases H
    · exact toList_get.mpr (get?_insert_eq rfl)
    · rename_i H
      by_cases He : k = k'
      · exfalso
        subst He
        cases h ▸ toList_get.mp H
      · refine toList_get.mpr ?_
        rw [get?_insert_ne He]
        refine toList_get.mp H

theorem toList_delete {m : M V} {k : K} {v : V} (h : get? m k = some v) :
    (toList (M := M) (K := K) m).Perm ((k, v) :: toList (M := M) (K := K) (delete m k)) := by
  refine (List.perm_ext_iff_of_nodup nodup_toList ?_).mpr fun ⟨k', v'⟩ => ⟨?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, nodup_toList⟩
    intro H
    have Hget := toList_get.mp H
    rw [get?_delete_eq rfl] at Hget
    cases Hget
  · intro H
    by_cases He : k = k'
    · subst He
      obtain ⟨rfl⟩ := h ▸ toList_get.mp H
      exact List.mem_cons_self
    · refine List.mem_cons_of_mem (k, v) ?_
      refine toList_get.mpr ?_
      rw [get?_delete_ne He]
      refine toList_get.mp H
  · intro H
    cases H
    · exact toList_get.mpr h
    · rename_i H'
      refine toList_get.mpr ?_
      have H'' := toList_get.mp H'
      by_cases He : k = k'
      · rw [get?_delete_eq He] at H''
        cases H''
      · rw [get?_delete_ne He] at H''
        exact H''

theorem all_iff_toList {P : K → V → Prop} {m : M V} :
    PartialMap.all P m ↔ ∀ kv ∈ toList m, P kv.1 kv.2 :=
  ⟨fun H ⟨k, v⟩ Hm => H k v (toList_get.mp Hm),
   fun H k v hg => H (k, v) (toList_get.mpr hg)⟩

theorem mem_ofList [DecidableEq K] {l : List (K × V)} {i : K} {x : V}
    (hnodup : (l.map Prod.fst).Nodup) :
    (i, x) ∈ l ↔ get? (ofList l : M V) i = some x :=
  ⟨(get?_ofList_some · hnodup), mem_of_mem_ofList⟩

theorem ofList_injective [DecidableEq K] {l₁ l₂ : List (K × V)}
    (hnodup1 : (l₁.map Prod.fst).Nodup) (hnodup2 : (l₂.map Prod.fst).Nodup) :
    PartialMap.equiv (ofList l₁ : M V) (ofList l₂) → l₁.Perm l₂ := by
  intro He
  refine (List.perm_ext_iff_of_nodup (NoDupKeys_noDup hnodup1) (NoDupKeys_noDup hnodup2)).mpr ?_
  refine fun ⟨k, v⟩ => ⟨fun H => ?_, fun H => ?_⟩
  · apply mem_of_mem_ofList (M := M)
    rw [← He k]
    exact get?_ofList_some H (List.nodup_iff_pairwise_ne.mpr hnodup1)
  · apply mem_of_mem_ofList (M := M)
    rw [He k]
    exact get?_ofList_some H (List.nodup_iff_pairwise_ne.mpr hnodup2)

theorem toList_insert_delete {m : M V} {k : K} {v : V} :
    (toList (M := M) (K := K) (insert m k v)).Perm
      (toList (M := M) (K := K) (insert (delete m k) k v)) := by
  apply toList_perm_of_get?_eq
  intro k'
  by_cases h : k = k'
  · simp [LawfulPartialMap.get?_insert_eq h]
  · simp [LawfulPartialMap.get?_insert_ne h, LawfulPartialMap.get?_delete_ne h]

theorem toList_map {f : V → V'} {m : M V}  :
    (toList (M := M) (K := K) (PartialMap.map f m)).Perm
      ((toList m).map (fun kv => (kv.1, f kv.2))) := by
  refine (List.perm_ext_iff_of_nodup nodup_toList ?_).mpr fun ⟨k, v⟩ => ⟨?_, ?_⟩
  · refine FromMathlib.Nodup.map_on ?_ nodup_toList
    rintro ⟨x₁, y₁⟩ H₁ ⟨x₂, y₂⟩ H₂
    simp only [Prod.mk.injEq, and_imp]
    rintro rfl _
    exact ⟨rfl, noDupKeys_inj toList_noDupKeys H₁ H₂⟩
  · intro H
    refine List.mem_map.mpr ?_
    have H' := toList_get.mp H
    rw [get?_map] at H'
    obtain ⟨v, Ha₁, Ha₂⟩ := Option.map_eq_some_iff.mp H'
    exact ⟨⟨k, v⟩, toList_get.mpr Ha₁, Prod.ext rfl Ha₂⟩
  · intro H
    obtain ⟨a, Ha₁, Ha₂⟩ := List.mem_map.mp H
    obtain ⟨rfl, H⟩ := Ha₂
    refine toList_get.mpr ?_
    rw [get?_map, toList_get.mp Ha₁]
    rfl

theorem toList_filterMap {f : V → Option V} {m : M V} (HI : Function.Injective f) :
    (toList (M := M) (K := K) (PartialMap.filterMap f m)).Perm
      ((toList m).filterMap (fun kv => (f kv.2).map (kv.1, ·))) := by
  refine (List.perm_ext_iff_of_nodup nodup_toList ?_).mpr fun ⟨k, v⟩ => ⟨?_, ?_⟩
  · refine FromMathlib.Nodup.filterMap ?_ nodup_toList
    simp only [Option.mem_def, Option.map_eq_some_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Prod.mk.injEq, Prod.forall]
    rintro _ _ _ _ _ H1 _ H2 rfl rfl
    exact ⟨rfl, HI (H2 ▸ H1)⟩
  · intro H
    refine List.mem_filterMap.mpr ?_
    have H' := toList_get.mp H
    simp [get?_filterMap] at H'
    obtain ⟨v', Ha₁, Ha₂⟩ := Option.bind_eq_some_iff.mp H'
    simp only [Option.map_eq_some_iff]
    exact ⟨(k, v'), toList_get.mpr Ha₁, v, Ha₂, rfl⟩
  · intro H
    obtain ⟨a, Ha₁, Ha₂⟩ := List.mem_filterMap.mp H
    refine toList_get.mpr ?_
    rw [get?_filterMap]
    refine Option.bind_eq_some_iff.mpr ?_
    simp at Ha₂
    obtain ⟨H', rfl⟩ := Ha₂
    refine ⟨a.snd, toList_get.mp Ha₁, H'⟩

theorem toList_filter {φ : K → V → Bool} {m : M V} :
    (toList (M := M) (K := K) (PartialMap.filter φ m)).Perm
      ((toList m).filter (fun kv => φ kv.1 kv.2)) := by
  refine (List.perm_ext_iff_of_nodup nodup_toList ?_).mpr fun ⟨k, v⟩ => ⟨?_, ?_⟩
  · exact FromMathlib.Nodup.filter ?_ (nodup_toList (M := M) (K := K))
  · intro H
    refine List.mem_filter.mpr ?_
    have H' := toList_get.mp H
    simp only [get?_filter] at H'
    obtain ⟨v', Ha₁, Ha₂⟩ := Option.bind_eq_some_iff.mp H'
    by_cases h : φ k v'
    · simp only [h, ↓reduceIte, Option.some.injEq] at Ha₂
      subst Ha₂
      exact ⟨toList_get.mpr Ha₁, h⟩
    · simp [h] at Ha₂
  · intro H
    refine toList_get.mpr ?_
    simp only [List.mem_filter] at H
    simp [get?_filter, toList_get.mp H.1, H.2]

theorem toList_zip {m₁ : M V} {m₂ : M V'} :
    (toList (M := M) (K := K) (PartialMap.zip m₁ m₂)).Perm
      ((toList m₁).filterMap fun kv₁ =>
        (get? m₂ kv₁.1).map fun v₂ => (kv₁.1, (kv₁.2, v₂))) := by
  refine (List.perm_ext_iff_of_nodup nodup_toList ?_).mpr fun ⟨k, v⟩ => ⟨?_, ?_⟩
  · refine FromMathlib.Nodup.filterMap ?_ nodup_toList
    simp only [Option.mem_def, Option.map_eq_some_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Prod.mk.injEq, Prod.forall]
    rintro _ _ _ _ _ _ _ _ rfl rfl rfl; exact ⟨rfl, rfl⟩
  · intro H
    refine List.mem_filterMap.mpr ?_
    have H' := toList_get.mp H
    simp [get?_zip] at H'
    obtain ⟨v', Ha₁, Ha₂⟩ := Option.bind_eq_some_iff.mp H'
    simp only [Option.map_eq_some_iff]
    simp only [Option.map_eq_some_iff] at Ha₂
    obtain ⟨b, Hb₁, Hb₂⟩ := Ha₂
    exact ⟨(k, v'), toList_get.mpr Ha₁, _, Hb₁, Prod.ext rfl Hb₂⟩
  · intro H
    obtain ⟨a, Ha₁, Ha₂⟩ := List.mem_filterMap.mp H
    refine toList_get.mpr ?_
    rw [get?_zip]
    refine Option.bind_eq_some_iff.mpr ?_
    simp at Ha₂
    obtain ⟨b, Hb₁, rfl, rfl⟩ := Ha₂
    refine ⟨a.2, toList_get.mp Ha₁, ?_⟩
    simp [Hb₁]

end LawfulFiniteMap

/-- Remap keys in a map from one key type to another. -/
def kmap {K1 K2 : Type _} {V : Type _} {M1 : Type _ → Type _} {M2 : Type _ → Type _}
    [LawfulFiniteMap M1 K1] [LawfulFiniteMap M2 K2]
    (f : K1 → K2) (m : M1 V) : M2 V :=
  PartialMap.ofList ((toList (K := K1) m).map (Prod.map f id))

theorem no_dup_keys_prod_map {K1 K2 : Type _} {V : Type _}
  {M1 : Type _ → Type _} {M2 : Type _ → Type _}
  [DecidableEq K1] [DecidableEq K2]
  [LawfulFiniteMap M1 K1] [LawfulFiniteMap M2 K2]
  {m : M1 V} {f : K1 → K2} (hinj : Function.Injective f) {g : V → V} :
  NoDupKeys (toList (K := K1) m)
    → NoDupKeys (List.map (Prod.map f g) (toList m)) := by
  simp only [NoDupKeys]
  rw [List.map_map]
  intro H
  apply FromMathlib.Nodup.map_on
  · rintro ⟨k, x⟩ Hin ⟨k', x'⟩ Hin'; dsimp; intro heq
    rw [hinj heq]; rw [hinj heq] at Hin
    rw [LawfulPartialMap.noDupKeys_inj LawfulFiniteMap.toList_noDupKeys Hin Hin']
  · apply FromMathlib.List.Nodup.of_map _ H

namespace Kmap

open PartialMap LawfulPartialMap LawfulFiniteMap

variable {K1 K2 : Type _} {V : Type _} {M1 : Type _ → Type _} {M2 : Type _ → Type _}
variable [DecidableEq K1] [DecidableEq K2]
variable [LawfulFiniteMap M1 K1] [LawfulFiniteMap M2 K2]
variable (f : K1 → K2)

theorem get?_kmap_some (hinj : Function.Injective f) (m : M1 V) (j : K2) (x : V) :
    get? (kmap (M2 := M2) f m) j = some x ↔ ∃ i, j = f i ∧ get? m i = some x := by
  constructor
  · intro h
    have ⟨a, heq1, heq2⟩ : ∃ a, (a, x) ∈ toList m ∧ f a = j := by
      have this := mem_of_mem_ofList h
      rw [List.mem_map] at this
      obtain ⟨⟨a, b⟩, hin, heq⟩ := this; dsimp at heq; rw [Prod.mk.injEq] at heq
      exists a; rw [<-heq.right]; apply And.intro; assumption
      exact heq.left
    exists a; rw [heq2, <-h]; apply And.intro; simp
    simp only [kmap]
    rw [get?_ofList_some (v := x)]
    · rw [<-toList_get]; exact heq1
    · rw [List.mem_map]
      exists ⟨a, x⟩; apply And.intro; assumption
      dsimp; rw [<-heq2]
    · apply no_dup_keys_prod_map (M2 := M2) hinj
      apply toList_noDupKeys
  · intro ⟨i, heq, hget⟩
    subst heq; rw [<-hget]
    simp only [kmap]
    rw [get?_ofList_some (v := x)]; symm; assumption
    · rw [List.mem_map]
      exists ⟨i, x⟩; apply And.intro;
        apply toList_get.mpr; assumption
      dsimp
    · apply no_dup_keys_prod_map (M2 := M2) hinj
      apply toList_noDupKeys

theorem get?_kmap_isSome (hinj : Function.Injective f) (m : M1 V) (j : K2) :
    (get? (kmap (M2 := M2) f m) j).isSome ↔ ∃ i, j = f i ∧ (get? m i).isSome := by
  constructor
  · intro h
    have ⟨a, h⟩ := Option.isSome_iff_exists.mp h
    rw [get?_kmap_some f hinj m j] at h
    obtain ⟨i, heq1, heq2⟩ := h
    exists i; apply And.intro; assumption
    rw [Option.isSome_iff_exists]
    exists a
  · intro ⟨i, heq, h⟩
    have ⟨a, h⟩ := Option.isSome_iff_exists.mp h
    rw [Option.isSome_iff_exists]
    exists a
    rw [get?_kmap_some f hinj m j]
    exists i

theorem get?_kmap_none (hinj : Function.Injective f) (m : M1 V) (j : K2) :
    get? (kmap (M2 := M2) f m) j = none ↔ ∀ i, j = f i → get? m i = none := by
  constructor
  · intro g i heq
    rw [<-toList_get?_none]
    intro v h
    rw [<-toList_get?_none] at g
    apply g v
    rw [heq]
    apply toList_get.mpr
    rw [get?_kmap_some _ hinj]
    exists i; apply And.intro; rfl
    apply toList_get.mp; assumption
  · intro g
    rw [<-toList_get?_none]
    intro v h
    rw [toList_get, get?_kmap_some _ hinj] at h
    obtain ⟨i, heq, hget⟩ := h
    rw [g i heq] at hget
    simp at hget

theorem get?_kmap (hinj : Function.Injective f) (m : M1 V) (i : K1) :
    get? (kmap (M2 := M2) f m) (f i) = get? m i := by
  cases h : get? m i
  · rw [get?_kmap_none f hinj]
    intro i' heq
    rw [<-hinj heq]
    assumption
  · rw [get?_kmap_some f hinj, <-h]
    exists i

theorem kmap_empty (hinj : Function.Injective f) :
  kmap (M1 := M1) (M2 := M2) f (∅ : M1 V) ≡ₘ ∅ := by
  rw [eq_empty_iff]
  intro k
  rw [get?_kmap_none _ hinj]
  intro i heq
  exact get?_empty i

theorem kmap_injective (hinj : Function.Injective f) (m1 m2 : M1 V) :
    kmap (M2 := M2) f m1 ≡ₘ kmap (M2 := M2) f m2
    → m1 ≡ₘ m2 := by
  intro heq
  apply induction_on (K := K1) (P := fun m1 => ∀ m2,
    kmap (M2 := M2) f m1 ≡ₘ kmap (M2 := M2) f m2
    → m1 ≡ₘ m2)
  · intro m₁ m₂ heqm hP m2' heq'
    intro k
    specialize (heq' (f k))
    rw [get?_kmap _ hinj, get?_kmap _ hinj] at heq'
    rw [<-heq']
  · intro m2' heq'
    intro k'
    specialize (heq' (f k'))
    rw [get?_kmap _ hinj, get?_kmap _ hinj] at heq'
    exact heq'
  · intro k x m' hm' IH m2' heq'
    intro k'
    specialize (heq' (f k'))
    rw [get?_kmap _ hinj, get?_kmap _ hinj] at heq'
    exact heq'
  · exact heq

theorem kmap_insert (hinj : Function.Injective f) (m : M1 V) (k : K1) (x : V) :
    get? m k = none →
    kmap f (insert m k x) ≡ₘ insert (kmap (M2 := M2) f m) (f k) x := by
  intro hk j
  by_cases h : f k = j
  · subst h
    rw [get?_insert_eq rfl, get?_kmap _ hinj, get?_insert_eq rfl]
  · rw [get?_insert_ne h]
    cases g : get? (kmap (M2 := M2) f (insert m k x)) j
    · rw [get?_kmap_none _ hinj] at g
      symm
      rw [get?_kmap_none _ hinj]
      intro i heq
      specialize g i heq
      rw [heq] at h
      rw [get?_insert_ne] at g; assumption
      intro j
      apply h
      rw [j]
    · rw [get?_kmap_some _ hinj] at g
      obtain ⟨i, heq, hget⟩ := g
      rw [heq] at h
      symm
      rw [get?_kmap_some _ hinj]
      exists i; apply And.intro; assumption
      rw [get?_insert_ne] at hget; assumption
      intro j
      apply h
      rw [j]

  theorem kmap_compose [DecidableEq K3] [LawfulFiniteMap M3 K3]
    (hinj_f : Function.Injective f) (g : K2 → K3)
    (hinj_g : Function.Injective g) (m : M1 V) :
    kmap g (kmap (M2 := M2) f m) ≡ₘ kmap (M2 := M3) (g ∘ f) m := by
  intro k
  have hinj_fg : Function.Injective (g ∘ f) := Function.Injective.comp hinj_g hinj_f
  cases h : get? (kmap g (M2 := M3) (kmap (M2 := M2) f m)) k
  · symm
    rw [get?_kmap_none _ hinj_fg]
    intro i heq
    rw [get?_kmap_none _ hinj_g] at h
    specialize (h (f i) heq)
    rw [get?_kmap_none _ hinj_f] at h
    apply h _ rfl
  · symm
    rw [get?_kmap_some _ hinj_fg]
    rw [get?_kmap_some _ hinj_g] at h
    obtain ⟨j, heq_j, h⟩ := h
    rw [get?_kmap_some _ hinj_f] at h
    obtain ⟨i, heq_i, h⟩ := h
    exists i; apply And.intro; simp only [heq_i, heq_j, Function.comp_apply]
    assumption

  theorem kmap_id {m : M1 V} : kmap (K2 := K1) (M2 := M1) id m ≡ₘ m := by
    intro k
    simp only [kmap]
    rw [Prod.map_id, List.map_id]
    apply ofList_toList (M := M1) (m := m) k

  theorem kmap_union (hinj : Function.Injective f)
    (m₁ m₂ : M1 V) :
    kmap f (m₁ ∪ m₂) ≡ₘ (kmap (M2 := M2) f m₁) ∪ (kmap f m₂) := by
    intro k
    simp only [Union.union]
    rw [get?_union (m₁ := kmap f m₁) (m₂ := kmap f m₂) (k := k)]
    cases h : get? (kmap (M2 := M2) f (union m₁ m₂)) k
    · symm
      rw [Option.orElse_eq_or, Option.or_eq_none_iff]
      rw [get?_kmap_none _ hinj, get?_kmap_none _ hinj]
      rw [get?_kmap_none _ hinj] at h
      apply And.intro
      · intro i heq
        specialize h i heq
        rw [get?_union (m₁ := m₁) (m₂ := m₂) (k := i)] at h
        rw [Option.orElse_eq_or, Option.or_eq_none_iff] at h
        apply h.left
      · intro i heq
        specialize h i heq
        rw [get?_union (m₁ := m₁) (m₂ := m₂) (k := i)] at h
        rw [Option.orElse_eq_or, Option.or_eq_none_iff] at h
        apply h.right
    · symm
      rw [Option.orElse_eq_or, Option.or_eq_some_iff]
      rw [get?_kmap_some _ hinj] at h
      obtain ⟨i, heq, h⟩ := h
      rw [get?_union (m₁ := m₁) (m₂ := m₂) (k := i)] at h
      rw [Option.orElse_eq_or, Option.or_eq_some_iff] at h
      cases h with
      | inl h =>
        left
        rw [heq, get?_kmap_some _ hinj]
        exists i
      | inr h =>
        right
        rw [heq, get?_kmap_some _ hinj, get?_kmap_none _ hinj]
        apply And.intro
        · intro j heq'
          rw [<-hinj heq', h.left]
        · exists i; apply And.intro; simp
          exact h.right

  theorem kmap_delete (hinj : Function.Injective f)
    (i : K1) (m : M1 V) :
    kmap f (delete m i) ≡ₘ delete (kmap (M2 := M2) f m) (f i) := by
    intro j
    by_cases h : f i = j
    · subst h
      rw [get?_delete_eq rfl, get?_kmap_none _ hinj]
      intro k heq
      rw [hinj heq, get?_delete_eq rfl]
    · rw [get?_delete_ne h]
      cases g : get? (kmap (M2 := M2) f m) j
      · rw [get?_kmap_none _ hinj] at g
        rw [get?_kmap_none _ hinj]
        intro k heq
        rw [get?_delete_ne]
        · apply g _ heq
        · intro c; rw [heq, c] at h; apply h rfl
      · rw [get?_kmap_some _ hinj] at g
        obtain ⟨k, heq, g⟩ := g
        rw [get?_kmap_some _ hinj]
        exists k; apply And.intro; assumption
        rw [get?_delete_ne, g]
        intro c; rw [heq, c] at h; apply h rfl

  theorem kmap_singleton (hinj : Function.Injective f) (k : K1) (x : V) :
    kmap (M2 := M2) f (singleton (M := M1) k x) ≡ₘ singleton (f k) x := by
    intro j
    by_cases h : f k = j
    · subst h
      rw [get?_kmap _ hinj, get?_singleton_eq rfl, get?_singleton_eq rfl]
    · rw [get?_singleton_ne h, get?_kmap_none _ hinj]
      intro i heq
      rw [get?_singleton_ne]
      intro c; rw [heq, c] at h; apply h rfl

  theorem kmap_mem (hinj : Function.Injective f) (m : M1 V) (k : K1) :
    k ∈ m ↔ f k ∈ kmap (M2 := M2) f m := by
    simp only [Membership.mem]
    rw [get?_kmap_isSome _ hinj]
    apply Iff.intro
    · intro h
      exists k
    · intro h
      obtain ⟨i, heq, hget⟩ := h
      rw [hinj heq]
      assumption

  theorem kmap_dom (hinj : Function.Injective f) (m : M1 V) :
    dom (kmap (M2 := M2) f m) = (fun k => ∃ j, k = f j ∧ dom m j) := by
    ext j
    simp only [dom]
    rw [get?_kmap_isSome _ hinj]

  theorem kmap_bindAlter (hinj : Function.Injective f) (g : K2 → V → Option V') (m : M1 V) :
    kmap f (bindAlter (g ∘ f) m) ≡ₘ bindAlter g (kmap (M2 := M2) f m) := by
    intro k
    rw [get?_bindAlter]
    cases h : get? (kmap (M2 := M2) f m) k
    · rw [Option.bind_none, get?_kmap_none _ hinj]
      intro i heq
      rw [get?_kmap_none _ hinj] at h
      rw [get?_bindAlter]
      rw [Option.bind_eq_none_iff]
      intro a g
      specialize h i heq
      cases h ▸ g
    · rw [Option.bind_some]
      rw [get?_kmap_some _ hinj] at h
      obtain ⟨i, heq, h⟩ := h
      rw [heq, get?_kmap _ hinj]
      rw [get?_bindAlter, h, Option.bind_some]
      rfl

  theorem kmap_map (hinj : Function.Injective f)
    (g : V → V') (m : M1 V) :
    kmap f (map g m) ≡ₘ map g (kmap (M2 := M2) f m) := by
    intro k
    simp only [map]
    rw [<-kmap_bindAlter (M2 := M2) _ hinj (fun k v => some (g v)) m k]
    rfl

  theorem kmap_filterMap (hinj : Function.Injective f)
    (g : V → Option V) (m : M1 V) :
    kmap f (filterMap g m) ≡ₘ filterMap g (kmap (M2 := M2) f m) := by
    intro k
    simp only [filterMap]
    rw [<-kmap_bindAlter (M2 := M2) _ hinj (fun k v => g v) m k]
    rfl

  theorem kmap_filter (hinj : Function.Injective f) (φ : K2 → V → Bool)  (m : M1 V) :
    kmap f (filter (fun k v => φ (f k) v) m) ≡ₘ filter φ (kmap (M2 := M2) f m) := by
    intro k
    simp only [filter]
    rw [<-kmap_bindAlter (M2 := M2) _ hinj (fun k v => if φ k v = true then some v else none) m k]
    rfl

  theorem kmap_disjoint (hinj : Function.Injective f) (m₁ m₂ : M1 V) :
    (kmap (M2 := M2) f m₁) ##ₘ (kmap f m₂) ↔ m₁ ##ₘ m₂ := by
    simp only [PartialMap.disjoint]
    apply Iff.intro
    · intro h i heq
      apply h (f i)
      rw [get?_kmap_isSome _ hinj, get?_kmap_isSome _ hinj]
      apply And.intro
      · exists i; apply And.intro; rfl
        rw [heq.left]
      · exists i; apply And.intro; rfl
        rw [heq.right]
    · intro h k heq
      rw [get?_kmap_isSome _ hinj, get?_kmap_isSome _ hinj] at heq
      obtain ⟨i, heq1, h1⟩ := heq.left
      obtain ⟨j, heq2, h2⟩ := heq.right
      cases (hinj (heq1 ▸ heq2))
      apply h i
      rw [h1, h2]; simp

  theorem kmap_submap (hinj : Function.Injective f) (m₁ m₂ : M1 V) :
    (kmap (M2 := M2) f m₁) ⊆ (kmap f m₂) ↔ m₁ ⊆ m₂ := by
    simp only [HasSubset.Subset]
    apply Iff.intro
    · intro h i v hget
      specialize h (f i) v
      rw [get?_kmap_some _ hinj, get?_kmap_some _ hinj] at h
      have hyp : ∃ i_1, f i = f i_1 ∧ get? m₁ i_1 = some v := by
        exists i
      obtain ⟨j, heq, hget⟩ := h hyp
      rw [hinj heq]
      exact hget
    · intro h i v hget
      rw [get?_kmap_some _ hinj]
      rw [get?_kmap_some _ hinj] at hget
      obtain ⟨j, heq, hget⟩ := hget
      exists j; apply And.intro; assumption
      apply h _ _ hget

  theorem kmap_all (hinj : Function.Injective f) (P : K2 → V → Prop) (m : M1 V) :
    all (P ∘ f) m ↔ all P (kmap (M2 := M2) f m) := by
    apply Iff.intro
    · intro h i v
      rw [get?_kmap_some _ hinj]
      intro h
      obtain ⟨j, heq, hget⟩ := h
      rw [heq]; apply h _ _ hget
    · intro h i v
      specialize h (f i) v
      rw [get?_kmap _ hinj] at h
      apply h

  theorem kmap_zipWith (hinj : Function.Injective f)
    (h : V → V' → V'')
    (m₁ : M1 V) (m₂ : M1 V') :
    kmap (M2 := M2) f (zipWith h m₁ m₂)
    ≡ₘ zipWith h (kmap (M2 := M2) f m₁) (kmap (M2 := M2) f m₂) := by
    intro k
    simp only [zipWith]
    rw [<-kmap_bindAlter (M2 := M2) _ hinj _ m₁ k]
    congr
    ext j v x
    rw [Function.comp_apply]
    rw [get?_kmap _ hinj]

  theorem kmap_difference (hinj : Function.Injective f) (m₁ m₂ : M1 V) :
    kmap f (m₁ \ m₂) ≡ₘ (kmap (M2 := M2) f m₁) \ (kmap f m₂) := by
    intro k
    rw [get?_difference (m₁ := kmap f m₁) (m₂ := kmap f m₂) (k := k)]
    cases h : get? (kmap (M2 := M2) f (m₁ \ m₂)) k
    · rw [get?_kmap_none _ hinj] at h
      symm
      simp only [ite_eq_left_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none]
      intro g
      rw [get?_kmap_none _ hinj]
      intro i heq
      specialize h i heq
      rw [get?_kmap_none _ hinj] at g
      specialize g i heq
      rw [get?_difference (m₁ := m₁) (m₂ := m₂) (k := i)] at h
      rw [g, Option.isSome_none] at h
      simp only [Bool.false_eq_true] at h
      apply h
    · rw [get?_kmap_some _ hinj] at h
      symm
      simp only [Option.ite_none_left_eq_some, Bool.not_eq_true
        , Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
      obtain ⟨i, heq, h⟩ := h
      rw [get?_difference (m₁ := m₁) (m₂ := m₂) (k := i)] at h
      rw [Option.ite_none_left_eq_some] at h
      rw [get?_kmap_none _ hinj, get?_kmap_some _ hinj, heq]
      simp only [Bool.not_eq_true, Option.isSome_eq_false_iff
        , Option.isNone_iff_eq_none] at h
      apply And.intro
      · intro j heq
        rw [<-hinj heq]
        rw [h.left]
      · exists i; apply And.intro; rfl
        rw [h.right]

end Kmap

end Iris.Std
