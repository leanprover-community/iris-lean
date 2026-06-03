/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Data.Multiset.Basic
public import Iris

/-! # `WordMap`: a non-extensional `PartialMap` whose stored payload is a raw *word*

This file defines a `LawfulPartialMap` instance in which each key stores a *word*
(`List V`) rather than a single value, and the observation `get?` collapses that word to
its last letter.  Distinct words with the same last letter therefore denote the same map:
the representation is genuinely **non-extensional** (two `≠` reps with `PartialMap.equiv`).

## Why this is the "free word / quotient" pattern

A `WordMap` stores, at every key, an unreduced *word*.  The observation `get?` is a
forgetful *denotation* `den : WordMap V → (K → Option V)` that only looks at the reduced
form of each word (here: its last letter, which is the net effect after all the
overwrites recorded in the word).  This mirrors `FreeGroup α`, where an element is an
equivalence class of words `List (α × Bool)` and `FreeGroup.mk` forgets the unreduced
representative; many distinct words reduce to the same group element.  Concretely, the
value type `V` of a `WordMap` is meant to be instantiated at a quotient-flavoured
commutative monoid such as `Multiset α` or a group such as `FreeGroup α` — see the
applicability note at the bottom of the file.

## Implementation

`WordMap V := K → List V`.  The empty word `[]` denotes "absent".  All seven laws are
proved by normalising each operation's output to `Option.toList`, so that `getLast?`
reads back exactly the intended `Option V`.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

variable {K V V' : Type _} [DecidableEq K]

/-- A `WordMap` stores a *word* (`List V`) at every key.  The empty word means "absent",
and a nonempty word denotes its last letter.  Distinct words with the same last letter
denote the same map. -/
def WordMap (K : Type _) (V : Type _) : Type _ := K → List V

namespace WordMap

/-- The forgetful denotation: read back the net value stored at `k` as the last letter of
its word. -/
def get? (m : WordMap K V) (k : K) : Option V := (m k).getLast?

/-- Insert stores the singleton word `[v]`. -/
def insert (m : WordMap K V) (k : K) (v : V) : WordMap K V :=
  fun k' => if k = k' then [v] else m k'

/-- Delete stores the empty word. -/
def delete (m : WordMap K V) (k : K) : WordMap K V :=
  fun k' => if k = k' then [] else m k'

/-- The empty map stores the empty word everywhere. -/
def empty : WordMap K V := fun _ => []

/-- `bindAlter` normalises through the denotation: it reads the net value, applies `f`,
and stores the result as a length-`≤ 1` word. -/
def bindAlter (f : K → V → Option V') (m : WordMap K V) : WordMap K V' :=
  fun k => ((m k).getLast?.bind (f k)).toList

/-- `merge` normalises through the denotation: it reads both net values, merges them, and
stores the result as a length-`≤ 1` word. -/
def merge (op : K → V → V → V) (m₁ m₂ : WordMap K V) : WordMap K V :=
  fun k => (Option.merge (op k) (m₁ k).getLast? (m₂ k).getLast?).toList

instance instPartialMap : PartialMap (WordMap K) K where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem getLast?_toList {o : Option V} : (o.toList).getLast? = o := by
  cases o <;> rfl

instance instLawfulPartialMap : LawfulPartialMap (WordMap K) K where
  get?_empty k := rfl
  get?_insert_eq h := by simp [PartialMap.get?, PartialMap.insert, get?, insert, h]
  get?_insert_ne h := by simp [PartialMap.get?, PartialMap.insert, get?, insert, h]
  get?_delete_eq h := by simp [PartialMap.get?, PartialMap.delete, get?, delete, h]
  get?_delete_ne h := by simp [PartialMap.get?, PartialMap.delete, get?, delete, h]
  get?_bindAlter := by simp [PartialMap.get?, PartialMap.bindAlter, get?, bindAlter]
  get?_merge := by simp [PartialMap.get?, PartialMap.merge, get?, merge]

/-! ## Non-extensionality

Two `WordMap`s that store different *words* but the same net (last) letter at every key
are pointwise equivalent yet unequal.  This is the defining property that distinguishes a
`WordMap` from the extensional function/`ExtTreeMap` instances. -/

/-- A reduced witness: every key stores the singleton `[v]`. -/
def reduced (v : V) : WordMap K V := fun _ => [v]

/-- An unreduced witness: every key stores the two-letter word `[w, v]`, whose net value
is still `v`. -/
def unreduced (w v : V) : WordMap K V := fun _ => [w, v]

theorem equiv_reduced_unreduced (w v : V) :
    PartialMap.equiv (reduced (K := K) v) (unreduced w v) := by
  intro k
  simp [PartialMap.get?, get?, reduced, unreduced]

/-- **Non-extensionality.** For any two distinct letters `w ≠ v` there are two `WordMap`s
that are pointwise equivalent (`PartialMap.equiv`) yet not equal: the reduced word `[v]`
and the unreduced word `[w, v]` denote the same map. -/
theorem nonextensional [Inhabited K] {w v : V} (h : w ≠ v) :
    ∃ m₁ m₂ : WordMap K V, PartialMap.equiv m₁ m₂ ∧ m₁ ≠ m₂ := by
  refine ⟨reduced v, unreduced w v, equiv_reduced_unreduced w v, ?_⟩
  intro heq
  have := congrFun heq (default : K)
  simp only [reduced, unreduced, List.cons.injEq] at this
  exact h this.1.symm

end WordMap

/-! ## Applicability: the HeapView CMRA over a `WordMap`

Because `get?` denotes into `K → Option V`, a `WordMap V` plugs into exactly the same
`HeapView F K V` resource-algebra construction (see `Iris.Algebra.HeapView`) used for the
other `PartialMap` instances: the authoritative element `Auth (.own one) m` owns the whole
heap and each `Frag k dq v` is a fragment asserting `k ↦ v` with discardable fraction `dq`.
The frame-preserving updates `~~>` in `HeapView` (`update_one_alloc`, `update_one_delete`,
`update_replace`, `update_of_local_update`, …) are all stated purely in terms of `get?`,
`insert`, and `delete`, so they transfer verbatim to `WordMap`.

What makes the *value monoid* interesting here is the intended instantiation of `V`:

* **`V := Multiset α`** is a commutative monoid under `⊎` (additive `+`), with unit `0`.
  As a unital CMRA its core is total and every element is shareable.  A `Frag k dq s`
  holding a multiset `s` can always be *grown* by any `t`: the local update
  `(s, s) ~l~> (s ⊎ t, s ⊎ t)` lifts via `update_of_local_update` to
  `Auth (.own one) m • Frag k dq s ~~> Auth (.own one) (insert m k (s ⊎ t)) • Frag k dq (s ⊎ t)`,
  modelling monotone accumulation (e.g. a multiset-valued ghost log) at a heap cell.

* **`V := FreeGroup α`** is a *group*: every element `g` is invertible.  Invertibility is
  the strongest possible setting for frame-preserving updates — the exclusive-fraction
  fragment `Frag k (.own one) g` may be *replaced* by an arbitrary valid `g'` via
  `update_replace`, giving
  `Auth (.own one) m • Frag k (.own one) g ~~> Auth (.own one) (insert m k g') • Frag k (.own one) g'`,
  and the net "word" reduction in the `WordMap` representation is exactly the free
  reduction in `FreeGroup α`.

In both cases the *non-extensionality* of `WordMap` is harmless for the CMRA: the
denotation `get?` is the only thing the resource algebra observes, so equivalent words are
identified by the logic while remaining distinct representations in the model. -/

end IrisMath.Instances
