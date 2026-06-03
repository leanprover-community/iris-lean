/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Tactic.Linter.Header
public import Iris

/-! # `HistoryMap`: a non-extensional `PartialMap` that is a per-cell *write log*

This file defines a `LawfulPartialMap` instance in which each key stores, instead of a
single value, the **entire chronological history of writes** to that cell — a `List V`
read as a stack of versions, newest on the right.  The observation `get?` reports only the
**current (latest) value**, i.e. the *last writer*:

  `get? : HistoryMap V → Nat → Option V := fun m k => (m k).getLast?`

`[]` means the cell was never written (absent / `none`); a nonempty list `[v₀, v₁, …, vₙ]`
means the cell currently holds `vₙ` but *remembers* the earlier versions `v₀ … vₙ₋₁`.
Two cells with different histories but the **same last writer** — e.g. `[a]` versus
`[b, a]` — are observationally indistinguishable through `get?`, yet are distinct Lean
values.  The representation is therefore genuinely **non-extensional**, and the
non-extensionality is *intrinsic*: the payload (`List V`) is strictly richer than
`Option V`, and `get?` (`getLast?`) genuinely forgets the prefix of the log.

## Order-theoretic reading

`List.getLast?` is the canonical *order-theoretic reduction* of a write log under the
"happens-before" order on indices: among all writes, observe the one that is **maximal in
time** (the most recent).  This is the temporal analogue of taking a join/sup, but it
requires **no order on `V`** — only the intrinsic order of the log positions — so the
instance stays fully polymorphic in `V` (see the *Applicability* section for the genuine
lattice/join story, which lives in the value CMRA, not here).

## Distinction from `WordMap`

`WordMap` observes the head/last *letter* of a single free *edit word* shared across the
whole map and quotients by a rewrite system.  `HistoryMap` is different in kind: the log is
**per cell**, there is **no quotient/rewrite** (distinct logs really are distinct values),
and the framing is a *version chain / audit trail* — the retained prefix is honest ghost
state that a CMRA can expose for rollback and time-travel invariants.

## Implementation

`HistoryMap V := Nat → List V`.  `[]` at a key means "absent".  Every constructive
operation produces a *singleton* log `[v]` for the new current value (or `[]` for delete),
so the seven laws reduce to facts about `List.getLast? [v] = some v` and `getLast? [] =
none`; non-extensionality is then witnessed by a length-2 log with the same last element as
a length-1 log.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

variable {V V' : Type _}

/-- A `HistoryMap` stores, at every key, the chronological *write log* (`List V`) of that
cell, newest write last.  `[]` means the cell is absent; a nonempty log means the cell
currently holds its last element and remembers the earlier versions. -/
def HistoryMap (V : Type _) : Type _ := Nat → List V

namespace HistoryMap

/-- The forgetful denotation: read back the **current (latest) value** — the last writer —
of the stored log at `k`.  `getLast?` forgets the entire prefix of the history. -/
def get? (m : HistoryMap V) (k : Nat) : Option V := (m k).getLast?

/-- Insert *pushes* a new write: it overwrites the cell's current log with the singleton
log `[v]`.  (A variant that genuinely appends — `m k ++ [v]` — has the same observation;
we use the singleton form so the laws are uniform with the other operations.) -/
def insert (m : HistoryMap V) (k : Nat) (v : V) : HistoryMap V :=
  fun k' => if k = k' then [v] else m k'

/-- Delete empties the cell's log entirely (`[]`), making it absent. -/
def delete (m : HistoryMap V) (k : Nat) : HistoryMap V :=
  fun k' => if k = k' then [] else m k'

/-- The empty map: every cell has an empty log. -/
def empty : HistoryMap V := fun _ => []

/-- `bindAlter` operates on the *current value* of each cell, collapsing the result to a
fresh singleton log. -/
def bindAlter (f : Nat → V → Option V') (m : HistoryMap V) : HistoryMap V' :=
  fun k => match (get? m k).bind (f k) with
    | none => []
    | some w => [w]

/-- `merge` combines the *current values* of two cells, collapsing the result to a fresh
singleton log. -/
def merge (op : Nat → V → V → V) (m₁ m₂ : HistoryMap V) : HistoryMap V :=
  fun k => match Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => []
    | some w => [w]

instance instPartialMap : PartialMap HistoryMap Nat where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : HistoryMap V) (k : Nat) :
    PartialMap.get? m k = (m k).getLast? := rfl

instance instLawfulPartialMap : LawfulPartialMap HistoryMap Nat where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, HistoryMap.insert, if_pos h, List.getLast?_singleton]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, HistoryMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, HistoryMap.delete, if_pos h, List.getLast?_nil]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, HistoryMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (HistoryMap.bindAlter f m k).getLast? = (HistoryMap.get? m k).bind (f k)
    unfold HistoryMap.bindAlter
    cases h : (HistoryMap.get? m k).bind (f k) <;> simp
  get?_merge {V op m₁ m₂ k} := by
    show (HistoryMap.merge op m₁ m₂ k).getLast?
      = Option.merge (op k) (HistoryMap.get? m₁ k) (HistoryMap.get? m₂ k)
    unfold HistoryMap.merge
    cases h : Option.merge (op k) (HistoryMap.get? m₁ k) (HistoryMap.get? m₂ k) <;> simp

/-! ## Non-extensionality

We exhibit two **distinct** `HistoryMap Nat` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but are not equal as Lean values.  The witness is a
single key whose two stored logs share the *same last writer* but differ in their history:
the length-1 log `[a]` and the length-2 log `[b, a]`.  Both have `getLast? = some a`, so
they denote "key `0` currently holds `a`", yet `[a] ≠ [b, a]` as lists, so the maps are
distinct. -/

/-- First witness: key `0` has the one-write history `[7]` (current value `7`). -/
def m_short : HistoryMap Nat := HistoryMap.insert HistoryMap.empty 0 7

/-- Second witness: key `0` has the two-write history `[3, 7]` (was `3`, now `7`).  Same
current value as `m_short`, different past. -/
def m_long : HistoryMap Nat := fun k => if k = 0 then [3, 7] else []

theorem getLast?_short : ((m_short : HistoryMap Nat) 0).getLast? = some 7 := by
  simp [m_short, HistoryMap.insert]

theorem getLast?_long : ((m_long : HistoryMap Nat) 0).getLast? = some 7 := by
  simp [m_long]

/-- **Non-extensionality.**  `m_short` and `m_long` are observationally equal
(`PartialMap.equiv`) — both denote "key `0` currently holds `7`, everything else absent" —
yet they are **distinct** Lean values, because the stored write logs (`[7]` versus `[3, 7]`)
differ in length / history.  This is impossible for any `ExtensionalPartialMap`, so
`HistoryMap` is genuinely non-extensional, and the distinction is *intrinsic*: the payload
records strictly more (the full version chain) than the observation `get? = getLast?`
exposes. -/
theorem nonextensional :
    PartialMap.equiv (M := HistoryMap) m_short m_long ∧ m_short ≠ m_long := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both give `some 7` at key 0, `none` elsewhere
    by_cases hk : k = 0
    · subst hk
      show ((m_short 0)).getLast? = ((m_long 0)).getLast?
      rw [getLast?_short, getLast?_long]
    · show ((m_short k)).getLast? = ((m_long k)).getLast?
      have hs : m_short k = [] := by
        simp [m_short, HistoryMap.insert, HistoryMap.empty, Ne.symm hk]
      have hl : m_long k = [] := by simp [m_long, hk]
      rw [hs, hl]
  · -- but distinct as Lean values: evaluate at key 0 and compare stored logs
    intro h
    have h0 : m_short 0 = m_long 0 := congrFun h 0
    have hs : m_short 0 = [7] := by simp [m_short, HistoryMap.insert]
    have hl : m_long 0 = [3, 7] := by simp [m_long]
    rw [hs, hl] at h0
    -- `[7] = [3, 7]` is false (different lengths)
    cases h0

/-- Consequently the `HistoryMap` instance is genuinely non-extensional: `equiv` does NOT
imply `=`.  (Contrast `ExtensionalPartialMap`, which the function / `ExtTreeMap` instances
satisfy.) -/
theorem not_extensionalPartialMap :
    ¬ ∀ {m₁ m₂ : HistoryMap Nat}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro h
  obtain ⟨heq, hne⟩ := nonextensional
  exact hne (h heq)

end HistoryMap

/-! ## Applicability: a `HeapView` CMRA over a versioned (write-log) heap

`HeapView` (`Iris/Iris/Algebra/HeapView.lean`) is parameterized by *any*
`LawfulPartialMap M K`; its authoritative/fragment construction and all frame-preserving
updates (`update_one_alloc`, `update_one_delete`, `update_of_local_update`,
`update_replace`, …) are stated **purely through `get?`/`insert`/`delete`/`merge`**, never
through term equality.  Hence `HistoryMap` instantiates `HeapView` directly:

  `HeapView F Nat V HistoryMap`  with  `H := HistoryMap` (this file) and `K := Nat`.

The authoritative `Auth (.own one) m` owns the whole versioned heap and `Frag k dq v` owns
a single cell's *current* value `v`; the view relation `HeapR` observes cells exactly
through `Std.PartialMap.get? = getLast?`, i.e. through their **current values only**.

### Why the write-log payload is interesting ghost state

The retained history is **honest ghost state invisible to the CMRA observation**, which is
precisely what makes it useful:

* **Audit / rollback invariants.**  A separation-logic predicate can be attached to the
  authoritative side asserting facts about the *full* log (e.g. "this cell was never `0`",
  "the value is monotone in time"), even though `Frag k dq v` only pins the current value.
  Replaying/rolling back to a previous version is a *local* rewrite of the prefix that the
  fragment cannot observe.
* **Finite-history modification is free.**  Any rewrite of the stored log that preserves
  its last element preserves `get?`, hence preserves `HeapR` verbatim for every frame —
  exactly the resource-algebra shadow of the `nonextensional` theorem above (`[7]` and
  `[3,7]` are interchangeable in the CMRA).

### The value lattice / join story (where an order on `V` *does* enter)

When the value type is a **join-semilattice** `V` (so values only ever *grow*), the natural
*value* CMRA is the join `(· ⊔ ·)`: it is commutative, associative, idempotent, and
**monotone**, so `v ~~> v ⊔ w` for any `w` — an update that can only increase the cell.
This order lives entirely in the *value* CMRA (the `V` slotted into `HeapView`), **not** in
this `PartialMap` instance, which stays polymorphic; the per-cell write log is the operational
witness of that monotone growth (each push is a new high-water mark).

### A concrete frame-preserving update

Replacing a cell's current value while leaving the fragment's recorded current value fixed
is the local update `(v, v) ~l~> (v, v)` lifted by `HeapView.update_of_local_update`.  More
to the point, the identity-on-observation update between two *distinct histories* is free:

  `Auth (.own one) m_short • Frag 0 (.own one) 7  ~~>  `
  `Auth (.own one) m_long  • Frag 0 (.own one) 7`,

because `get? m_short 0 = get? m_long 0 = some 7` (the histories `[7]` and `[3,7]` share a
last writer), so the `HeapR` view relation is preserved unchanged for every frame.  This is
an instance of `HeapView.update_replace` / `update_of_local_update`: the *finite
modification of the log* (prepending the historical write `3`) is invisible to the CMRA
precisely because the CMRA only sees the current value `getLast?`. -/

end IrisMath.Instances
