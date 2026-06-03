/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Iris

/-! # `IntervalConstraintMap`: constraint propagation as a non-extensional `PartialMap`

This file defines a `LawfulPartialMap` instance whose stored payload at each key is an
**interval of partial information** `Set.Icc lo hi` over an ordered value type `V` — the
proposition "the value is *known to lie* in `[lo, hi]`".  The observation `get?` reads back a
concrete value only once the constraints have *pinned* the cell to a **single point**
`Set.Icc v v = {v}`; any genuinely-wide interval (`Icc a b` with `a < b`, the whole space, …)
is still *uncertain* and observes as `none`, and the empty interval (`Icc lo hi` with
`lo ≰ hi`, i.e. `∅`) means *contradiction / no consistent value*.

## Abstract interpretation / interval narrowing as an owned, monotone resource

This is the resource-algebra shadow of **interval constraint propagation** (and, more
generally, abstract interpretation over the interval domain): each cell owns a *constraint*,
the observation is "has the constraint pinned the value yet?", and the only sound moves are

* **NARROW** — replace a cell's interval `I` by a sub-interval `I' ⊆ I` (constraint
  propagation: a new bound is intersected in).  This is *monotone* (information only
  increases) and **observation-CHANGING**: narrowing a wide `Icc a b` (`a < b`, reads `none`)
  down to the point `Icc a a = {a}` flips the observation `none ↦ some a`.  It is the genuine
  "the value just got determined" step, not an invisible rewrite.

* **MERGE** (`⊓` = intersection) — combine two parties' constraints at a key by intersecting
  their intervals: `Icc a b ∩ Icc c d = Icc (a ⊔ c) (b ⊓ d)`.  The intervals form a
  **meet-semilattice under `∩`**; meet = pooling information.  This is the CRDT/monotone
  structure of the resource: two owners' partial knowledge join to a sharper constraint.

The forgetful projection collapses every non-point interval to `none`, so the cell *forgets
everything about the value except whether it is pinned* — exactly the non-extensionality.

## The rich payload is a meet-semilattice, not a list endpoint

The payload is a genuine `Set V` (the interval), ordered by **inclusion = information
refinement** (`I ⊇ I'` means "`I'` is the sharper constraint").  This is REAL ORDER THEORY,
not a list/endpoint trick and not a `(extra × V)` ghost projection: the cell is an honest
order object (an interval in the powerset lattice of `V`) and the readout `pin` is its
"is-this-pinned-to-a-point?" denotation, which is *not injective*.

## Implementation

`IntervalConstraintMap V := K → Set V`, with the constructive operations storing point
intervals `Set.Icc v v` (= `{v}`) or the empty interval `∅`.  `get? m k = pin (m k)`, where
`pin s = some v` iff `s = {v}`.  `insert`/`bindAlter`/`merge` *observe* via `get?`, combine,
and store the result back as a point interval / `∅`, so `pin` commutes definitionally with the
seven laws.  Non-extensionality is precisely the non-injectivity of `pin`: many distinct wide
intervals share the observation `none`.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

variable {K V V' : Type _}

/-! ## The pin readout `pin` -/

open Classical in
/-- The forgetful **pin readout**: read back the value a constraint interval has been narrowed
down to.  `some v` exactly when the interval is the single point `{v}` (the constraints have
*pinned* the value); otherwise (a wide interval `Icc a b` with `a < b`, the whole space, or the
empty/contradictory interval) the value is still uncertain or impossible, so the observation is
`none`.  This is `V`-natural and **not injective** — every wide interval shares `none`. -/
noncomputable def pin (s : Set V) : Option V :=
  if h : ∃ v, s = {v} then some h.choose else none

/-- The pinned (point) constraint `{v}` reads back `v`. -/
@[simp] theorem pin_singleton (v : V) : pin ({v} : Set V) = some v := by
  have hex : ∃ w, ({v} : Set V) = {w} := ⟨v, rfl⟩
  rw [pin, dif_pos hex]
  have hspec : ({v} : Set V) = {hex.choose} := hex.choose_spec
  exact congrArg some (_root_.Set.singleton_eq_singleton_iff.mp hspec.symm)

/-- A point interval `Set.Icc v v` is pinned to `v`. -/
@[simp] theorem pin_Icc_self [PartialOrder V] (v : V) : pin (Set.Icc v v) = some v := by
  rw [Set.Icc_self]; exact pin_singleton v

/-- The empty (contradictory) constraint `∅` is unpinned. -/
@[simp] theorem pin_empty : pin (∅ : Set V) = none := by
  rw [pin, dif_neg]
  rintro ⟨v, hv⟩
  exact absurd (hv ▸ rfl : v ∈ (∅ : Set V)) (Set.notMem_empty v)

/-! ## The carrier and operations -/

/-- An `IntervalConstraintMap` stores an **interval of partial information** `Set V` at every
key: the set of values still consistent with the accumulated constraints.  `∅` = contradictory,
`{v}` (a point interval) = pinned to `v`, a wider interval = still uncertain. -/
def IntervalConstraintMap (V : Type _) : Type _ := K → Set V

namespace IntervalConstraintMap

variable [∀ V, PartialOrder V]

/-- Store an `Option V` back as a constraint: `none ↦ ∅` (contradiction), `some v ↦ Set.Icc v v`
(the point interval pinning `v`). -/
def store (o : Option V) : Set V := o.elim ∅ (fun v => Set.Icc v v)

@[simp] theorem store_none : store (none : Option V) = (∅ : Set V) := rfl
@[simp] theorem store_some (v : V) : store (some v) = Set.Icc v v := rfl

/-- The readout undoes the storage: reading back the constraint stored from `o` recovers `o`. -/
@[simp] theorem pin_store (o : Option V) : pin (store o) = o := by
  cases o with
  | none => simp
  | some v => simp

/-- The forgetful observation: read back the pinned value of the constraint at `k`. -/
noncomputable def get? (m : IntervalConstraintMap (K := K) V) (k : K) : Option V := pin (m k)

/-- `insert` records *full knowledge* — the point interval `Set.Icc v v` — at `k`. -/
def insert [DecidableEq K] (m : IntervalConstraintMap (K := K) V) (k : K)
    (v : V) : IntervalConstraintMap (K := K) V :=
  fun k' => if k = k' then Set.Icc v v else m k'

/-- `delete` records *contradiction* `∅` at `k`. -/
def delete [DecidableEq K] (m : IntervalConstraintMap (K := K) V) (k : K) :
    IntervalConstraintMap (K := K) V :=
  fun k' => if k = k' then ∅ else m k'

/-- The empty map: every key contradictory (`∅`). -/
def empty : IntervalConstraintMap (K := K) V := fun _ => ∅

/-- `bindAlter` *observes* the pinned value at each key, applies `f`, and stores the result
back as a constraint. -/
noncomputable def bindAlter (f : K → V → Option V')
    (m : IntervalConstraintMap (K := K) V) : IntervalConstraintMap (K := K) V' :=
  fun k => store ((get? m k).bind (f k))

/-- `merge` observes the pinned values of both maps, combines via `op`, and stores back. -/
noncomputable def merge (op : K → V → V → V)
    (m₁ m₂ : IntervalConstraintMap (K := K) V) : IntervalConstraintMap (K := K) V :=
  fun k => store (Option.merge (op k) (get? m₁ k) (get? m₂ k))

noncomputable instance instPartialMap [DecidableEq K] :
    PartialMap (IntervalConstraintMap (K := K)) K where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq [DecidableEq K]
    (m : IntervalConstraintMap (K := K) V) (k : K) :
    PartialMap.get? m k = pin (m k) := rfl

noncomputable instance instLawfulPartialMap [DecidableEq K] :
    LawfulPartialMap (IntervalConstraintMap (K := K)) K where
  get?_empty k := by change pin (empty k) = none; simp [empty]
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, IntervalConstraintMap.insert, if_pos h, pin_Icc_self]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, IntervalConstraintMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, IntervalConstraintMap.delete, if_pos h, pin_empty]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, IntervalConstraintMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    change pin (IntervalConstraintMap.bindAlter f m k) = (get? m k).bind (f k)
    simp only [IntervalConstraintMap.bindAlter, pin_store]
  get?_merge {V op m₁ m₂ k} := by
    change pin (IntervalConstraintMap.merge op m₁ m₂ k)
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    simp only [IntervalConstraintMap.merge, pin_store]

/-! ## Non-extensionality

We exhibit two **distinct** constraint intervals at the same key that observe as the *same*
`get?` (`PartialMap.equiv`) yet are unequal Lean values.  The witnesses are two genuinely
different *uncertain* intervals over `ℕ`: the wide interval `Set.Icc 0 1` (the value is known to
lie in `[0,1]`) and the wider interval `Set.Icc 0 2` (known to lie in `[0,2]`).  Neither is a
single point, so `pin` collapses both to `none` — but as intervals they differ (e.g. `2` lies
in the second but not the first).  This is impossible for any `ExtensionalPartialMap`, and the
forgetfulness is *meaningful*: the constraint cell forgets everything about the value except
whether it is pinned. -/

section NonExtensional

variable [DecidableEq K]

omit [∀ V, PartialOrder V] in
/-- `pin` collapses every interval containing two distinct points to `none`: such an interval is
not a singleton. -/
theorem pin_eq_none_of_two {s : Set V} {a b : V} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    pin s = none := by
  rw [pin, dif_neg]
  rintro ⟨v, rfl⟩
  rw [_root_.Set.mem_singleton_iff] at ha hb
  exact hab (ha.trans hb.symm)

omit [∀ V, PartialOrder V] in
/-- A nondegenerate interval `Set.Icc a b` with `a < b` is unpinned: it contains both endpoints,
which are distinct. -/
theorem pin_Icc_eq_none [PartialOrder V] {a b : V} (hab : a < b) :
    pin (Set.Icc a b) = none :=
  pin_eq_none_of_two (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) (ne_of_lt hab)

/-- First witness: key `k₀` stores the constraint `Set.Icc 0 1` ("value lies in `[0,1]`"). -/
noncomputable def m_Icc01 (k₀ : K) : IntervalConstraintMap (K := K) ℕ :=
  fun k => if k = k₀ then Set.Icc 0 1 else ∅

/-- Second witness: key `k₀` stores the wider constraint `Set.Icc 0 2` ("value lies in
`[0,2]`"). -/
noncomputable def m_Icc02 (k₀ : K) : IntervalConstraintMap (K := K) ℕ :=
  fun k => if k = k₀ then Set.Icc 0 2 else ∅

/-- **Non-extensionality.**  `m_Icc01 k₀` and `m_Icc02 k₀` are observationally equal
(`PartialMap.equiv`) — at `k₀` both constraints are nondegenerate intervals (`0 < 1`, `0 < 2`),
so `pin` gives `none`, and elsewhere both are `∅` — yet they are **distinct** Lean values, since
`2 ∈ Set.Icc 0 2` while `2 ∉ Set.Icc 0 1`.  This is impossible for any `ExtensionalPartialMap`:
the constraint cell forgets the *width* of the interval and remembers only whether it is
pinned. -/
theorem nonextensional (k₀ : K) :
    PartialMap.equiv (M := IntervalConstraintMap (K := K)) (m_Icc01 k₀) (m_Icc02 k₀) ∧
      m_Icc01 k₀ ≠ m_Icc02 k₀ := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both intervals are nondegenerate at `k₀`, `∅` elsewhere
    change pin (m_Icc01 k₀ k) = pin (m_Icc02 k₀ k)
    by_cases hk : k = k₀
    · subst hk
      have h1 : m_Icc01 (K := K) k k = (Set.Icc 0 1 : Set ℕ) := by simp [m_Icc01]
      have h2 : m_Icc02 (K := K) k k = (Set.Icc 0 2 : Set ℕ) := by simp [m_Icc02]
      have e1 : pin (Set.Icc 0 1 : Set ℕ) = none :=
        pin_eq_none_of_two (Set.mem_Icc.mpr ⟨by decide, by decide⟩)
          (Set.mem_Icc.mpr ⟨by decide, by decide⟩) (by decide : (0 : ℕ) ≠ 1)
      have e2 : pin (Set.Icc 0 2 : Set ℕ) = none :=
        pin_eq_none_of_two (Set.mem_Icc.mpr ⟨by decide, by decide⟩)
          (Set.mem_Icc.mpr ⟨by decide, by decide⟩) (by decide : (0 : ℕ) ≠ 2)
      rw [h1, h2, e1, e2]
    · simp only [m_Icc01, m_Icc02, if_neg hk]
  · -- but distinct as Lean values: the intervals at `k₀` differ at the point `2`
    intro h
    have hk0 : m_Icc01 (K := K) k₀ k₀ = m_Icc02 k₀ k₀ := congrFun h k₀
    have h1 : m_Icc01 (K := K) k₀ k₀ = (Set.Icc 0 1 : Set ℕ) := by simp [m_Icc01]
    have h2 : m_Icc02 (K := K) k₀ k₀ = (Set.Icc 0 2 : Set ℕ) := by simp [m_Icc02]
    rw [h1, h2] at hk0
    have hmem : (2 : ℕ) ∈ (Set.Icc 0 1 : Set ℕ) :=
      hk0 ▸ Set.mem_Icc.mpr ⟨by decide, by decide⟩
    rw [Set.mem_Icc] at hmem
    exact absurd hmem.2 (by decide)

/-- Consequently the `IntervalConstraintMap` instance is genuinely non-extensional: `equiv` does
NOT imply `=`. -/
theorem not_extensionalPartialMap [Nonempty K] :
    ¬ ∀ {m₁ m₂ : IntervalConstraintMap (K := K) ℕ},
      PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro hext
  obtain ⟨k₀⟩ : Nonempty K := ‹Nonempty K›
  obtain ⟨heq, hne⟩ := nonextensional (K := K) k₀
  exact hne (hext heq)

end NonExtensional

/-! ## Applicability: NARROW and MERGE over a `HeapView` CMRA

`HeapView F K V H` (`Iris/Iris/Algebra/HeapView.lean`) is parameterized by *any*
`LawfulPartialMap H K`; its authoritative/fragment construction and all frame-preserving
updates (`update_one_alloc`, `update_one_delete`, `update_of_local_update`, `update_replace`,
…) are stated purely through `Std.PartialMap.get?`/`insert`/`delete`/`merge`, never through
representation equality.  Hence `IntervalConstraintMap` instantiates `HeapView` directly,
giving a heap whose cells store *interval constraints* rather than fixed values.

### NARROW: the observation-CHANGING update (`I' ⊆ I`)

The constraints form a **meet-semilattice under `∩`** (intersecting intervals pools
information), and `I ⊇ I'` is the *information-refinement order* ("`I'` is the sharper
constraint").  This exposes a structurally new frame-preserving move unavailable to extensional
maps or `List`-endpoint instances:

  **NARROW: replace a cell's interval `I` at `k` by a sub-interval `I' ⊆ I`.**

Narrowing can turn an *uncertain* cell (`pin I = none`) into a *pinned* one
(`pin I' = some v`) — collapsing `Icc a b` (`a < b`) down to the point `Icc a a = {a}` flips the
observation from `none` to `some a`.  In `HeapView` terms this is an `insert`-style update at `k`
realized by `HeapView.update_replace` / `HeapView.update_of_local_update`: the *observation*
changes from `none` to `some a` while the stored interval is replaced by its sub-interval.
This is constraint propagation's "the value just got determined" step — a genuine
observation-changing move, not an invisible rewrite.

### MERGE (`⊓` = intersection)

Combining two parties' constraints at a key is interval intersection
`Icc a b ∩ Icc c d = Icc (a ⊔ c) (b ⊓ d)`; informally `obs k I₁ , obs k I₂ ⊢ obs k (I₁ ∩ I₂)`.
The meet-semilattice of intervals under `∩` is the CRDT/monotone structure: two owners' partial
knowledge joins to a sharper constraint.

The next lemmas are the concrete, machine-checked content. -/

section Applicability

variable [DecidableEq K]

/-- Store the nondegenerate constraint `Set.Icc a b` at `k₀`, `∅` elsewhere. -/
noncomputable def cell_Icc (k₀ : K) (a b : V) :
    IntervalConstraintMap (K := K) V :=
  fun k => if k = k₀ then Set.Icc a b else ∅

/-- **NARROW changes the observation.**  The uncertain constraint `Set.Icc a b` (with `a < b`)
observes as `none` at `k₀`; narrowing it to the point sub-interval `Set.Icc a a = {a}` (obtained
by `insert`) observes as `some a`.  This `none ↦ some a` transition under the inclusion
`Set.Icc a a ⊆ Set.Icc a b` is the genuinely new, observation-CHANGING "narrow the constraint"
update of interval constraint propagation; it has no counterpart in extensional or
`List`-endpoint partial maps. -/
theorem narrow_pins {k₀ : K} {a b : V} (hab : a < b) :
    PartialMap.get? (M := IntervalConstraintMap (K := K)) (cell_Icc k₀ a b) k₀ = none ∧
      PartialMap.get? (M := IntervalConstraintMap (K := K))
        (PartialMap.insert (cell_Icc k₀ a b) k₀ a) k₀ = some a := by
  refine ⟨?_, ?_⟩
  · change pin (cell_Icc k₀ a b k₀) = none
    have hc : cell_Icc k₀ a b k₀ = (Set.Icc a b : Set V) := by simp [cell_Icc]
    rw [hc]; exact pin_Icc_eq_none hab
  · exact get?_insert_eq rfl

end Applicability

end IntervalConstraintMap

/-! ## The meet-semilattice of intervals (order theory of MERGE / NARROW)

These pure order-theoretic facts about interval intersection live *outside* the
`[∀ V, PartialOrder V]`-parameterized instance namespace so they can use a genuine `[Lattice V]`
(and `ℕ`'s real order) without the instance diamond. -/

/-- The narrowed interval `Set.Icc a a ⊆ Set.Icc a b` is a **meet** in the information
semilattice: the point interval is the intersection of the wide interval with the new (tighter)
upper-bound constraint `Set.Icc a a`.  Narrowing = intersecting with new information. -/
theorem narrow_is_meet [Lattice V] (a b : V) (hab : a ≤ b) :
    Set.Icc a a = Set.Icc a b ∩ Set.Icc a a := by
  rw [Set.Icc_inter_Icc, sup_idem, inf_eq_right.mpr hab]

/-- **MERGE = interval intersection.**  In a `LinearOrder` (in fact any lattice), intersecting
two constraint intervals at a key gives the interval whose endpoints are the *max of the lower
bounds* and the *min of the upper bounds* — the pooled, sharper constraint.  This is the
meet-semilattice operation underlying the CRDT/monotone MERGE: two owners' partial knowledge
joins to `obs k (I₁ ∩ I₂)`. -/
theorem merge_is_inter [Lattice V] (a b c d : V) :
    Set.Icc a b ∩ Set.Icc c d = Set.Icc (a ⊔ c) (b ⊓ d) :=
  Set.Icc_inter_Icc

/-- MERGE can pin: intersecting two genuinely-uncertain constraints can yield a point interval.
Neither `Set.Icc 0 2` nor a wide neighbour alone is pinned, yet their intersection collapses to a
single point precisely when the upper bound of one meets the lower bound of the other.
Concretely `Icc 0 2 ∩ Icc 1 1 = Icc 1 1`, pooling two parties' bounds to *determine* the
value `1`. -/
theorem merge_pins_example :
    pin (Set.Icc (0 : ℕ) 2 ∩ Set.Icc 1 1) = some 1 := by
  rw [merge_is_inter, show (0 : ℕ) ⊔ 1 = 1 from by decide, show (2 : ℕ) ⊓ 1 = 1 from by decide,
    pin_Icc_self]

end IrisMath.Instances
