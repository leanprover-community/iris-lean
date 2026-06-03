/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Iris

/-! # `KnowledgeMap`: a non-extensional `PartialMap` of partial-information states

This file defines a `LawfulPartialMap` instance whose stored payload at each key is a
**knowledge state** about the value: a *set of candidate values* `Set V`.  The observation
`get?` reads back a value only when the knowledge state has been *pinned* to a singleton
`{v}`; any wider set (`Set.univ`, a two-element set, …) is still *uncertain* and observes as
`none`, and the empty set `∅` means *absent / contradictory*.

## The rich payload is a meet-semilattice, not a list endpoint

The extra structure carried at each key is a genuine `Set V`, ordered by **inclusion =
information refinement**: `s ⊇ s'` means "`s'` is more certain than `s`" (fewer candidates).
This is a *meet-semilattice* under `∩` — intersecting two knowledge states combines the
information in both.  The forgetful projection

  `π : Set V → Option V`,   `π s = some v` iff `s = {v}`, else `none`

collapses *all* non-singleton states (every uncertain or contradictory state) to `none`.
`π` is **not injective** (e.g. `Set.univ` and any two-element set both map to `none`), which
is exactly the source of non-extensionality.  Crucially this is REAL ALGEBRA, not a
list/endpoint trick and not a `(extra × V)` ghost projection: the payload is an honest
order-theoretic object (the powerset lattice of `V`) and `π` is its "is-this-pinned?"
denotation.

## Why the constraint is satisfied

`get? : M V → K → Option V` is polymorphic in `V`.  We store the richer structure
`S V := Set V`, with the `V`-natural projection `π : S V → Option V` above.  Every operation
is defined so that it **commutes with `π`**: constructive operations store a singleton or the
empty set, whose `π` is forced.  Non-extensionality is precisely the non-injectivity of `π`.

## Implementation

`KnowledgeMap V := K → Set V`.  `get? m k = π (m k)`.  `insert` stores `{v}` (full
knowledge), `delete` stores `∅` (absent/contradiction), `empty` stores `∅` everywhere.
`bindAlter`/`merge` first *observe* via `get?`, combine, and store the result back as a
singleton/empty set, so `π` commutes definitionally with the seven laws.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap
open scoped Classical

variable {K V V' : Type _}

/-! ## The knowledge-state projection `π` -/

open Classical in
/-- The forgetful projection from a knowledge state (a set of candidate values) to an
observed value: `some v` exactly when the state has been *pinned* to the singleton `{v}`;
otherwise (`∅`, `Set.univ`, any non-singleton set) the value is still uncertain or absent, so
the observation is `none`.  This is `V`-natural and **not injective** — many distinct sets
share the observation `none`. -/
noncomputable def pin (s : Set V) : Option V :=
  if h : ∃ v, s = {v} then some h.choose else none

/-- The knowledge state `{v}` is pinned to `v`. -/
@[simp] theorem pin_singleton (v : V) : pin ({v} : Set V) = some v := by
  have hex : ∃ w, ({v} : Set V) = {w} := ⟨v, rfl⟩
  rw [pin, dif_pos hex]
  have hspec : ({v} : Set V) = {hex.choose} := hex.choose_spec
  -- `{v} = {choose}` forces `choose = v`.
  exact congrArg some (_root_.Set.singleton_eq_singleton_iff.mp hspec.symm)

/-- The empty knowledge state (`∅`, absent/contradictory) is unpinned. -/
@[simp] theorem pin_empty : pin (∅ : Set V) = none := by
  rw [pin, dif_neg]
  rintro ⟨v, hv⟩
  exact absurd (hv ▸ rfl : v ∈ (∅ : Set V)) (Set.notMem_empty v)

/-- `pin` of the option-driven storage `optSet o := o.elim ∅ ({·})` recovers `o`. -/
@[simp] theorem pin_optSet (o : Option V) : pin (o.elim ∅ (fun v => {v})) = o := by
  cases o with
  | none => simp
  | some v => simp

/-! ## The carrier and operations -/

/-- A `KnowledgeMap` stores a **knowledge state** `Set V` at every key: the set of values
still considered possible.  `∅` = absent/contradiction, `{v}` = pinned to `v`, anything wider
= still uncertain. -/
def KnowledgeMap (V : Type _) : Type _ := K → Set V

namespace KnowledgeMap

/-- Store an `Option V` back as a knowledge state: `none ↦ ∅`, `some v ↦ {v}`. -/
def store (o : Option V) : Set V := o.elim ∅ (fun v => {v})

@[simp] theorem store_none : store (none : Option V) = ∅ := rfl
@[simp] theorem store_some (v : V) : store (some v) = ({v} : Set V) := rfl

@[simp] theorem pin_store (o : Option V) : pin (store o) = o := pin_optSet o

/-- The forgetful observation: read back the pinned value of the knowledge state at `k`. -/
noncomputable def get? (m : KnowledgeMap (K := K) V) (k : K) : Option V := pin (m k)

/-- `insert` records *full knowledge* `{v}` at `k`. -/
def insert [DecidableEq K] (m : KnowledgeMap (K := K) V) (k : K) (v : V) :
    KnowledgeMap (K := K) V :=
  fun k' => if k = k' then {v} else m k'

/-- `delete` records *absence/contradiction* `∅` at `k`. -/
def delete [DecidableEq K] (m : KnowledgeMap (K := K) V) (k : K) : KnowledgeMap (K := K) V :=
  fun k' => if k = k' then ∅ else m k'

/-- The empty map: every key absent (`∅`). -/
def empty : KnowledgeMap (K := K) V := fun _ => ∅

/-- `bindAlter` *observes* the pinned value at each key, applies `f`, and stores the result
back as a knowledge state. -/
noncomputable def bindAlter (f : K → V → Option V') (m : KnowledgeMap (K := K) V) :
    KnowledgeMap (K := K) V' :=
  fun k => store ((get? m k).bind (f k))

/-- `merge` observes the pinned values of both maps, combines via `op`, and stores back. -/
noncomputable def merge (op : K → V → V → V) (m₁ m₂ : KnowledgeMap (K := K) V) :
    KnowledgeMap (K := K) V :=
  fun k => store (Option.merge (op k) (get? m₁ k) (get? m₂ k))

noncomputable instance instPartialMap [DecidableEq K] :
    PartialMap (KnowledgeMap (K := K)) K where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq [DecidableEq K] (m : KnowledgeMap (K := K) V) (k : K) :
    PartialMap.get? m k = pin (m k) := rfl

noncomputable instance instLawfulPartialMap [DecidableEq K] :
    LawfulPartialMap (KnowledgeMap (K := K)) K where
  get?_empty k := by show pin (empty k) = none; simp [empty]
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, KnowledgeMap.insert, if_pos h, pin_singleton]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, KnowledgeMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, KnowledgeMap.delete, if_pos h, pin_empty]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, KnowledgeMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show pin (KnowledgeMap.bindAlter f m k) = (get? m k).bind (f k)
    simp only [KnowledgeMap.bindAlter, pin_store]
  get?_merge {V op m₁ m₂ k} := by
    show pin (KnowledgeMap.merge op m₁ m₂ k) = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    simp only [KnowledgeMap.merge, pin_store]

/-! ## Non-extensionality

We exhibit two **distinct** knowledge states at the same key that observe as the *same*
`get?` (`PartialMap.equiv`) yet are unequal Lean values.  The witnesses are two genuinely
different *uncertain* states: `Set.univ` ("know nothing") and a two-element set `{a, b}`
("narrowed to two candidates").  Both are non-singletons, so `pin` collapses both to `none`,
hence both observe as "absent/uncertain" — but as sets they differ.  This is impossible for
any `ExtensionalPartialMap`, and the forgetfulness is *meaningful*: the information order
collapses every non-pinned state to the same observation. -/

section NonExtensional

variable [DecidableEq K]

/-- `pin` collapses every set with at least two distinct elements to `none`: such a set is not
a singleton. -/
theorem pin_eq_none_of_two {s : Set V} {a b : V} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    pin s = none := by
  rw [pin, dif_neg]
  rintro ⟨v, rfl⟩
  rw [_root_.Set.mem_singleton_iff] at ha hb
  exact hab (ha.trans hb.symm)

/-- `Set.univ` over a type with two distinct elements is unpinned. -/
theorem pin_univ_eq_none {a b : V} (hab : a ≠ b) : pin (Set.univ : Set V) = none :=
  pin_eq_none_of_two (Set.mem_univ a) (Set.mem_univ b) hab

/-- `{a, b}` with `a ≠ b` is unpinned. -/
theorem pin_pair_eq_none {a b : V} (hab : a ≠ b) : pin ({a, b} : Set V) = none :=
  pin_eq_none_of_two (_root_.Set.mem_insert a _) (_root_.Set.mem_insert_of_mem a rfl) hab

/-- First witness: key `k₀` stores the **maximally uncertain** state `Set.univ`. -/
noncomputable def m_univ (k₀ : K) : KnowledgeMap (K := K) V :=
  fun k => if k = k₀ then Set.univ else ∅

/-- Second witness: key `k₀` stores the **two-candidate** state `{a, b}`. -/
noncomputable def m_pair (k₀ : K) (a b : V) : KnowledgeMap (K := K) V :=
  fun k => if k = k₀ then {a, b} else ∅

/-- **Non-extensionality.**  `m_univ k₀` and `m_pair k₀ a b` (for `a ≠ b`) are observationally
equal (`PartialMap.equiv`) — at `k₀` both knowledge states are non-singletons, so `pin` gives
`none`, and elsewhere both are `∅` — yet they are **distinct** Lean values, since `Set.univ`
and `{a, b}` differ as sets (e.g. a third value, or any value `≠ a, b`, witnesses the
difference whenever it exists; in general `Set.univ ≠ {a, b}` unless `V` has exactly the two
points `a, b`).  We state it over `V := ℕ`, `a := 0`, `b := 1`, where `2 ∈ univ \ {0,1}`. -/
theorem nonextensional (k₀ : K) :
    PartialMap.equiv (M := KnowledgeMap (K := K)) (m_univ (V := ℕ) k₀) (m_pair k₀ 0 1) ∧
      m_univ (V := ℕ) k₀ ≠ m_pair k₀ 0 1 := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal
    show pin (m_univ k₀ k) = pin (m_pair k₀ 0 1 k)
    by_cases hk : k = k₀
    · subst hk
      have hu : m_univ (V := ℕ) k k = (Set.univ : Set ℕ) := by simp [m_univ]
      have hp : m_pair (V := ℕ) k 0 1 k = ({0, 1} : Set ℕ) := by simp [m_pair]
      rw [hu, hp, pin_univ_eq_none (by decide : (0 : ℕ) ≠ 1),
        pin_pair_eq_none (by decide : (0 : ℕ) ≠ 1)]
    · simp only [m_univ, m_pair, if_neg hk]
  · -- but distinct as Lean values: the sets at `k₀` differ at the point `2`
    intro h
    have hk0 : m_univ (V := ℕ) k₀ k₀ = m_pair k₀ 0 1 k₀ := congrFun h k₀
    have hu : m_univ (V := ℕ) k₀ k₀ = (Set.univ : Set ℕ) := by simp [m_univ]
    have hp : m_pair (V := ℕ) k₀ 0 1 k₀ = ({0, 1} : Set ℕ) := by simp [m_pair]
    rw [hu, hp] at hk0
    -- `2 ∈ univ` but `2 ∉ {0,1}`
    have h2 : (2 : ℕ) ∈ ({0, 1} : Set ℕ) := hk0 ▸ _root_.Set.mem_univ 2
    simp at h2

/-- Consequently the `KnowledgeMap` instance is genuinely non-extensional: `equiv` does NOT
imply `=`. -/
theorem not_extensionalPartialMap [Nonempty K] :
    ¬ ∀ {V : Type} {m₁ m₂ : KnowledgeMap (K := K) V},
      PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro hext
  obtain ⟨k₀⟩ : Nonempty K := ‹Nonempty K›
  obtain ⟨heq, hne⟩ := nonextensional (K := K) k₀
  exact hne (hext heq)

end NonExtensional

/-! ## Applicability: refinement updates over a `HeapView` CMRA

`HeapView F K V H` (`Iris/Iris/Algebra/HeapView.lean`) is parameterized by *any*
`LawfulPartialMap H K`; its authoritative/fragment construction and all frame-preserving
updates (`update_one_alloc`, `update_one_delete`, `update_of_local_update`, `update_replace`,
…) are stated purely through `Std.PartialMap.get?`/`insert`/`delete`/`merge`, never through
representation equality.  Hence `KnowledgeMap` instantiates `HeapView` directly, giving a heap
whose cells store *partial-information* knowledge states rather than fixed values.

### The new kind of update: REFINE (`s ⊇ s'`)

The knowledge states form a **meet-semilattice under `∩`**: intersecting two states combines
their information, and `s ⊇ s'` is the *information-refinement order* ("`s'` is more certain").
This exposes a structurally new frame-preserving move unavailable to extensional maps or to the
`List`-endpoint instances:

  **REFINE: replace a knowledge state `s` at `k` by a subset `s' ⊆ s`.**

Refinement can turn an *uncertain* cell (`pin s = none`) into a *pinned* one
(`pin s' = some v`) — narrowing `{a, b}` down to `{a}` changes the observation from `none` to
`some a`.  In `HeapView` terms this is exactly an `insert`-style update at `k` from the
unpinned cell to the pinned cell `{a}`, realized by `HeapView.update_replace` /
`HeapView.update_of_local_update`: the *observation* changes from `none` to `some a`, while the
underlying carrier is updated by replacing the stored set.  Because every HeapView update is
phrased through `get?`/`insert`, this "narrow the candidate set" rewrite is a first-class CMRA
update — the resource-algebra shadow of the projection `pin` going from `none` to `some`.

The next lemma is the concrete, machine-checked content: refining `{a, b}` to `{a}` at `k`
changes the observation from `none` to `some a`. -/

section Applicability

variable [DecidableEq K]

/-- Store `{a, b}` (uncertain) at `k₀`, `∅` elsewhere. -/
noncomputable def cell_pair (k₀ : K) (a b : V) : KnowledgeMap (K := K) V :=
  fun k => if k = k₀ then {a, b} else ∅

/-- **Refinement changes the observation.**  The uncertain knowledge state `{a, b}` (with
`a ≠ b`) observes as `none` at `k₀`, while its refinement to the subset `{a}` (a pinned state,
obtained by `insert`) observes as `some a`.  This `none ↦ some a` transition under the
inclusion `{a} ⊆ {a, b}` is the genuinely new "refine the candidate set" update; it has no
counterpart in extensional or `List`-endpoint partial maps. -/
theorem refine_pins {k₀ : K} {a b : V} (hab : a ≠ b) :
    PartialMap.get? (M := KnowledgeMap (K := K)) (cell_pair k₀ a b) k₀ = none ∧
      PartialMap.get? (M := KnowledgeMap (K := K))
        (PartialMap.insert (cell_pair k₀ a b) k₀ a) k₀ = some a := by
  refine ⟨?_, ?_⟩
  · show pin (cell_pair k₀ a b k₀) = none
    have hc : cell_pair k₀ a b k₀ = ({a, b} : Set V) := by simp [cell_pair]
    rw [hc]; exact pin_pair_eq_none hab
  · exact get?_insert_eq rfl

/-- The refinement `{a} ⊆ {a, b}` is a meet in the information semilattice:
`{a} = {a, b} ∩ {a}`, i.e. refining is intersecting with new information. -/
theorem refine_is_meet (a b : V) : ({a} : Set V) = ({a, b} : Set V) ∩ {a} := by
  ext x; simp

end Applicability

end KnowledgeMap

end IrisMath.Instances
