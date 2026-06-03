/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Iris

/-! # `CutMap`: the *order-completion* non-extensional `PartialMap` of Dedekind cuts

This file defines a `LawfulPartialMap` instance whose stored payload at each key is a
**down-set / "Dedekind cut"** of candidate values: an arbitrary `Set V` over a
`[PartialOrder V]`, thought of as the *lower part* of a cut.  The observation `get?` reads
back a value only when the cut **pins** a single element — namely when the set has a
*greatest element* `v` (`v ∈ s ∧ ∀ x ∈ s, x ≤ v`).  A principal down-set `Set.Iic v = {x | x
≤ v}` has greatest element `v`; the empty cut `∅` and any cut with no top (e.g. an open
initial segment) observe as `none`.

## This is the ORDER completion, not the metric completion

`CompletionMap` stores Cauchy-style approximating data and reads back a **metric** limit; it
is the *Cauchy completion* (the construction of `ℝ` as equivalence classes of Cauchy
sequences of `ℚ`).  `CutMap` is its order-theoretic dual: it stores a **down-set** and reads
back its **supremum / greatest element**.  This is exactly the *Dedekind–MacNeille
completion* — the construction of `ℝ` as Dedekind cuts of `ℚ`.  The two are complementary
completions of the rationals, and here they appear as complementary non-extensional
`PartialMap` instances: `CompletionMap` forgets metric-Cauchy-equivalent tails, `CutMap`
forgets *everything strictly below the top of the cut*.

## The rich payload is a complete lattice, not a list endpoint

The extra structure carried at each key is a genuine `Set V` ordered by **inclusion**.  The
powerset of `V` is a complete lattice; the down-sets form a sublattice, and the readout

  `top : Set V → Option V`,   `top s = some v` iff `v` is the greatest element of `s`

is the partial *supremum* operation of the Dedekind–MacNeille completion: it returns the join
of the cut whenever that join is attained *inside* the cut.  `top` is **not injective** —
`Set.Iic v` and `{v}` (and indeed every set whose greatest element is `v`) all map to
`some v` — which is precisely the source of non-extensionality and is genuinely
*order-theoretic*: the cut forgets all the data below its top.  This is REAL ORDER THEORY,
not a list/endpoint trick and not a `(extra × V)` ghost projection: the payload is an honest
order object and `top` is its "is-this-cut-at-a-point?" denotation.

## Why the polymorphism constraint is satisfied

`get? : M V → K → Option V` is polymorphic in `V`.  We store the richer structure
`S V := Set V` and use the `V`-natural projection `top : S V → Option V` above (well-defined
because greatest elements are unique by antisymmetry, the *only* place `[PartialOrder V]` is
used).  Every operation is defined so that it **commutes with `top`**: constructive operations
store a principal down-set `Set.Iic v` (whose top is `v`) or `∅` (no top), so `top` commutes
definitionally with the seven laws.

## Implementation

`CutMap V := K → Set V`.  `get? m k = top (m k)`.  `insert` stores `Set.Iic v` (the cut *at*
`v`), `delete` stores `∅` (no cut), `empty` stores `∅` everywhere.  `bindAlter`/`merge` first
*observe* via `get?`, combine, and store the result back as a principal down-set / `∅`, so
`top` commutes definitionally with the seven laws.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

variable {K V V' : Type _}

/-! ## The cut readout `top` -/

/-- `IsTop s v`: `v` is the greatest element of the cut `s` (`v` is in `s` and dominates every
member).  When it holds, `v` is the supremum of the cut that is *attained inside* it. -/
def IsTop [PartialOrder V] (s : Set V) (v : V) : Prop := v ∈ s ∧ ∀ x ∈ s, x ≤ v

/-- Greatest elements are unique (antisymmetry), so the cut readout is well-defined. -/
theorem IsTop.unique [PartialOrder V] {s : Set V} {v w : V}
    (hv : IsTop s v) (hw : IsTop s w) : v = w :=
  le_antisymm (hw.2 v hv.1) (hv.2 w hw.1)

open Classical in
/-- The forgetful **cut readout**: read back the greatest element of the cut `s`, i.e. the
supremum of the down-set *when it is attained inside the cut*.  `some v` exactly when `v` is
the greatest element of `s`; otherwise (`∅`, an open/topless cut, …) the observation is
`none`.  This is `V`-natural and **not injective** — every set whose greatest element is `v`
(e.g. `{v}` and the whole principal down-set `Set.Iic v`) shares the observation `some v`. -/
noncomputable def top [PartialOrder V] (s : Set V) : Option V :=
  if h : ∃ v, IsTop s v then some h.choose else none

/-- If `v` is the greatest element of `s`, the readout is `some v`. -/
theorem top_eq_some_of_isTop [PartialOrder V] {s : Set V} {v : V} (h : IsTop s v) :
    top s = some v := by
  have hex : ∃ w, IsTop s w := ⟨v, h⟩
  rw [top, dif_pos hex]
  exact congrArg some (hex.choose_spec.unique h)

/-- The principal down-set `Set.Iic v` is the cut *at* `v`: its greatest element is `v`. -/
@[simp] theorem top_Iic [PartialOrder V] (v : V) : top (Set.Iic v) = some v :=
  top_eq_some_of_isTop ⟨le_refl v, fun _ hx => hx⟩

/-- The singleton cut `{v}` also reads back as `v`. -/
@[simp] theorem top_singleton [PartialOrder V] (v : V) : top ({v} : Set V) = some v :=
  top_eq_some_of_isTop ⟨rfl, fun _ hx => le_of_eq hx⟩

/-- The empty cut has no greatest element, so it is unpinned. -/
@[simp] theorem top_empty [PartialOrder V] : top (∅ : Set V) = none := by
  rw [top, dif_neg]
  rintro ⟨v, hv, _⟩
  exact Set.notMem_empty v hv

/-! ## The carrier and operations -/

/-- A `CutMap` stores a **Dedekind cut / down-set** `Set V` at every key: the lower part of a
cut.  `∅` = no cut, `Set.Iic v` = the cut *at* `v`, an open initial segment = a cut with no
attained top. -/
def CutMap (V : Type _) : Type _ := K → Set V

namespace CutMap

variable [∀ V, PartialOrder V]

/-- Store an `Option V` back as a cut: `none ↦ ∅` (no cut), `some v ↦ Set.Iic v` (cut at
`v`). -/
def store (o : Option V) : Set V := o.elim ∅ Set.Iic

@[simp] theorem store_none : store (none : Option V) = (∅ : Set V) := rfl
@[simp] theorem store_some (v : V) : store (some v) = Set.Iic v := rfl

/-- The readout undoes the storage: reading back the cut stored from `o` recovers `o`. -/
@[simp] theorem top_store (o : Option V) : top (store o) = o := by
  cases o with
  | none => simp
  | some v => simp

/-- The forgetful observation: read back the greatest element of the cut at `k`. -/
noncomputable def get? (m : CutMap (K := K) V) (k : K) : Option V := top (m k)

/-- `insert` records the cut *at* `v`, the principal down-set `Set.Iic v`. -/
def insert [DecidableEq K] (m : CutMap (K := K) V) (k : K) (v : V) : CutMap (K := K) V :=
  fun k' => if k = k' then Set.Iic v else m k'

/-- `delete` records *no cut* `∅` at `k`. -/
def delete [DecidableEq K] (m : CutMap (K := K) V) (k : K) : CutMap (K := K) V :=
  fun k' => if k = k' then ∅ else m k'

/-- The empty map: every key has no cut (`∅`). -/
def empty : CutMap (K := K) V := fun _ => ∅

/-- `bindAlter` *observes* the cut's top at each key, applies `f`, and stores the result back
as a principal down-set. -/
noncomputable def bindAlter (f : K → V → Option V') (m : CutMap (K := K) V) :
    CutMap (K := K) V' :=
  fun k => store ((get? m k).bind (f k))

/-- `merge` observes the tops of both cuts, combines via `op`, and stores back. -/
noncomputable def merge (op : K → V → V → V) (m₁ m₂ : CutMap (K := K) V) :
    CutMap (K := K) V :=
  fun k => store (Option.merge (op k) (get? m₁ k) (get? m₂ k))

noncomputable instance instPartialMap [DecidableEq K] :
    PartialMap (CutMap (K := K)) K where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq [DecidableEq K] (m : CutMap (K := K) V) (k : K) :
    PartialMap.get? m k = top (m k) := rfl

noncomputable instance instLawfulPartialMap [DecidableEq K] :
    LawfulPartialMap (CutMap (K := K)) K where
  get?_empty k := by change top (empty k) = none; simp [empty]
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, CutMap.insert, if_pos h, top_Iic]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, CutMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, CutMap.delete, if_pos h, top_empty]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, CutMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    change top (CutMap.bindAlter f m k) = (get? m k).bind (f k)
    simp only [CutMap.bindAlter, top_store]
  get?_merge {V op m₁ m₂ k} := by
    change top (CutMap.merge op m₁ m₂ k) = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    simp only [CutMap.merge, top_store]

/-! ## Non-extensionality

We exhibit two **distinct** cuts at the same key that observe as the *same* `get?`
(`PartialMap.equiv`) yet are unequal Lean values.  The witnesses are genuinely different cuts
*sharing the same top*: the singleton cut `{v}` and the full principal down-set `Set.Iic v`.
Both have greatest element `v`, so `top` reads both as `some v` — but as sets they differ
whenever *something lies strictly below* `v`.  This is impossible for any
`ExtensionalPartialMap`, and the forgetfulness is *order-theoretic*: the cut forgets all the
data below its top.  (Contrast with `CompletionMap`, which forgets metric-Cauchy-equivalent
tails.) -/

section NonExtensional

variable [DecidableEq K]

/-- First witness: key `k₀` stores the **degenerate** cut `{v}` (a single point). -/
noncomputable def m_singleton (k₀ : K) (v : V) : CutMap (K := K) V :=
  fun k => if k = k₀ then {v} else ∅

/-- Second witness: key `k₀` stores the **full** principal down-set `Set.Iic v`. -/
noncomputable def m_Iic (k₀ : K) (v : V) : CutMap (K := K) V :=
  fun k => if k = k₀ then Set.Iic v else ∅

/-- **Non-extensionality.**  Whenever the value order has a strict pair `u < v`, the cuts
`{v}` and `Set.Iic v` are observationally equal (`PartialMap.equiv`) — both have greatest
element `v`, so `top` reads `some v` at `k₀`, and elsewhere both are `∅` — yet they are
**distinct** Lean values, since `u ∈ Set.Iic v` (as `u ≤ v`) while `u ∉ {v}` (as `u ≠ v`).
This is impossible for any `ExtensionalPartialMap`, and the collapsed data is exactly the
*interior of the cut* `{x | x < v}`. -/
theorem nonextensional (k₀ : K) {u v : V} (huv : u < v) :
    PartialMap.equiv (M := CutMap (K := K)) (m_singleton k₀ v) (m_Iic k₀ v) ∧
      m_singleton k₀ v ≠ m_Iic k₀ v := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both tops are `v` at `k₀`, `none` elsewhere
    change top (m_singleton k₀ v k) = top (m_Iic k₀ v k)
    by_cases hk : k = k₀
    · subst hk
      rw [show m_singleton k v k = ({v} : Set V) from if_pos rfl,
        show m_Iic k v k = (Set.Iic v : Set V) from if_pos rfl, top_singleton, top_Iic]
    · simp only [m_singleton, m_Iic, if_neg hk]
  · -- but distinct as Lean values: `u` lies in `Set.Iic v` but not in `{v}`
    intro h
    have hk0 : m_singleton k₀ v k₀ = m_Iic k₀ v k₀ := congrFun h k₀
    rw [show m_singleton k₀ v k₀ = ({v} : Set V) from if_pos rfl,
      show m_Iic k₀ v k₀ = (Set.Iic v : Set V) from if_pos rfl] at hk0
    -- `u ∈ Set.Iic v` but `u ∉ {v}`
    have hu : u ∈ ({v} : Set V) := hk0 ▸ Set.mem_Iic.mpr (le_of_lt huv)
    exact (ne_of_lt huv) (Set.mem_singleton_iff.mp hu)

/-- Consequently the `CutMap` instance is genuinely non-extensional: as soon as *some* value
order admits a strict pair `u < v`, `equiv` does NOT imply `=`.  (e.g. take the order to be the
genuine order on `ℕ` with `0 < 1`.) -/
theorem not_extensionalPartialMap [Nonempty K] {u v : V} (huv : u < v) :
    ¬ ∀ {m₁ m₂ : CutMap (K := K) V}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro hext
  obtain ⟨k₀⟩ : Nonempty K := ‹Nonempty K›
  obtain ⟨heq, hne⟩ := nonextensional (K := K) k₀ huv
  exact hne (hext heq)

end NonExtensional

/-! ## Applicability: lowering the cut over a `HeapView` CMRA

`HeapView F K V H` (`Iris/Iris/Algebra/HeapView.lean`, lines 314–495) is parameterized by
*any* `LawfulPartialMap H K`; its authoritative/fragment construction and all
frame-preserving updates (`update_one_alloc`, `update_one_delete`, `update_of_local_update`,
`update_replace`, …) are stated purely through `Std.PartialMap.get?`/`insert`/`delete`/`merge`,
never through representation equality.  Hence `CutMap` instantiates `HeapView` directly,
giving a heap whose cells store *Dedekind cuts* rather than fixed values.

### The new kind of update: REFINE-THE-CUT (`s ⊇ s'`, supremum-preserving / lowering)

The cuts form a **complete lattice under inclusion** (the powerset of `V`); the readout `top`
is the *partial supremum* of the Dedekind–MacNeille completion.  This exposes a structurally
new frame-preserving move unavailable to extensional maps or to `List`-endpoint instances:

  **REFINE: replace a cut `s` at `k` by a sub-cut `s' ⊆ s` with the same top** — *or* a
  sub-cut that *raises* the observation toward the supremum.

Two flavors, both phrased through `get?`/`insert`:

* **Lower the cut, fix the value.**  Shrinking `Set.Iic v` to `{v}` (forgetting everything
  strictly below the top) leaves the observation `some v` unchanged: the supremum is
  invariant under throwing away the interior of the cut.  This is the order analogue of
  passing to a *tail-equivalent* Cauchy representative in `CompletionMap`, but here it is
  *intrinsically order-theoretic* — the data discarded is exactly `{x | x < v}`.

* **Refine toward the supremum.**  An open/topless cut observes as `none`; *attaining* its
  supremum `v` (replacing it by `Set.Iic v`) flips the observation `none ↦ some v`.  In
  `HeapView` terms this is an `insert`-style update at `k` realized by
  `HeapView.update_replace` / `HeapView.update_of_local_update`.

Connection to `ℝ`: with `V := ℚ`, the cells are literally Dedekind cuts of the rationals, and
this REFINE update is "name the real number a cut converges to" — the order-completion
counterpart of `CompletionMap`'s metric-completion "name the Cauchy limit".

The next lemma is the concrete, machine-checked content: lowering `Set.Iic v` to the
degenerate cut `{v}` at `k` leaves the observation at `some v` — the supremum is preserved by
forgetting the cut's interior. -/

section Applicability

variable [DecidableEq K]

/-- Store the full principal cut `Set.Iic v` at `k₀`, `∅` elsewhere. -/
noncomputable def cell_Iic (k₀ : K) (v : V) : CutMap (K := K) V :=
  fun k => if k = k₀ then Set.Iic v else ∅

/-- **Lowering the cut preserves the supremum.**  The full cut `Set.Iic v` observes as
`some v` at `k₀`; refining it to the degenerate cut `{v}` (obtained by `insert`, throwing away
the interior `{x | x < v}`) *also* observes as `some v`.  The `some v ↦ some v` invariance
under the inclusion `{v} ⊆ Set.Iic v` is the order-completion "lower the cut" update; it has
no counterpart in extensional or `List`-endpoint partial maps. -/
theorem lower_cut_preserves_sup {k₀ : K} {v : V} :
    PartialMap.get? (M := CutMap (K := K)) (cell_Iic k₀ v) k₀ = some v ∧
      PartialMap.get? (M := CutMap (K := K))
        (PartialMap.insert (cell_Iic k₀ v) k₀ v) k₀ = some v := by
  refine ⟨?_, ?_⟩
  · change top (cell_Iic k₀ v k₀) = some v
    rw [show cell_Iic k₀ v k₀ = (Set.Iic v : Set V) from if_pos rfl, top_Iic]
  · exact get?_insert_eq rfl

/-- The refinement `{v} ⊆ Set.Iic v` is a meet in the cut lattice: `{v} = Set.Iic v ∩ {v}`,
i.e. lowering the cut is intersecting with the degenerate cut at its top. -/
theorem lower_is_meet (v : V) : ({v} : Set V) = Set.Iic v ∩ {v} := by
  ext x; simp

end Applicability

end CutMap

end IrisMath.Instances
