/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Iris
public import IrisMath.Instances.ConstOnFilterMap

/-! # `VariableFilterMap`: a non-extensional `PartialMap` whose *negligibility structure is
part of the heap state*

This file generalizes `ConstOnFilterMap` along its deepest axis.  In `ConstOnFilterMap` a
*single* filter `l : Filter Idx` is fixed once and for all, and every cell is observed up to
`l`-eventual equality.  Here we instead **store the filter inside each cell**: a present cell
carries a *pair* `(l, s)` of a filter `l : Filter ℕ` together with a representative sequence
`s : ℕ → V`, and the observation reads back the `l`-eventual value of `s` using *that cell's
own* filter.

  `VariableFilterMap K V := K → Option ((l : Filter ℕ) × (ℕ → V))`

  `get? m k :=` the `l`-eventual-constant value of `s`, where `(l, s)` is the stored pair.

So the *resolution* at which a cell is observed — the size of the "small/negligible" sets that
are forgotten — is **owned by the cell** and can differ from key to key.  The cell at `k₁`
might forget finite prefixes (`atTop`), while the cell at `k₂` forgets nothing (`pure i`):
both live in the same map.

## Reuse

The `eventualValue`/`eventualValue_congr` helpers proved filter-agnostically in
`ConstOnFilterMap.lean` are now top-level in `IrisMath.Instances`; we `open` that namespace and
reuse them directly rather than redefining.  `eventualValue l s` is total for *any* `l`: it
returns `some c` when `s =ᶠ[l] (fun _ => c)` and `none` otherwise; the uniqueness/congruence
lemmas need `[l.NeBot]`, which we supply by storing `atTop` (a `NeBot` filter) in every
*constructed* cell.

## Laws

All seven `LawfulPartialMap` laws go through exactly as in `ConstOnFilterMap`, because every
cell produced by `insert`/`bindAlter`/`merge` stores the *fixed* `NeBot` filter `atTop` together
with a *constant* sequence, whose `eventualValue` is just the inserted value.  The stored filter
only varies on cells the user builds by hand (the non-extensionality witness below), and
because `get?` reads each cell's *own* filter, two hand-built cells with different filters but
the same eventual value are observationally equal.

All helpers live in the `VariableFilterMap` sub-namespace so they never clash with the
shared-level `eventualValue`/`den` of the sibling instances.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap Filter

variable {K : Type _} [DecidableEq K] {V V' : Type _}

/-- A cell payload: a filter `l` on `ℕ` (the per-cell *resolution* / negligibility structure)
together with a representative sequence `s : ℕ → V`, observed only up to `l`-eventual equality. -/
abbrev Cell (V : Type _) : Type _ := (_l : Filter ℕ) × (ℕ → V)

/-- The carrier: at each key, either absent (`none`) or a present cell carrying *its own*
filter and representative sequence. -/
def VariableFilterMap (K V : Type _) : Type _ := K → Option (Cell V)

namespace VariableFilterMap

/-- Read back the eventual value stored at `k`, using **the cell's own filter**.  This is the
crux: the resolution at which the cell is observed is the one stored in the cell. -/
noncomputable def get? (m : VariableFilterMap K V) (k : K) : Option V :=
  (m k).bind (fun c => eventualValue c.1 c.2)

/-- Insert stores the fixed `NeBot` filter `atTop` together with the *constant* sequence
`fun _ => v`. -/
def insert (m : VariableFilterMap K V) (k : K) (v : V) : VariableFilterMap K V :=
  fun k' => if k = k' then some ⟨atTop, fun _ => v⟩ else m k'

/-- Delete stores `none` (absent). -/
def delete (m : VariableFilterMap K V) (k : K) : VariableFilterMap K V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : VariableFilterMap K V := fun _ => none

/-- `bindAlter` applies `f` to the (own-filter) eventual value of each cell, re-storing the
result as a constant sequence under `atTop`. -/
noncomputable def bindAlter (f : K → V → Option V') (m : VariableFilterMap K V) :
    VariableFilterMap K V' :=
  fun k => (get? m k).bind (fun v => (f k v).map (fun w => ⟨atTop, fun _ => w⟩))

/-- `merge` combines the (own-filter) eventual values of two cells, re-storing the result as a
constant sequence under `atTop`. -/
noncomputable def merge (op : K → V → V → V) (m₁ m₂ : VariableFilterMap K V) :
    VariableFilterMap K V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => ⟨atTop, fun _ => w⟩)

noncomputable instance instPartialMap : PartialMap (VariableFilterMap K) K where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : VariableFilterMap K V) (k : K) :
    PartialMap.get? m k = (m k).bind (fun c => eventualValue c.1 c.2) := rfl

/-- The eventual value of a cell `⟨atTop, fun _ => v⟩` is `some v` (since `atTop.NeBot`). -/
@[simp] theorem eventualValue_atTop_const (v : V) :
    eventualValue (atTop : Filter ℕ) (fun _ => v) = some v :=
  eventualValue_const v

noncomputable instance instLawfulPartialMap : LawfulPartialMap (VariableFilterMap K) K where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, VariableFilterMap.insert, if_pos h, Option.bind_some,
      eventualValue_atTop_const]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, VariableFilterMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, VariableFilterMap.delete, if_pos h, Option.bind_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, VariableFilterMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    change (VariableFilterMap.bindAlter f m k).bind (fun c => eventualValue c.1 c.2)
      = (get? m k).bind (f k)
    unfold VariableFilterMap.bindAlter
    cases hv : get? m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp
  get?_merge {V op m₁ m₂ k} := by
    change (VariableFilterMap.merge op m₁ m₂ k).bind (fun c => eventualValue c.1 c.2)
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold VariableFilterMap.merge
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => simp
    | some w => simp

/-! ## Non-extensionality — *intrinsic*, and stronger than `ConstOnFilterMap`'s

Because each cell owns its filter, non-extensionality here comes in **two genuinely distinct
flavours**, both impossible for any `ExtensionalPartialMap`:

1. *Same filter, different representatives* (as in `ConstOnFilterMap`): two cells storing the
   same `NeBot` filter but reps that agree only `l`-eventually.
2. *Different filters entirely*: two cells storing **different filters** `l₁ ≠ l₂` whose stored
   reps nonetheless have the same eventual value.  This is impossible to even *state* for a
   fixed-filter construction, since the filter is part of the state here.

We exhibit flavour (2): key `0` stores `⟨atTop, fun _ => 0⟩` in one map and `⟨pure 7, fun _ => 0⟩`
in the other.  Different filters (and `pure 7` is also `NeBot`), but both reps are the constant
`0` sequence, so both observe `some 0`.  The underlying cells differ as Lean values (their
filter components differ), so the maps are `≠` yet `PartialMap.equiv`. -/

/-- First witness: key `0` stores the constant-`0` sequence under filter `atTop`. -/
noncomputable def w_atTop : VariableFilterMap ℕ ℕ :=
  fun k => if k = 0 then some ⟨atTop, fun _ => 0⟩ else none

/-- Second witness: key `0` stores the constant-`0` sequence under the **different** filter
`pure 7`.  Same eventual value, different stored resolution. -/
noncomputable def w_pure : VariableFilterMap ℕ ℕ :=
  fun k => if k = 0 then some ⟨pure 7, fun _ => 0⟩ else none

/-- **Intrinsic non-extensionality, distinct-filter flavour.**  `w_atTop` and `w_pure` store the
constant-`0` sequence under two *different* filters (`atTop` vs `pure 7`).  Both are `NeBot`, so
both cells observe `some 0` at key `0` and `none` elsewhere: the maps are `PartialMap.equiv`.
Yet they are `≠` as Lean values, because the stored filter components differ.  No fixed-filter
construction can even phrase this collapse, since the filter is part of the cell state. -/
theorem nonextensional_distinct_filters :
    PartialMap.equiv (M := VariableFilterMap ℕ) w_atTop w_pure ∧ w_atTop ≠ w_pure := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = 0
    · subst hk
      change ((w_atTop 0).bind (fun c => eventualValue c.1 c.2))
        = ((w_pure 0).bind (fun c => eventualValue c.1 c.2))
      have ha : w_atTop 0 = some ⟨atTop, fun _ => 0⟩ := by simp [w_atTop]
      have hp : w_pure 0 = some ⟨pure 7, fun _ => 0⟩ := by simp [w_pure]
      rw [ha, hp, Option.bind_some, Option.bind_some, eventualValue_const, eventualValue_const]
    · change ((w_atTop k).bind (fun c => eventualValue c.1 c.2))
        = ((w_pure k).bind (fun c => eventualValue c.1 c.2))
      have ha : w_atTop k = none := by simp [w_atTop, hk]
      have hp : w_pure k = none := by simp [w_pure, hk]
      rw [ha, hp]
  · intro h
    have h0 : w_atTop 0 = w_pure 0 := congrFun h 0
    have ha : w_atTop 0 = some ⟨atTop, fun _ => 0⟩ := by simp [w_atTop]
    have hp : w_pure 0 = some ⟨pure 7, fun _ => (0 : ℕ)⟩ := by simp [w_pure]
    rw [ha, hp, Option.some.injEq] at h0
    -- the filter components `atTop` and `pure 7` are different
    have hfilt : (atTop : Filter ℕ) = pure 7 := congrArg Sigma.fst h0
    -- `atTop` is not principal at a point; `pure 7` is.  `0 ∈ atTop`-eventually is false but
    -- `0 ∉ pure 7`-membership of the complement... use that `{7}ᶜ ∈ pure 7` is false but `∈ atTop`.
    have h7 : {n : ℕ | n ≠ 7} ∈ (atTop : Filter ℕ) :=
      eventually_atTop.mpr ⟨8, fun b hb => show b ≠ 7 by omega⟩
    rw [hfilt] at h7
    simp only [Filter.mem_pure, Set.mem_setOf_eq] at h7
    exact h7 rfl

/-- A sequence equal to `0` everywhere except at index `0`; agrees with the constant-`0`
sequence eventually along `atTop`. -/
def bumped : ℕ → ℕ := fun n => if n = 0 then 1 else 0

theorem bumped_eventuallyEq : bumped =ᶠ[atTop] (fun _ => (0 : ℕ)) := by
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun b hb => by simp [bumped, Nat.one_le_iff_ne_zero.mp hb]⟩

/-- **Intrinsic non-extensionality, same-filter flavour** (the `ConstOnFilterMap` style, recovered
here): key `0` stores the constant-`0` sequence vs a sequence bumped at index `0`, both under
`atTop`.  They agree `atTop`-eventually, hence observe `some 0`, yet differ as reps. -/
theorem nonextensional_same_filter :
    PartialMap.equiv (M := VariableFilterMap ℕ)
        (fun k => if k = 0 then some ⟨atTop, fun _ => 0⟩ else none)
        (fun k => if k = 0 then some ⟨atTop, bumped⟩ else none)
      ∧ (fun k => if k = 0 then some (⟨atTop, fun _ => 0⟩ : Cell ℕ) else none)
          ≠ (fun k : ℕ => if k = 0 then some ⟨atTop, bumped⟩ else none) := by
  refine ⟨fun k => ?_, ?_⟩
  · simp only [get?_eq]
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, if_pos rfl, Option.bind_some, Option.bind_some, eventualValue_const,
        eventualValue_congr bumped_eventuallyEq, eventualValue_const]
    · rw [if_neg hk, if_neg hk]
  · intro h
    have h0 := congrFun h 0
    rw [if_pos rfl, if_pos rfl, Option.some.injEq] at h0
    have := congrFun (congrArg Sigma.snd h0) 0
    simp [bumped] at this

/-! ## Applicability (the novelty): the stored filter is an *owned, adjustable resolution*

Slotting `VariableFilterMap` into `Iris.Algebra.HeapView` (as `H := VariableFilterMap`,
`K := ℕ`, value type the cell's eventual value), the authoritative heap `Auth (.own one) m`
owns, *per cell*, not just a value but the **resolution** `l` at which that value is observed.
This has no analogue in any fixed-equality CMRA: ordinary heaps carry values, not the
equivalence relation those values are read modulo.  Here the relation itself is heap state.

### Resolution-lowering (filter-coarsening) updates `~~>`

The defining new move is a **frame-preserving update that coarsens a cell's filter**, forgetting
*more* — enlarging the negligible sets — while *preserving the observation*.  Getting the
direction right is the whole content.

In mathlib, `l ≤ l'` means `l` is **finer** (more sets are "eventually true" / `l` has *smaller*
small-sets); `l'` is **coarser**.  Being `l'`-eventually-constant is therefore the **stronger**
statement: it implies `l`-eventually-constant, since `EventuallyEq` *transfers down* a `≤`-chain.
So the correct, observation-*preserving* direction is:

> **Coarsen up the order.**  If `s =ᶠ[l'] (fun _ => v)` and `l ≤ l'` then `s =ᶠ[l] (fun _ => v)`,
> hence `get?` of the cell `⟨l', s⟩` equals `get?` of `⟨l, s⟩` *when the coarser cell already
> resolves to `some v`* — but the finer cell `⟨l, s⟩` may resolve to *more* values, never fewer.

Concretely the safe update keeps the same rep `s` and replaces a coarser filter by a finer one
**along a chain on which the eventual value is unchanged**; the cleanest packaging fixes the
observation by working with constant reps, where any two `NeBot` filters agree (flavour (2)
above) — the resolution is then a free parameter.  The single concrete coarsening lemma below is
the engine; it is the `VariableFilterMap` analogue of `Filter.EventuallyEq.filter_mono`. -/

/-- **The filter-coarsening lemma.**  If a sequence is `l'`-eventually the constant `v` and
`l ≤ l'` (so `l'` is *coarser*, `l` *finer*), then the cell `⟨l, s⟩` *also* observes `some v`:
`get?` of the finer-filter cell equals `get?` of the coarser-filter cell.  This is the engine of
resolution-lowering updates: a coarser-observed cell can be re-stored with any finer filter `l`
(`l ≤ l'`) on which its rep is still eventually constant, with the **observation preserved**.
The asymmetry — finer filters preserve, coarser ones may only forget — is exactly what makes the
"lower the resolution" update one-directional, with no analogue in a fixed-equality CMRA. -/
theorem get?_coarsen {s : ℕ → V} {v : V} {l l' : Filter ℕ} [l.NeBot] [l'.NeBot]
    (hmono : l ≤ l') (hconst : s =ᶠ[l'] (fun _ => v)) :
    eventualValue l s = some v ∧ eventualValue l' s = some v := by
  refine ⟨?_, eventualValue_of_eventuallyEq hconst⟩
  exact eventualValue_of_eventuallyEq (hconst.filter_mono hmono)

/-- Packaged as a statement about the map cells: replacing a coarser-filter constant cell by a
finer-filter one (`l ≤ l'`) along a constant rep is `PartialMap.equiv`-preserving — the
resolution-lowering update is *observationally invisible*, hence (via `HeapView.update_replace`)
a frame-preserving `~~>` whenever the value's CMRA validity carries over (here trivially, the
value is literally unchanged). -/
theorem equiv_coarsen_cell (k₀ : ℕ) {v : V} {l l' : Filter ℕ} [l.NeBot] [l'.NeBot]
    (_hmono : l ≤ l') :
    PartialMap.equiv (M := VariableFilterMap ℕ)
      (fun k => if k = k₀ then some ⟨l', fun _ => v⟩ else none)
      (fun k => if k = k₀ then some ⟨l, fun _ => v⟩ else none) := by
  intro k
  simp only [get?_eq]
  by_cases hk : k = k₀
  · rw [if_pos hk, if_pos hk, Option.bind_some, Option.bind_some, eventualValue_const,
      eventualValue_const]
  · rw [if_neg hk, if_neg hk]

end VariableFilterMap

end IrisMath.Instances
