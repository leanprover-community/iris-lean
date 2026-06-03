/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Iris

/-! # `CoarseningMap`: a non-extensional `PartialMap` observed through a coarsening

This file defines a `LawfulPartialMap` instance in which every key stores a **fine object**
— a function `f : ℕ → V` indexed by a fine index type `ℕ` — and the observation `get?`
reads it back only through a fixed **coarsening** of the index, genuinely *merging*
information.  This is the combinatorial / conditional-expectation flavour of
non-extensionality: many distinct fine representatives have the same coarse observation.

## Semantics: conditional expectation onto a coarse σ-algebra

Fix once and for all a surjection `c : ℕ → ℕ`, the *coarsening map* on the fine index.
Think of `c` as generating a sub-σ-algebra `σ(c) ⊆ 𝒫(ℕ)` whose atoms are the fibers
`c⁻¹{j}`; a fine function `f : ℕ → V` is "`σ(c)`-measurable" (coarse) exactly when it is
constant on every fiber of `c`.  The observation we expose for a *single* `Option V` value
is the conditional-expectation-style readback at a **fixed coarse cell** — the fiber over
`c 0` — returning the common value of `f` there *if* `f` is constant on that cell, and
`none` otherwise.

Concretely the coarse observation is

  `coarseValue f = some v`  iff  `f` agrees with `fun _ => v` on the fiber `{ i | c i = c 0 }`.

This is intrinsically forgetful: `coarseValue` cannot see *any* of `f`'s values off the
observed fiber, nor how `f` is distributed across the rest of `ℕ`.  Two fine functions that
agree on the cell but differ wildly elsewhere have the *same* coarse observation, yet are
distinct Lean values.  The forgetfulness does real work — it is the lookup map of a genuine
coarsening, not a discarded product factor.  (The measure-theoretic reading: `coarseValue`
is `E[f | σ(c)]` evaluated on the atom containing `0`, defined when that conditional
expectation is a.e.-constant on the atom, which for the counting/atomic structure here means
literally constant on the cell.)

## Implementation

`CoarseningMap V := ℕ → Option (ℕ → V)`.  `none` at a key means "absent"; `some f` stores
the fine representative `f`.  `get?` returns `coarseValue f`.  Every *constructive*
operation stores a fine function that is **constant** (`fun _ => v`), whose coarse value is
just `v`; so the seven laws reduce to the underlying function-map laws.  Non-extensionality
is witnessed by a fine function that agrees with a constant on the observed cell but differs
off it.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

variable {V V' : Type _}

/-- The fixed **coarsening map** on the fine index `ℕ`.  Its fibers `{ i | c i = j }` are the
atoms of the coarse σ-algebra `σ(c)`.  We take the "halving" surjection `c n = n / 2`, whose
fiber over `0` is `{0, 1}` (so the observed coarse cell is genuinely larger than a point —
that is what makes the observation properly forgetful).  Any surjection would do; the laws
and non-extensionality only use that the fiber over `c 0` contains a point `≠ 0`. -/
def c (n : ℕ) : ℕ := n / 2

/-- The observed **coarse cell**: the fiber of `c` over `c 0`, i.e. the atom of `σ(c)`
containing the fine index `0`.  For `c = (· / 2)` this is `{0, 1}`. -/
def cell (i : ℕ) : Prop := c i = c 0

/-- Index `1` lies in the observed cell (`1 / 2 = 0 = 0 / 2`), but `1 ≠ 0`.  This single fact
is what powers non-extensionality: the cell is strictly bigger than `{0}`. -/
theorem one_mem_cell : cell 1 := rfl

open Classical in
/-- The **coarse value** of a fine function `f : ℕ → V`: `some v` iff `f` is constant `= v`
on the observed coarse cell `{ i | c i = c 0 }`.  This is the single-`Option V` readback of
the conditional expectation `E[f | σ(c)]` on the atom containing `0`.  It is intrinsically
forgetful: it depends on `f` only through its restriction to the cell. -/
noncomputable def coarseValue (f : ℕ → V) : Option V :=
  if h : ∃ v, ∀ i, cell i → f i = v then some h.choose else none

/-- If `f` is constant `= v` on the cell, its coarse value is `some v`. -/
theorem coarseValue_of_const_on_cell {f : ℕ → V} {v : V} (h : ∀ i, cell i → f i = v) :
    coarseValue f = some v := by
  have hex : ∃ v, ∀ i, cell i → f i = v := ⟨v, h⟩
  rw [coarseValue, dif_pos hex]
  -- `hex.choose` and `v` both equal `f 0` on the cell (`0` is in its own cell).
  have hcell0 : cell 0 := rfl
  have h1 := hex.choose_spec 0 hcell0
  have h2 := h 0 hcell0
  exact congrArg some (h1 ▸ h2)

/-- The coarse value of a constant fine function is that constant. -/
@[simp] theorem coarseValue_const (v : V) : coarseValue (fun _ : ℕ => v) = some v :=
  coarseValue_of_const_on_cell (fun _ _ => rfl)

/-- **Coarsening-invariance**: fine functions agreeing on the observed cell have the same
coarse value.  This is the heart of non-extensionality — the observation factors through the
restriction to `{ i | c i = c 0 }`. -/
theorem coarseValue_congr {f f' : ℕ → V} (h : ∀ i, cell i → f i = f' i) :
    coarseValue f = coarseValue f' := by
  by_cases hex : ∃ v, ∀ i, cell i → f i = v
  · obtain ⟨v, hv⟩ := hex
    rw [coarseValue_of_const_on_cell hv,
      coarseValue_of_const_on_cell (fun i hi => (h i hi) ▸ hv i hi)]
  · have hex' : ¬ ∃ v, ∀ i, cell i → f' i = v := by
      rintro ⟨v, hv⟩; exact hex ⟨v, fun i hi => (h i hi).trans (hv i hi)⟩
    classical rw [coarseValue, coarseValue, dif_neg hex, dif_neg hex']

/-- A `CoarseningMap` stores a *fine representative* (`ℕ → V`) at every key.  `none` means
"absent".  Distinct fine functions agreeing on the observed coarse cell denote the same map. -/
def CoarseningMap (V : Type _) : Type _ := ℕ → Option (ℕ → V)

namespace CoarseningMap

/-- The forgetful denotation: read back the coarse value of the fine function stored at `k`. -/
noncomputable def get? (m : CoarseningMap V) (k : ℕ) : Option V := (m k).bind coarseValue

/-- Insert stores the *constant* fine function `fun _ ↦ v`. -/
def insert (m : CoarseningMap V) (k : ℕ) (v : V) : CoarseningMap V :=
  fun k' => if k = k' then some (fun _ => v) else m k'

/-- Delete stores `none` (absent). -/
def delete (m : CoarseningMap V) (k : ℕ) : CoarseningMap V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : CoarseningMap V := fun _ => none

/-- `bindAlter` applies `f` to the coarse value of each stored fine function, re-storing the
result as a constant fine function. -/
noncomputable def bindAlter (f : ℕ → V → Option V') (m : CoarseningMap V) : CoarseningMap V' :=
  fun k => (get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))

/-- `merge` combines the coarse values of two stored fine functions, re-storing the result as
a constant fine function. -/
noncomputable def merge (op : ℕ → V → V → V) (m₁ m₂ : CoarseningMap V) : CoarseningMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)

noncomputable instance instPartialMap : PartialMap CoarseningMap ℕ where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : CoarseningMap V) (k : ℕ) :
    PartialMap.get? m k = (m k).bind coarseValue := rfl

noncomputable instance instLawfulPartialMap : LawfulPartialMap CoarseningMap ℕ where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, CoarseningMap.insert, if_pos h, Option.bind_some,
      coarseValue_const]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, CoarseningMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, CoarseningMap.delete, if_pos h, Option.bind_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, CoarseningMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (CoarseningMap.bindAlter f m k).bind coarseValue = (get? m k).bind (f k)
    unfold CoarseningMap.bindAlter
    show ((get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))).bind coarseValue
      = (get? m k).bind (f k)
    cases hv : get? m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp [coarseValue_const]
  get?_merge {V op m₁ m₂ k} := by
    show (CoarseningMap.merge op m₁ m₂ k).bind coarseValue
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold CoarseningMap.merge
    show ((Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)).bind
      coarseValue = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => simp
    | some w => simp [coarseValue_const]

/-! ## Non-extensionality

We exhibit two **distinct** `CoarseningMap ℕ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but not equal as Lean values.  The witness is a single
key storing two fine functions that agree on the observed coarse cell `{0, 1}` but differ
*off* it: the constant function `fun _ ↦ 0` and `refined`, which is `0` on the cell `{0, 1}`
and `1` elsewhere.  Both have coarse value `some 0`, yet differ at index `2` (which is
outside the cell, hence invisible to the coarsening).  This is genuine **type-I intrinsic**
non-extensionality: the stored payload `ℕ → V` is strictly richer than `Option V`, and
`get?` collapses it via the coarsening — there is no discarded product factor. -/

/-- A fine function equal to `0` on the observed cell `{0, 1}` and `1` off it.  It agrees with
the constant-`0` function on the cell, but differs at `2`. -/
def refined : ℕ → ℕ := fun n => if c n = c 0 then 0 else 1

/-- `refined` agrees with the constant-`0` function on the observed cell. -/
theorem refined_agree_on_cell : ∀ i, cell i → refined i = (fun _ => 0) i := by
  intro i hi
  have hi' : c i = c 0 := hi
  show (if c i = c 0 then (0 : ℕ) else 1) = 0
  rw [if_pos hi']

/-- `refined` differs from the constant-`0` function at index `2` (which is *off* the cell:
`2 / 2 = 1 ≠ 0`), proving the two fine representatives are distinct Lean functions. -/
theorem refined_ne_const : refined ≠ (fun _ => 0) := by
  intro h
  have h2 := congrFun h 2
  simp only [refined, c] at h2
  rw [if_neg (by decide)] at h2
  exact absurd h2 (by decide)

/-- First witness: key `0` stores the constant-`0` fine function. -/
def m_const : CoarseningMap ℕ := CoarseningMap.insert CoarseningMap.empty 0 0

/-- Second witness: key `0` stores the `refined` fine function (same coarse observation,
different fine representative). -/
def m_refined : CoarseningMap ℕ := fun k => if k = 0 then some refined else none

/-- **Non-extensionality.**  `m_const` and `m_refined` are observationally equal
(`PartialMap.equiv`) — both denote "key `0` ↦ coarse value `0`, everything else absent" — yet
they are **distinct** Lean values, because the underlying stored fine functions
(`fun _ ↦ 0` versus `refined`) differ off the observed cell (at index `2`).  This is
impossible for any `ExtensionalPartialMap`, so `CoarseningMap` is genuinely non-extensional,
and the non-extensionality is *intrinsic* (the collapse is the coarsening, not a projection
of a stored product). -/
theorem nonextensional :
    PartialMap.equiv (M := CoarseningMap) m_const m_refined ∧ m_const ≠ m_refined := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both give `some 0` at key 0, `none` elsewhere
    by_cases hk : k = 0
    · subst hk
      show ((m_const 0).bind coarseValue) = ((m_refined 0).bind coarseValue)
      have hc : m_const 0 = some (fun _ => 0) := by simp [m_const, CoarseningMap.insert]
      have hr : m_refined 0 = some refined := by simp [m_refined]
      rw [hc, hr, Option.bind_some, Option.bind_some,
        coarseValue_const, coarseValue_congr refined_agree_on_cell, coarseValue_const]
    · show ((m_const k).bind coarseValue) = ((m_refined k).bind coarseValue)
      have hc : m_const k = none := by
        simp [m_const, CoarseningMap.insert, CoarseningMap.empty, Ne.symm hk]
      have hr : m_refined k = none := by simp [m_refined, hk]
      rw [hc, hr]
  · -- distinct as Lean values: at key 0 the stored fine functions differ off the cell
    intro h
    have h0 : m_const 0 = m_refined 0 := congrFun h 0
    have hc : m_const 0 = some (fun _ => 0) := by simp [m_const, CoarseningMap.insert]
    have hr : m_refined 0 = some refined := by simp [m_refined]
    rw [hc, hr, Option.some.injEq] at h0
    exact refined_ne_const h0.symm

/-- Consequently this instance is genuinely non-extensional: `equiv` does NOT imply `=`. -/
theorem not_extensionalPartialMap :
    ¬ ∀ {m₁ m₂ : CoarseningMap ℕ}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro h
  exact nonextensional.2 (h nonextensional.1)

end CoarseningMap

/-! ## Applicability: a `HeapView` CMRA over coarsely-observed cells

Since `CoarseningMap` is a `LawfulPartialMap CoarseningMap ℕ`, it slots directly into
`Iris.Algebra.HeapView`:

  `HeapView F ℕ V H`  with  `H := CoarseningMap` (this file) and `K := ℕ`.

`HeapView` provides authoritative ownership `Auth (.own one) m` over the whole heap of fine
cells, and fragmental ownership `Frag k dq v` over a single cell's *coarse value*; the view
relation `HeapR` observes the heap **only** through `Std.PartialMap.get?`, i.e. through this
file's coarse readback `coarseValue`.

### An interesting frame-preserving update `~~>`

The coarsening makes a class of updates *free* (frame-preserving) that change real data but
leave the observation fixed: **rewriting the fine representative off the observed cell — or
anywhere within it as long as the cell stays constant at the same value — leaves the coarse
value invariant.**  This is the resource-algebra shadow of `nonextensional` above.

Concretely, replacing the fine function `fun _ ↦ v` by `refined`-style data that still reads
back to `v` on the cell is the *identity on coarse values*, so for `H := CoarseningMap`:

  `Auth (.own one) m₁ • Frag k (.own one) v  ~~>  `
  `Auth (.own one) (insert m₁ k v) • Frag k (.own one) v`,

an instance of `HeapView.update_replace` (`Iris/Algebra/HeapView.lean`, line 438): the
new cell value `v2 := v` is valid because `✓ v` already held, and the update is stated purely
through `get?`/`insert`, never term equality.  Because `insert` re-stores the *constant* fine
function (coarse value `v`), this is observationally an identity on the CMRA element — yet the
underlying fine storage has been refreshed.  More generally, `HeapView.update_of_local_update`
lifts any local update `(v, v) ~l~> (v, v')` on the coarse values; the "fine refinement off
the observed cell" is invisible to the CMRA precisely because every HeapView operation only
sees `coarseValue`.  This is exactly the conditional-expectation intuition: changing a
function away from (or constantly within) the conditioned σ-algebra cell does not change the
conditional expectation, hence does not change the observable resource. -/

section Applicability

open CoarseningMap

/-- **Coarse-observation invariance under fine refinement off the cell**, machine-checked.
Replacing the constant fine function at a key by *any* fine function agreeing with it on the
observed cell yields an `equiv` map.  Such a rewrite is therefore frame-preserving for every
`HeapView` update built on this instance (it is the denotation-level content of
`update_replace`/`update_of_local_update`). -/
theorem refine_off_cell_equiv (m : CoarseningMap V) (k : ℕ) (v : V) {g : ℕ → V}
    (hg : ∀ i, cell i → g i = v) :
    PartialMap.equiv (PartialMap.insert m k v) (fun k' => if k = k' then some g else m k') := by
  intro k'
  show ((CoarseningMap.insert m k v) k').bind coarseValue
    = ((fun k' => if k = k' then some g else m k') k').bind coarseValue
  by_cases hk : k = k'
  · simp only [CoarseningMap.insert, if_pos hk, Option.bind_some]
    rw [coarseValue_const, coarseValue_of_const_on_cell hg]
  · simp only [CoarseningMap.insert, if_neg hk]

end Applicability

end IrisMath.Instances
