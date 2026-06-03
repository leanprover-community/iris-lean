/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Prod
public import Mathlib.Order.Filter.Prod
public import Iris

/-! # `ProductGermMap`: a non-extensional `PartialMap` whose payload is a *double sequence*

This file defines a `LawfulPartialMap` instance in which each key stores a **2D family**
`ℕ × ℕ → V` (a double sequence), and the observation `get?` collapses that family to the
value of its **germ along the product filter `(atTop : Filter (ℕ × ℕ))`** — i.e. its
eventual value as *both* coordinates tend to infinity.  Two double sequences that agree
eventually along the product filter (differ only on a filter-negligible set, e.g. a "thin
cross" of finitely many rows/columns) have the same germ, hence the same denotation, yet
are distinct Lean values: the representation is genuinely **non-extensional** (two `≠`
reps with `PartialMap.equiv`).

## Why this is genuinely distinct from `GermMap`

`GermMap` (this directory) stores a *one-dimensional* sequence `ℕ → V` and observes the
germ along the **fixed 1D filter `Filter.atTop`** on `ℕ`; its negligible sets are the
*finite prefixes* (`{0, 1, …, N}`).  `ProductGermMap` instead stores a *two-dimensional*
family `ℕ × ℕ → V` and observes the germ along the **product filter**
`(atTop : Filter (ℕ × ℕ))` — equivalently `Filter.atTop ×ˢ Filter.atTop` — on the product
order `ℕ × ℕ`.  The index/observation structure is therefore genuinely different:

* the **directed set** is now the product order `(ℕ × ℕ, ≤)`, not the chain `ℕ`;
* the **negligible sets** are no longer finite prefixes but **complements of product
  up-sets** `{ (i, j) | i ≥ a ∧ j ≥ b }ᶜ` — in particular *infinite* "thin crosses" such
  as an entire row `{ (0, j) | j }` or column are negligible, even though they contain
  infinitely many points.

So two double sequences can differ on an **entire row** (an infinite set!) and still have
the same product-filter germ — a phenomenon with no 1D analogue.  The eventual-constant
extraction reuses the classical `choose` machinery of `GermMap`, but over the product
filter; non-extensionality is witnessed by a "row-0 bump", a difference on an infinite but
filter-negligible thin cross.

## Implementation

`ProductGermMap V := ℕ → Option (ℕ × ℕ → V)`.  `none` at a key means "absent"; `some s`
stores the representative double sequence `s`.  `get?` returns the *product-filter eventual
value* `eventualValueProd s`: the unique `c` with `s =ᶠ[atTop] (fun _ ↦ c)` if one exists.
Every constructive operation stores a *constant* double sequence `fun _ ↦ v`, whose
eventual value is just `v`, so the seven laws reduce to the function-map laws;
non-extensionality is then witnessed by a double sequence that is constant off row `0` but
differs from that constant on all of row `0`.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap Filter

variable {V V' : Type _}

/-- The product index used as the observation domain: pairs `(i, j) : ℕ × ℕ` ordered by the
product order, on which `(atTop : Filter (ℕ × ℕ))` is the product filter
`Filter.atTop ×ˢ Filter.atTop`.  It is a directed nonempty preorder, hence `atTop` is
`NeBot`. -/
abbrev Idx := ℕ × ℕ

open Classical in
/-- The eventual value of a double sequence `s : ℕ × ℕ → V` along the product filter
`(atTop : Filter (ℕ × ℕ))`: the unique `c` such that `s` is eventually equal to the constant
family `fun _ => c` as both coordinates tend to infinity, if one exists.  This is the
observation of the germ `(↑s : Germ atTop V)` whenever that germ is constant. -/
noncomputable def eventualValueProd (s : Idx → V) : Option V :=
  if h : ∃ c, s =ᶠ[atTop] (fun _ => c) then some h.choose else none

/-- If `s` is eventually constant `= c` along the product filter, its `eventualValueProd` is
`some c`.  Uses that `atTop` on `ℕ × ℕ` is `NeBot`, so eventually-equal constants are
equal. -/
theorem eventualValueProd_of_eventuallyEq {s : Idx → V} {c : V} (h : s =ᶠ[atTop] (fun _ => c)) :
    eventualValueProd s = some c := by
  have hex : ∃ c, s =ᶠ[atTop] (fun _ => c) := ⟨c, h⟩
  rw [eventualValueProd, dif_pos hex]
  have hspec : s =ᶠ[atTop] (fun _ => hex.choose) := hex.choose_spec
  have heq : (fun _ : Idx => hex.choose) =ᶠ[atTop] (fun _ => c) := hspec.symm.trans h
  exact congrArg some (const_eventuallyEq.mp heq)

/-- The eventual value of a constant double sequence is that constant. -/
@[simp] theorem eventualValueProd_const (v : V) : eventualValueProd (fun _ : Idx => v) = some v :=
  eventualValueProd_of_eventuallyEq EventuallyEq.rfl

/-- `eventualValueProd` is **germ-invariant**: double sequences that agree eventually along the
product filter (equal germs) have the same eventual value.  This is the heart of
non-extensionality: the observation factors through `Germ.ofFun` for `(atTop : Filter Idx)`. -/
theorem eventualValueProd_congr {s s' : Idx → V} (h : s =ᶠ[atTop] s') :
    eventualValueProd s = eventualValueProd s' := by
  by_cases hex : ∃ c, s =ᶠ[atTop] (fun _ => c)
  · obtain ⟨c, hc⟩ := hex
    rw [eventualValueProd_of_eventuallyEq hc, eventualValueProd_of_eventuallyEq (h.symm.trans hc)]
  · have hex' : ¬ ∃ c, s' =ᶠ[atTop] (fun _ => c) := by
      rintro ⟨c, hc⟩; exact hex ⟨c, h.trans hc⟩
    classical rw [eventualValueProd, eventualValueProd, dif_neg hex, dif_neg hex']

/-- The germ-flavoured forgetful denotation `den : ProductGermMap V → (ℕ → Option V)`: read
back the product-filter eventual value of the stored double sequence at each key. -/
noncomputable def denProd (m : ℕ → Option (Idx → V)) (k : ℕ) : Option V :=
  (m k).bind eventualValueProd

/-- A `ProductGermMap` stores a *representative double sequence* (`ℕ × ℕ → V`) at every key.
`none` means "absent".  Distinct double sequences with the same germ along the product
filter denote the same map. -/
def ProductGermMap (V : Type _) : Type _ := ℕ → Option (Idx → V)

namespace ProductGermMap

/-- The forgetful denotation: read back the eventual (product-filter germ) value stored at
`k`. -/
noncomputable def get? (m : ProductGermMap V) (k : ℕ) : Option V := denProd m k

/-- Insert stores the *constant* double sequence `fun _ ↦ v`. -/
def insert (m : ProductGermMap V) (k : ℕ) (v : V) : ProductGermMap V :=
  fun k' => if k = k' then some (fun _ => v) else m k'

/-- Delete stores `none` (absent). -/
def delete (m : ProductGermMap V) (k : ℕ) : ProductGermMap V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : ProductGermMap V := fun _ => none

/-- `bindAlter` applies `f` to the eventual value of each stored double sequence, storing the
result as a constant double sequence. -/
noncomputable def bindAlter (f : ℕ → V → Option V') (m : ProductGermMap V) : ProductGermMap V' :=
  fun k => (get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))

/-- `merge` combines the eventual values of two stored double sequences, storing the result
as a constant double sequence. -/
noncomputable def merge (op : ℕ → V → V → V) (m₁ m₂ : ProductGermMap V) : ProductGermMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)

noncomputable instance instPartialMap : PartialMap ProductGermMap ℕ where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : ProductGermMap V) (k : ℕ) :
    PartialMap.get? m k = (m k).bind eventualValueProd := rfl

noncomputable instance instLawfulPartialMap : LawfulPartialMap ProductGermMap ℕ where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, ProductGermMap.insert, if_pos h, Option.bind_some,
      eventualValueProd_const]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, ProductGermMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, ProductGermMap.delete, if_pos h, Option.bind_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, ProductGermMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (ProductGermMap.bindAlter f m k).bind eventualValueProd = (get? m k).bind (f k)
    unfold ProductGermMap.bindAlter
    show ((get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))).bind eventualValueProd
      = (get? m k).bind (f k)
    cases hv : get? m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp [eventualValueProd_const]
  get?_merge {V op m₁ m₂ k} := by
    show (ProductGermMap.merge op m₁ m₂ k).bind eventualValueProd
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold ProductGermMap.merge
    show ((Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)).bind
      eventualValueProd = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => simp
    | some w => simp [eventualValueProd_const]

/-! ## Non-extensionality

We exhibit two **distinct** `ProductGermMap ℕ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but not equal as Lean values.  The witness is a single
key storing two double sequences with the *same germ* along the product filter: the constant
double sequence `fun _ ↦ 0` and `rowBumped`, which equals `0` everywhere except on the whole
of **row `0`** (`{ (0, j) | j }`), where it is `1`.  Row `0` is a *thin cross*: it is an
**infinite** set, yet it is **negligible** for `(atTop : Filter (ℕ × ℕ))` because the
product up-set `{ (i, j) | i ≥ 1 }` is eventually true and avoids it.  Hence the two double
sequences agree eventually along the product filter and have the same eventual value `0` —
even though they differ at infinitely many points.  This has no 1D `GermMap` analogue, where
only *finite* sets are negligible. -/

/-- A double sequence equal to `0` everywhere except on the whole of **row `0`**, where it is
`1`.  Row `0` is an infinite "thin cross", yet negligible for the product filter, so this
agrees with the constant-`0` family eventually along `(atTop : Filter (ℕ × ℕ))`. -/
def rowBumped : Idx → ℕ := fun p => if p.1 = 0 then 1 else 0

/-- `rowBumped` agrees with the constant-`0` family eventually along the product filter: they
coincide on the product up-set `{ (i, j) | i ≥ 1 }`, which is eventually true.  Note this
is an *infinite* agreement region whose complement (row `0`) is also infinite — impossible
for the 1D `atTop` on `ℕ`. -/
theorem rowBumped_eventuallyEq : rowBumped =ᶠ[atTop] (fun _ => 0) := by
  rw [EventuallyEq, eventually_atTop]
  -- Beyond the threshold `(1, 0)` (product order), the first coordinate is `≥ 1`, off row `0`.
  refine ⟨(1, 0), fun p hp => ?_⟩
  have h1 : 1 ≤ p.1 := (Prod.le_def.mp hp).1
  simp only [rowBumped, Nat.one_le_iff_ne_zero.mp h1, if_false]

/-- First witness: key `0` stores the constant-`0` double sequence. -/
def m_const : ProductGermMap ℕ := ProductGermMap.insert ProductGermMap.empty 0 0

/-- Second witness: key `0` stores the `rowBumped` double sequence (same product-filter germ,
different representative). -/
def m_bumped : ProductGermMap ℕ := fun k => if k = 0 then some rowBumped else none

/-- **Non-extensionality.**  `m_const` and `m_bumped` are observationally equal
(`PartialMap.equiv`) — both denote "key `0` ↦ product-filter eventual value `0`, everything
else absent" — yet they are **distinct** Lean values, because the underlying stored double
sequences (`fun _ ↦ 0` versus `rowBumped`) differ on the whole of row `0` (an infinite,
filter-negligible thin cross).  This is impossible for any `ExtensionalPartialMap`, so
`ProductGermMap` is genuinely non-extensional, and intrinsically so: the stored payload
`ℕ × ℕ → V` is strictly richer than `Option V`, collapsed by the product-filter germ — no
discarded product factor. -/
theorem nonextensional :
    PartialMap.equiv (M := ProductGermMap) m_const m_bumped ∧ m_const ≠ m_bumped := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both give `some 0` at key 0, `none` elsewhere
    by_cases hk : k = 0
    · subst hk
      show ((m_const 0).bind eventualValueProd) = ((m_bumped 0).bind eventualValueProd)
      have hc : m_const 0 = some (fun _ => 0) := by simp [m_const, ProductGermMap.insert]
      have hb : m_bumped 0 = some rowBumped := by simp [m_bumped]
      rw [hc, hb, Option.bind_some, Option.bind_some,
        eventualValueProd_const, eventualValueProd_congr rowBumped_eventuallyEq, eventualValueProd_const]
    · show ((m_const k).bind eventualValueProd) = ((m_bumped k).bind eventualValueProd)
      have hc : m_const k = none := by
        simp [m_const, ProductGermMap.insert, ProductGermMap.empty, Ne.symm hk]
      have hb : m_bumped k = none := by simp [m_bumped, hk]
      rw [hc, hb]
  · -- distinct as Lean values: at key 0 the stored double sequences differ on row 0
    intro h
    have h0 : m_const 0 = m_bumped 0 := congrFun h 0
    have hc : m_const 0 = some (fun _ => 0) := by simp [m_const, ProductGermMap.insert]
    have hb : m_bumped 0 = some rowBumped := by simp [m_bumped]
    rw [hc, hb, Option.some.injEq] at h0
    -- `(fun _ => 0) = rowBumped` would force agreement at `(0, 0)` (on row `0`)
    have := congrFun h0 (0, 0)
    simp [rowBumped] at this

/-- Consequently this instance is genuinely non-extensional: `equiv` does NOT imply `=`. -/
theorem not_extensionalPartialMap :
    ¬ ∀ {m₁ m₂ : ProductGermMap ℕ}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro h
  exact nonextensional.2 (h nonextensional.1)

end ProductGermMap

/-! ## Applicability: a `HeapView` CMRA over product-filter germ values

Since `ProductGermMap` is a `LawfulPartialMap ProductGermMap ℕ`, it slots directly into
`Iris.Algebra.HeapView`:

  `HeapView F ℕ V H`  with  `H := ProductGermMap` (this file) and `K := ℕ`.

`HeapView` provides authoritative ownership `Auth (.own one) m` over the whole heap of
double-sequence cells, and fragmental ownership `Frag k dq v` over a single cell's
*product-filter germ value*; the view relation `HeapR` observes the heap **only** through
`Std.PartialMap.get?`, i.e. through this file's product-filter readback `eventualValueProd`.

### An interesting frame-preserving update `~~>`

The product-filter germ makes a class of updates *free* (frame-preserving) that change real
data on an **infinite** region yet leave the observation fixed: **modifying the
representative double sequence along a thin, filter-negligible slice — e.g. an entire row
or column, or any finite union of rows/columns — leaves the germ invariant.**  This is the
resource-algebra shadow of `nonextensional` above, and it is *strictly more permissive* than
the `GermMap` update: there the negligible region was a finite prefix; here it is a thin
cross of infinitely many points.

Concretely, if `s =ᶠ[atTop] s'` (they differ only on a filter-negligible thin cross, e.g.
`rowBumped` vs `fun _ ↦ 0`), then `(↑s : Germ atTop β) = ↑s'`, so for any frame the view
relation `HeapR` is preserved verbatim:

  `Auth (.own one) m₁ • Frag k (.own one) v  ~~>  `
  `Auth (.own one) (insert m₁ k v) • Frag k (.own one) v`,

an instance of `HeapView.update_replace` (`Iris/Algebra/HeapView.lean`): the new cell value
is valid because `✓ v` already held, and the update is stated purely through `get?`/`insert`,
never term equality.  Because `insert` re-stores the *constant* double sequence (product-
filter germ value `v`) while the underlying storage may have been refreshed along an entire
row, the rewrite is observationally an identity on the CMRA element.  More generally,
`HeapView.update_of_local_update` lifts any local update `(v, v) ~l~> (v, v')` on the germ
values; the "thin-cross refinement" of the representative is invisible to the CMRA precisely
because every HeapView operation only sees the product-filter germ via `eventualValueProd`. -/

section Applicability

open ProductGermMap

/-- **Product-filter-germ invariance under thin-cross refinement**, machine-checked.
Replacing the constant double sequence at a key by *any* double sequence agreeing with it
eventually along the product filter (i.e. off a filter-negligible thin cross) yields an
`equiv` map.  Such a rewrite is therefore frame-preserving for every `HeapView` update built
on this instance (it is the denotation-level content of
`update_replace`/`update_of_local_update`), and it permits refining along an **infinite**
slice — strictly more than the finite-prefix refinement available to `GermMap`. -/
theorem refine_thin_cross_equiv (m : ProductGermMap V) (k : ℕ) (v : V) {s : Idx → V}
    (hs : s =ᶠ[atTop] (fun _ => v)) :
    PartialMap.equiv (PartialMap.insert m k v) (fun k' => if k = k' then some s else m k') := by
  intro k'
  show ((ProductGermMap.insert m k v) k').bind eventualValueProd
    = ((fun k' => if k = k' then some s else m k') k').bind eventualValueProd
  by_cases hk : k = k'
  · simp only [ProductGermMap.insert, if_pos hk, Option.bind_some]
    rw [eventualValueProd_const, eventualValueProd_of_eventuallyEq hs]
  · simp only [ProductGermMap.insert, if_neg hk]

end Applicability

end IrisMath.Instances
