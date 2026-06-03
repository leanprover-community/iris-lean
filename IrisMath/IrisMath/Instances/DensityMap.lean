/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Iris

/-! # A non-extensional `LawfulPartialMap`: densities observed modulo a.e. equality

This file constructs a `LawfulPartialMap` whose values are *densities* on a measure space,
observed only up to almost-everywhere equality.  This is the Radon–Nikodym flavour requested in
the prototype: a value is a function `Ω → ℝ≥0∞` (an `ENNReal`-valued density), and two densities
that agree `μ`-almost-everywhere induce the same measure `μ.withDensity f`, hence are
*indistinguishable* through the map even though they differ as raw functions.

## The observed value type

We observe densities through the filter germ along the a.e. filter `μ.ae`:
`Filter.Germ μ.ae ℝ≥0∞`.  By `Filter.Germ.coe_eq`, two raw densities coerce to the *same* germ
iff they are `=ᵐ[μ]` equal:
`(↑f = ↑g) ↔ f =ᵐ[μ] g`.
This already gives non-extensionality and avoids every measurability side condition that
`MeasureTheory.AEEqFun` would force on us (we never need `AEStronglyMeasurable`).

## The representation

`DensityMap V := K → Option (V × (Ω → ℝ≥0∞))`.

Each entry carries the observed value `v : V` *together with a raw density representative*
`r : Ω → ℝ≥0∞`.  The lookup `get?` projects out only the observed value (`Prod.fst`), discarding the
raw representative.  Consequently `get?` cannot see which raw density was stored, and two maps that
store `=ᵐ[μ]`-equal-but-distinct raw densities are `PartialMap.equiv` yet unequal as data — this is
the non-extensionality theorem `equiv_ne` below.

`merge` adds the raw density representatives pointwise (`r₁ + r₂`), which under
`μ.withDensity` corresponds to *addition of the induced measures*
(`μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g`).  When `V` itself is the germ
`Filter.Germ μ.ae ℝ≥0∞`, the observed value also adds via the germ monoid, so the construction is
coherent: the value monoid is `(Ω → ℝ≥0∞, +)` quotiented to germs, a canonically ordered
commutative monoid — exactly the shape that yields a well-behaved CMRA.

## Applicability (HeapView CMRA sketch)

`ENNReal` is a `CanonicallyOrderedAddCommMonoid`; pointwise it lifts to densities, and the germ
quotient `Filter.Germ μ.ae ℝ≥0∞` inherits a `CommMonoid` (additive) structure.  Feeding this value
monoid into the `HeapView` construction of `Iris/Iris/Algebra/HeapView.lean` (the
authoritative/fragment heap RA over a `LawfulPartialMap`), a fragment `◯ {[k := ⟦f⟧]}` owns the
density at region `k`, and the authoritative element tracks the total density.

The interesting frame-preserving updates `~~>` are exactly the ones that move within an a.e. class:

* **Modify the density on a null set.**  If `s` is `μ`-null and `g` agrees with `f` off `s`, then
  `⟦f⟧ = ⟦g⟧` (by `Filter.Germ.coe_eq`), so
  `◯ {[k := ⟦f⟧]} ~~> ◯ {[k := ⟦g⟧]}`
  is the identity update on the observed resource — frame preserving because the induced measure
  `μ.withDensity f = μ.withDensity g` is unchanged.

* **Add mass to a region.**  Adding a density `h` to region `k` is the monoid step
  `⟦f⟧ ↝ ⟦f⟧ + ⟦h⟧`, mirroring `μ.withDensity f ↝ μ.withDensity f + μ.withDensity h`; under the
  HeapView authoritative/fragment split this is a local update of the `k` cell.

One concrete update statement (informal): for `f =ᵐ[μ] g`,
`HeapView.frag {[k := ⟦f⟧]} ~~> HeapView.frag {[k := ⟦g⟧]}`, valid because the observed germs are
equal so the global resource is literally unchanged.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std MeasureTheory

variable {Ω : Type _} [MeasurableSpace Ω] (μ : Measure Ω)
variable {K : Type _} [DecidableEq K]

/-- A raw density on the measure space: an `ℝ≥0∞`-valued function on `Ω`. -/
abbrev RawDensity (Ω : Type _) := Ω → ENNReal

/-- The observed value type: densities modulo `μ`-almost-everywhere equality, realized as the
filter germ along `μ.ae`.  Two raw densities coerce to the same `AEDensity` iff they are
`=ᵐ[μ]`-equal. -/
abbrev AEDensity (Ω : Type _) [MeasurableSpace Ω] (μ : Measure Ω) : Type _ :=
  Filter.Germ (MeasureTheory.ae μ) ENNReal

/-- The carrier: a partial map from keys to a pair of (observed value, raw density representative).
The raw density is non-observed bookkeeping that makes the construction non-extensional. -/
def DensityMap (Ω : Type _) (V : Type _) : Type _ := K → Option (V × RawDensity Ω)

namespace DensityMap

variable {V V' : Type _}

/-- Lookup discards the raw density representative, observing only the value `V`. -/
def get? (m : DensityMap (K := K) Ω V) (k : K) : Option V := (m k).map Prod.fst

/-- Insert stores the value together with the everywhere-zero raw density representative. -/
def insert (m : DensityMap (K := K) Ω V) (k : K) (v : V) : DensityMap (K := K) Ω V :=
  fun k' => if k = k' then some (v, fun _ => 0) else m k'

/-- Delete drops the entry at `k`. -/
def delete (m : DensityMap (K := K) Ω V) (k : K) : DensityMap (K := K) Ω V :=
  fun k' => if k = k' then none else m k'

/-- The empty density map. -/
def empty : DensityMap (K := K) Ω V := fun _ => none

/-- `bindAlter` transforms observed values, keeping the raw density representative. -/
def bindAlter (f : K → V → Option V') (m : DensityMap (K := K) Ω V) :
    DensityMap (K := K) Ω V' :=
  fun k => (m k).bind fun (v, r) => (f k v).map fun v' => (v', r)

/-- `merge` combines observed values via `op` and *adds* the raw density representatives,
mirroring addition of the induced measures `μ.withDensity (r₁ + r₂)`. -/
noncomputable def merge (op : K → V → V → V) (m₁ m₂ : DensityMap (K := K) Ω V) :
    DensityMap (K := K) Ω V :=
  fun k =>
    match m₁ k, m₂ k with
    | none, none => none
    | some x, none => some x
    | none, some y => some y
    | some (v₁, r₁), some (v₂, r₂) => some (op k v₁ v₂, r₁ + r₂)

/-- `DensityMap` is a `PartialMap`. -/
noncomputable instance instPartialMap : PartialMap (DensityMap (K := K) Ω) K where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

omit [MeasurableSpace Ω] in
@[simp] theorem get?_eq (m : DensityMap (K := K) Ω V) (k : K) :
    PartialMap.get? m k = (m k).map Prod.fst := rfl

/-- `DensityMap` satisfies all seven `LawfulPartialMap` laws. -/
noncomputable instance instLawfulPartialMap : LawfulPartialMap (DensityMap (K := K) Ω) K where
  get?_empty := by intro V k; rfl
  get?_insert_eq := by
    intro V m k k' v h
    simp only [get?_eq, PartialMap.insert, insert, if_pos h]
    simp [Option.map]
  get?_insert_ne := by
    intro V m k k' v h
    simp only [get?_eq, PartialMap.insert, insert, if_neg h]
  get?_delete_eq := by
    intro V m k k' h
    simp only [get?_eq, PartialMap.delete, delete, if_pos h]
    rfl
  get?_delete_ne := by
    intro V m k k' h
    simp only [get?_eq, PartialMap.delete, delete, if_neg h]
  get?_bindAlter := by
    intro V V' k m f
    simp only [get?_eq, PartialMap.bindAlter, bindAlter]
    cases h : m k with
    | none => simp
    | some p =>
      obtain ⟨v, r⟩ := p
      cases hf : f k v <;> simp [hf]
  get?_merge := by
    intro V op m₁ m₂ k
    simp only [get?_eq, PartialMap.merge, merge]
    cases h₁ : m₁ k with
    | none => cases h₂ : m₂ k <;> simp [Option.merge]
    | some p₁ =>
      obtain ⟨v₁, r₁⟩ := p₁
      cases h₂ : m₂ k with
      | none => simp [Option.merge]
      | some p₂ => obtain ⟨v₂, r₂⟩ := p₂; simp [Option.merge]

end DensityMap

/-! ## Non-extensionality

Two density maps that store the *same observed germ value* but *different raw density
representatives* are `PartialMap.equiv` (they agree on every `get?`) yet are unequal as data,
whenever the two raw densities are `=ᵐ[μ]`-equal but distinct as functions. -/

namespace DensityMap

open Filter

variable {K : Type _} [DecidableEq K]

/-- **Non-extensionality witness.**  Suppose `f g : Ω → ℝ≥0∞` agree `μ`-almost everywhere
(`f =ᵐ[μ] g`) but differ as raw functions (`f ≠ g`).  Pick any key `k₀`.  Form the two singleton
density maps storing the *observed germs* `⟦f⟧` and `⟦g⟧` paired with the *distinct raw
representatives* `f` and `g`.  These are pointwise equivalent through the interface — precisely
because the a.e.-equality `hae` collapses `⟦f⟧ = ⟦g⟧` (the Radon–Nikodym observation) — yet they
are unequal as underlying data, since `f ≠ g`. -/
theorem equiv_ne (μ : Measure Ω) {f g : RawDensity Ω}
    (hae : f =ᵐ[μ] g) (hne : f ≠ g) (k₀ : K) :
    let m₁ : DensityMap (K := K) Ω (AEDensity Ω μ) :=
      fun k => if k = k₀ then some ((↑f : AEDensity Ω μ), f) else none
    let m₂ : DensityMap (K := K) Ω (AEDensity Ω μ) :=
      fun k => if k = k₀ then some ((↑g : AEDensity Ω μ), g) else none
    PartialMap.equiv m₁ m₂ ∧ m₁ ≠ m₂ := by
  intro m₁ m₂
  -- The germs coincide because `f =ᵐ[μ] g`.
  have hgerm : (↑f : AEDensity Ω μ) = (↑g : AEDensity Ω μ) := Filter.Germ.coe_eq.mpr hae
  refine ⟨?_, ?_⟩
  · -- Equivalence through the interface: both observe the same germ at `k₀`, none elsewhere.
    intro k
    simp only [get?_eq, m₁, m₂]
    by_cases h : k = k₀ <;> simp [h, hgerm]
  · -- But the raw data differs at `k₀`, since `f ≠ g`.
    intro hcontra
    have hk₀ := congrFun hcontra k₀
    simp only [m₁, m₂, if_pos rfl] at hk₀
    -- `some (⟦f⟧, f) = some (⟦g⟧, g)` forces `f = g`, contradiction.
    have : f = g := (Prod.mk.injEq .. ▸ Option.some.injEq .. ▸ hk₀).2
    exact hne this

/-- Sanity check that the observed germs of `f` and `g` genuinely coincide: this is the
Radon–Nikodym observation that a.e.-equal densities are indistinguishable.  (Same germ ⇒ same
induced measure `μ.withDensity f = μ.withDensity g`.) -/
theorem germ_eq_of_ae {f g : RawDensity Ω} {μ : Measure Ω} (hae : f =ᵐ[μ] g) :
    (↑f : AEDensity Ω μ) = (↑g : AEDensity Ω μ) :=
  Filter.Germ.coe_eq.mpr hae

end DensityMap

end IrisMath.Instances
