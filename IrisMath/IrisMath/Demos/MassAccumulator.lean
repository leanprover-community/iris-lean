/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import IrisMath.Instances.MeasureValuedMap

/-! # Demo 4 — A weird problem: a heap whose cells hold *measures* and only ever accumulate mass

**The problem.**  Several parties concurrently contribute *evidence* (a histogram, a batch of
samples, a sub-probability weighting) to shared locations.  Each contribution should:
(a) be a real owned heap resource, with separation-logic framing and transfer;
(b) combine *additively* — contributions fuse, never overwrite; and
(c) the underlying object should be a genuine mathematical measure, so downstream code can integrate
    against it, normalize it, push it forward along a measurable map, etc.

A standard `gmap ℕ Value` heap cannot do (b)/(c): its cells hold opaque values with no additive
structure, and "merge two owners' contributions" is not a heap operation.

**The solution.**  Use the auto-researcher's `MeasureValuedMap`: the `HeapView` heap whose value
CMRA is `MeasureTheory.Measure Ω` with `+` as the camera operation.  The *mathematics of measures*
(commutative-monoid addition, every measure valid) is exactly what makes the heap's `~~>` updates
behave like additive accumulation.  We lift the proven camera update `update_add_mass` to an `IProp`
fancy update: **owning a cell with mass `μ`, a party may fuse a fresh batch `ν`, atomically updating
the cell to `μ + ν`.**  This is the heap-level rule a verifier of an evidence-accumulation protocol
would use.
-/

@[expose] public section

namespace IrisMath.Demos.MassAccumulator

open Iris Iris.BI COFE MeasureTheory
open HeapView One DFrac
open IrisMath.Instances IrisMath.Instances.MeasureStore
open scoped IrisMath.Instances.MeasureValuedMap

-- A fixed measurable space of outcomes, and a fraction type.
variable (F : Type _) (Ω : Type _) [UFraction F] [MeasurableSpace Ω]

/-- The heap container: the plain function store, with **measure values**.  (Non-extensionality is
not the point here; the richness of the *value CMRA* is.) -/
abbrev H := (Nat → Option ·)

/-- The heap functor: `constOF` of the generic `HeapView` CMRA over a measure-valued heap. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat (Measure Ω) H

variable {GF} [ElemG GF (HeapF F Ω)]

/-- Authoritative ownership of the whole measure heap. -/
noncomputable def auth (γ : GName) (m : H (Measure Ω)) : IProp GF :=
  iOwn (GF := GF) (F := HeapF F Ω) γ (Auth (own one) m)

/-- A points-to: region `k` currently carries the accumulated measure `μ`. -/
noncomputable def hasMass (γ : GName) (k : Nat) (μ : Measure Ω) : IProp GF :=
  iOwn (GF := GF) (F := HeapF F Ω) γ (Frag k (own one) μ)

/-- **Accumulate evidence (the protocol rule).**  Owning the authority and the full mass cell at
`k` (currently `μ`), a party may *fuse* a fresh batch of evidence `ν`: the cell, both in the
authoritative record and in the party's own fragment, becomes `μ + ν`.  The update is
frame-preserving because measures form a (valid) commutative monoid under `+` — pure mathematics
discharging the camera obligation.

This is `MeasureStore.update_add_mass` (a proven HeapView `~~>`) lifted to an `IProp` fancy update
via `iOwn_update`.  Iterating it accumulates `μ + ν₁ + ν₂ + …`: contributions fuse additively and
never overwrite. -/
theorem accumulate (γ : GName) (m : H (Measure Ω)) (k : Nat) (μ ν : Measure Ω) :
    auth (GF := GF) F Ω γ m ∗ hasMass (GF := GF) F Ω γ k μ ⊢
      |==> (auth (GF := GF) F Ω γ (Std.PartialMap.insert m k (μ + ν))
            ∗ hasMass (GF := GF) F Ω γ k (μ + ν)) := by
  refine iOwn_op.mpr.trans ?_
  refine (iOwn_update (γ := γ)
    (MeasureStore.update_add_mass (F := F) (H := H) m k μ ν)).trans ?_
  exact BIUpdate.mono iOwn_op.mp

/-! ## The point

`accumulate` is a perfectly ordinary separation-logic update rule — `auth ∗ k ↦ μ ⊢ |==> auth' ∗ k
↦ (μ+ν)` — and it is proved with no new metatheory: the generic `iOwn_update` plus the auto-
researcher's measure-valued camera.  What the *mathematics of measures* contributes is the meaning
and the validity of the update:
- the camera operation is **measure addition**, so the heap operation is genuine accumulation;
- **every measure is valid**, so the update never gets stuck on a validity side-condition;
- the stored object is a real `MeasureTheory.Measure Ω`, so the same fragment can subsequently be
  pushed forward, restricted, or normalized (the companion lemmas `update_pushforward`,
  `update_restrict` in `MeasureValuedMap.lean`).

An Iris researcher gets, for free from the framework, a heap whose cells are first-class measures
with additive, always-valid ownership — exactly the resource discipline a probabilistic /
evidence-accumulation program logic needs, and which the standard value heap cannot provide. -/

end IrisMath.Demos.MassAccumulator
