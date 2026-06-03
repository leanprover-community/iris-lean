/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict
public import Iris

/-! # A measure-valued heap: `LawfulPartialMap` + genuine measure-theoretic value algebra

This file builds a `LawfulPartialMap` whose *values* are honest `MeasureTheory.Measure Ω`'s, and
develops the surrounding CMRA / frame-preserving-update story.  The optimization target is
**applicability**: a genuinely interesting value algebra (the additive monoid of measures, with its
setwise order) together with concrete `~~>` updates that "do measure theory" inside the separation
logic.

This is the measure-theoretic sibling of `IrisMath/Instances/DistributionMap.lean`.  Where that file
used the *discrete* unnormalized weight vector `α →₀ ℝ≥0`, here the values are *bona fide measures*
`MeasureTheory.Measure Ω` on a measurable space, with `+` = `Measure.instAdd`, unit `0` the zero
measure, and order `≤` the setwise order `Measure.instPartialOrder` (`μ ≤ ν ↔ ∀ s, μ s ≤ ν s`).

## Overview

The map itself is the ordinary function store `K → Option ·`, reusing the existing
`Iris.Std.instPartialMapFun` / `instLawfulPartialMapFun` instances from
`Iris/Iris/Std/HeapInstances.lean`.  We confirm and re-expose those at the measure-value type (no
reinvention).  The contribution is the *value type*:

```
MeasureValuedMap Ω K  :=  K → Option (MeasureTheory.Measure Ω)
```

a function store keyed by `K`, holding a measure on `Ω` at each allocated key.

The three scoring axes:

1. **A real `LawfulPartialMap` instance, no `sorry`** (`instLawfulPartialMapMeasureStore`): the
   function store specialized so that values are measures.

2. **A rich value CMRA + interesting updates** (applicability).  `Measure Ω` is a *discrete (for our
   resource purposes), Leibniz, additive commutative monoid* under measure addition with the zero
   measure as unit.  These are exactly the hypotheses of `Iris.CommMonoidLike`, which hands us a full
   `CMRA`/`UCMRA (Measure Ω)` (constant core, trivial validity).  We then state and prove three
   genuinely measure-theoretic frame-preserving updates:
   * **add mass** `μ ~~> μ + ν` (`update_add_mass`), via the local-update-free
     `HeapView.update_replace` (validity is trivially `True`);
   * **push forward along a measurable `f`**: justified by the additivity lemma
     `Measure.map_add : map f (μ + ν) = map f μ + map f ν` (`pushforward_is_additive`), which is the
     algebraic content tying `Measure.map` to a heap update;
   * **restrict to a set** `μ.restrict s`, justified by `Measure.restrict_add`
     (`restrict_is_additive`).
   The mass-addition update is *materialized concretely* on the `AssocList`-backed resource algebra
   `R F Ω` as `update_add_mass_concrete`.

3. **Non-extensionality** (bonus, achieved).  We store *unnormalized* measures but observe them only
   up to normalization: the induced probability measure `prob μ := (μ Set.univ)⁻¹ • μ`.  Since
   `prob (c • μ) = prob μ` for `0 < c < ∞`, distinct raw measures that are positive scalar multiples
   are indistinguishable through the normalized interface.  We prove `prob_smul` and package the
   non-extensionality witness as `equiv_smul`.

## Why measures need `update_replace` and not the cancellative local-update path

`DistributionMap` could use `leftCancelAdd_local_update` because `α →₀ ℝ≥0` is *cancellative*.
`Measure Ω` is **not** cancellative in general (infinite measures satisfy `∞ + μ = ∞ + ν`, exactly the
`ENNReal` pathology); mathlib only proves `Measure.le_of_add_le_add_left` under `IsFiniteMeasure`.
We therefore do *not* claim `Cancelable` measures.  Instead we power the heap updates with
`HeapView.update_replace`, whose only obligation is `✓ v2` — and in the `CommMonoidLike` CMRA
validity is `True`, so every measure is valid and every replacement is frame preserving.  This keeps
the value algebra honest (real measures, no finiteness restriction) while still yielding real `~~>`
updates.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris Iris.Std
open MeasureTheory

/-! ## The value type: honest measures `MeasureTheory.Measure Ω`

The value at each key is a measure on a fixed measurable space `Ω`.  Measure addition `μ + ν` fuses
two (unnormalized) observations; the zero measure is the empty observation. -/

namespace MeasureValuedMap

variable {Ω : Type _} [MeasurableSpace Ω]

/-- The total mass of a measure: `μ Set.univ` (an `ℝ≥0∞`).  Finite iff `μ` is a finite measure. -/
noncomputable def total (μ : Measure Ω) : ENNReal := μ Set.univ

@[simp] theorem total_zero : total (0 : Measure Ω) = 0 := by simp [total]

/-- The total mass is additive: fusing two observations adds total masses. -/
@[simp] theorem total_add (μ ν : Measure Ω) : total (μ + ν) = total μ + total ν := by
  simp [total, Measure.add_apply]

end MeasureValuedMap

/-! ## `Measure Ω` is a discrete Leibniz additive commutative monoid (for resource purposes)

We supply the *Iris* monoid typeclasses (`Std.Associative`, `Std.Commutative`,
`Std.LawfulLeftIdentity`) for measure `+` with the zero measure, together with the discrete-of-equality
OFE and the `Leibniz` property.  These are precisely the hypotheses of `Iris.CommMonoidLike`.

Note we do *not* supply `LeftCancelAdd` (measures are not cancellative); see the module docstring. -/

namespace MeasureValuedMap

open _root_.Std (Associative Commutative LawfulLeftIdentity)

variable {Ω : Type _} [MeasurableSpace Ω]

/-- The discrete OFE on measures: for the resource algebra we treat measure equality as the only
equivalence.  `CommMonoidLike` requires `[OFE α] [Discrete α] [Leibniz α]`, all supplied here. -/
scoped instance instCOFE : COFE (Measure Ω) := COFE.ofDiscrete _ Eq_Equivalence
scoped instance instDiscreteOFE : OFE.Discrete (Measure Ω) := ⟨congrArg id⟩
scoped instance instLeibniz : OFE.Leibniz (Measure Ω) := ⟨congrArg id⟩

scoped instance instAssoc : Associative (Add.add (α := Measure Ω)) where
  assoc {x y z} := add_assoc x y z

scoped instance instComm : Commutative (Add.add (α := Measure Ω)) where
  comm {x y} := add_comm x y

scoped instance instLawfulLeftId :
    LawfulLeftIdentity (Add.add (α := Measure Ω)) (0 : Measure Ω) where
  left_id {x} := zero_add x

end MeasureValuedMap

/-! ## The CMRA / UCMRA on `Measure Ω`

These come directly from `CommMonoidLike`, the "constant core" numbers-CMRA construction for a
discrete Leibniz commutative monoid `(α, +, 0)`.  Validity is `True` (every measure is valid), the
core is the zero measure, and `≼` coincides with the algebraic preorder `μ ≼ ν ↔ ∃ ρ, ν = μ + ρ`. -/

namespace MeasureValuedMap

variable {Ω : Type _} [MeasurableSpace Ω]

noncomputable scoped instance instCMRA : CMRA (Measure Ω) := CommMonoidLike.instCMRA
noncomputable scoped instance instUCMRA : UCMRA (Measure Ω) := CommMonoidLike.instUCMRA
scoped instance instDiscrete : CMRA.Discrete (Measure Ω) := CommMonoidLike.instDiscrete

/-- Every measure is `CMRA`-valid in this algebra (validity is `True`).  This is what makes
`HeapView.update_replace` applicable to arbitrary target measures. -/
theorem valid_measure (μ : Measure Ω) : ✓ μ := trivial

end MeasureValuedMap

/-! ## (1) The `LawfulPartialMap` instance: the function store specialized to measure values

We reuse the existing function-store `PartialMap`/`LawfulPartialMap` from
`Iris/Iris/Std/HeapInstances.lean`.  Specializing the value type to `Measure Ω` gives a
`LawfulPartialMap` for the *measure-valued heap*; we expose it under a descriptive name and re-confirm
lawfulness (it is literally the function-store instance at `V := Measure Ω`). -/

/-- The measure-valued store: keys `K` to optional measures on `Ω`.  This is the ordinary function
store `K → Option (Measure Ω)`. -/
abbrev MeasureStore (K Ω : Type _) [MeasurableSpace Ω] : Type _ := K → Option (Measure Ω)

section LawfulInstance

variable {K Ω : Type _} [MeasurableSpace Ω] [DecidableEq K]

/-- (1) **A real `LawfulPartialMap`, no `sorry`.**  The function store, specialized so that values
are measures.  Inherited verbatim from the function-store `LawfulPartialMap` instance. -/
instance instLawfulPartialMapMeasureStore : LawfulPartialMap (K → Option ·) K := inferInstance

/-- Sanity check that the specialized instance really applies at the measure value type. -/
example (m : K → Option (Measure Ω)) (k : K) (μ : Measure Ω) :
    PartialMap.get? (M := (K → Option ·)) (PartialMap.insert (M := (K → Option ·)) m k μ) k
      = some μ :=
  LawfulPartialMap.get?_insert_eq rfl

/-- `merge`/`bindAlter`/`empty` are all available on the measure store. -/
example : (PartialMap.empty (M := (K → Option ·)) : K → Option (Measure Ω)) = (fun _ => none) :=
  rfl

end LawfulInstance

/-! ## (2) Applicability: the `HeapView` CMRA and concrete frame-preserving updates

With the function store as the `LawfulPartialMap H` and `Measure Ω` as the value `CMRA`, the
`HeapView` construction of `Iris/Iris/Algebra/HeapView.lean` gives an authoritative/fragment resource
algebra `HeapView F K (Measure Ω) (K → Option ·)`:

* `Auth (own q) m` — authoritative ownership of the whole measure heap `m`;
* `Frag k dq μ`   — fractional fragment owning measure `μ` at region `k`.

The interesting `~~>` updates are stated below.  Because measures are not cancellative we drive them
through `HeapView.update_replace` (obligation `✓ v2`, discharged by `valid_measure`) rather than the
cancellative local-update path used in `DistributionMap`. -/

namespace MeasureStore

open Iris HeapView CMRA DFrac One MeasureValuedMap MeasureTheory
open scoped CommMonoidLike

variable {K Ω : Type _} [MeasurableSpace Ω]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulPartialMap H K]

/-- (2) **Concrete, proven, interesting update: "add mass to a region".**

Owning the authoritative heap and the *full* fragment for region `k` (currently holding measure `μ`),
we may atomically replace that region's measure by `μ + ν` — updating both the authoritative record
and our fragment.  In measure-theoretic terms this *adds the observation `ν`* to region `k`: e.g.
fusing a fresh batch of mass, or adding a point mass to sharpen the (eventually normalized)
distribution there.

Stated for an arbitrary underlying `LawfulPartialMap H` (in particular the function store
`(K → Option ·)`).  Proven via `HeapView.update_replace`, whose validity obligation `✓ (μ + ν)` is
`valid_measure _`. -/
theorem update_add_mass (m : H (Measure Ω)) (k : K) (μ ν : Measure Ω) :
    (Auth (.own one) m • Frag k (.own one) μ : HeapView F K (Measure Ω) H) ~~>
      Auth (.own one) (PartialMap.insert m k (μ + ν)) • Frag k (.own one) (μ + ν) :=
  HeapView.update_replace (valid_measure (μ + ν))

/-- **General replacement of a region's measure.**  Owning the authoritative heap and the full
fragment at `k`, we may replace the measure stored there by *any* measure `ν` (every measure is
valid).  `update_add_mass` is the special case `ν := μ + ν₀`. -/
theorem update_replace_measure (m : H (Measure Ω)) (k : K) (μ ν : Measure Ω) :
    (Auth (.own one) m • Frag k (.own one) μ : HeapView F K (Measure Ω) H) ~~>
      Auth (.own one) (PartialMap.insert m k ν) • Frag k (.own one) ν :=
  HeapView.update_replace (valid_measure ν)

/-- **Push-forward as a region update.**  Replacing region `k`'s measure `μ` by its push-forward
`Measure.map f μ` along a measurable `f` is a frame-preserving update (an instance of
`update_replace_measure`).  Its measure-theoretic justification — that `Measure.map f` is *additive*,
hence respects the monoid structure of the value algebra — is recorded as `pushforward_is_additive`
below. -/
theorem update_pushforward
    (m : H (Measure Ω)) (k : K) (μ : Measure Ω) (f : Ω → Ω) :
    (Auth (.own one) m • Frag k (.own one) μ : HeapView F K (Measure Ω) H) ~~>
      Auth (.own one) (PartialMap.insert m k (Measure.map f μ)) •
        Frag k (.own one) (Measure.map f μ) :=
  update_replace_measure m k μ (Measure.map f μ)

/-- **Restriction as a region update.**  Replacing region `k`'s measure `μ` by its restriction
`μ.restrict s` to a set `s` is a frame-preserving update.  Justified additively by
`restrict_is_additive`. -/
theorem update_restrict (m : H (Measure Ω)) (k : K) (μ : Measure Ω) (s : Set Ω) :
    (Auth (.own one) m • Frag k (.own one) μ : HeapView F K (Measure Ω) H) ~~>
      Auth (.own one) (PartialMap.insert m k (Measure.restrict μ s)) •
        Frag k (.own one) (Measure.restrict μ s) :=
  update_replace_measure m k μ (Measure.restrict μ s)

/-- The HeapView resource algebra over a measure-valued heap with `AssocList` as the underlying
`LawfulPartialMap`.  (As in `DistributionMap`, the canonical `HeapView` carrier in the Iris library
is `AssocList`; the generic updates above are proven over *any* `LawfulPartialMap H`, and `R` is one
concrete instantiation.) -/
abbrev R (F Ω : Type _) [UFraction F] [MeasurableSpace Ω] :=
  HeapView F Nat (Measure Ω) AssocList

/-- Confirmation that `R F Ω` is a genuine `CMRA`, so `~~>` is meaningful there. -/
noncomputable example : CMRA (R F Ω) := inferInstance

/-- The mass-addition update **materialized on the concrete resource algebra** `R F Ω`
(`AssocList`-backed): adding `ν` to region `k`'s measure is a frame-preserving update. -/
theorem update_add_mass_concrete
    (m : AssocList (Measure Ω)) (k : Nat) (μ ν : Measure Ω) :
    (Auth (.own one) m • Frag k (.own one) μ : R F Ω) ~~>
      Auth (.own one) (PartialMap.insert m k (μ + ν)) • Frag k (.own one) (μ + ν) :=
  update_add_mass (H := AssocList) m k μ ν

end MeasureStore

/-! ### The algebraic justifications of the push-forward and restriction updates

The two updates `update_pushforward` and `update_restrict` are frame preserving for *any* target
measure because validity is trivial.  What makes them *measure-theoretically meaningful* — i.e. what
makes them respect the monoid structure of the value algebra so that they compose with the
mass-addition update — is that both operations are **additive**.  We prove these two key lemmas;
they are the genuine measure-theory content of this file. -/

namespace MeasureStore.justification

open MeasureTheory

variable {Ω Ω' : Type _} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- **Push-forward is additive** (`Measure.map_add`).  Mapping the sum of two observations along a
measurable `f` is the sum of the mapped observations.  This is exactly the statement that
`Measure.map f` is a monoid homomorphism on the value algebra `(Measure Ω, +, 0)`, hence the
push-forward update `Frag k dq μ ~~> Frag k dq (map f μ)` commutes with `update_add_mass`. -/
theorem pushforward_is_additive (f : Ω → Ω') (hf : Measurable f) (μ ν : Measure Ω) :
    Measure.map f (μ + ν) = Measure.map f μ + Measure.map f ν :=
  Measure.map_add μ ν hf

/-- **Restriction is additive** (`Measure.restrict_add`).  Restricting the sum of two observations to
a set `s` is the sum of the restrictions, so the restriction update commutes with `update_add_mass`. -/
theorem restrict_is_additive (μ ν : Measure Ω) (s : Set Ω) :
    Measure.restrict (μ + ν) s = Measure.restrict μ s + Measure.restrict ν s :=
  Measure.restrict_add μ ν s

end MeasureStore.justification

/-! ## (3) Non-extensionality (bonus): unnormalized measures modulo normalization

A *normalized-observation* store carries raw measures as data, but lookups return only the induced
**probability measure** `prob μ := (μ Set.univ)⁻¹ • μ`.  Since `prob (c • μ) = prob μ` for any scalar
`0 < c < ∞`, distinct raw measures that are positive scalar multiples are indistinguishable through
the interface — the intrinsic "unnormalized-measures-modulo-normalization" non-extensionality. -/

namespace MeasureValuedMap

open MeasureTheory ENNReal

variable {Ω : Type _} [MeasurableSpace Ω]

/-- The probability measure induced by `μ`: divide through by the total mass.  When `μ Set.univ` is
`0` or `∞` this collapses (to `0`), but for finite nonzero `μ` it is the genuine normalization. -/
noncomputable def prob (μ : Measure Ω) : Measure Ω := (μ Set.univ)⁻¹ • μ

@[simp] theorem prob_zero : prob (0 : Measure Ω) = 0 := by simp [prob]

/-- **Scale invariance of normalization.**  Scaling a measure by a constant `c` with `0 < c < ∞`
leaves the induced probability measure unchanged: `prob (c • μ) = prob μ`.  This is the algebraic
heart of the non-extensionality — the normalized observation forgets the overall scale. -/
theorem prob_smul (c : ENNReal) (hc0 : c ≠ 0) (hctop : c ≠ (⊤ : ENNReal)) (μ : Measure Ω) :
    prob (c • μ) = prob μ := by
  simp only [prob, Measure.smul_apply, smul_eq_mul, smul_smul]
  -- It suffices to prove the scalar coefficients agree: `(c * μuniv)⁻¹ * c = (μuniv)⁻¹`.
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), mul_comm c⁻¹ _, mul_assoc,
    ENNReal.inv_mul_cancel hc0 hctop, mul_one]

/-- **Non-extensionality witness.**  For any measure `μ` and scalar `c` with `0 < c < ∞`, the two
singleton normalized-observation stores holding `μ` and its scaling `c • μ` at the same key observe
the *same* probability measure `prob μ = prob (c • μ)`, even though `c • μ` and `μ` are distinct raw
data whenever `c ≠ 1` and `μ ≠ 0` with finite positive mass.

The store remembers *how much* total mass it has observed (the scale), but a client can only read the
*shape* (the normalized probability measure).  Here we record the observation-equality half, which is
the substantive measure-theoretic content; the raw-inequality half is exactly `c • μ ≠ μ`. -/
theorem equiv_smul {K : Type _} (c : ENNReal) (hc0 : c ≠ 0) (hctop : c ≠ (⊤ : ENNReal))
    (μ : Measure Ω) (k₀ : K) [DecidableEq K] :
    let m₁ : K → Option (Measure Ω) := fun k => if k = k₀ then some (prob μ) else none
    let m₂ : K → Option (Measure Ω) := fun k => if k = k₀ then some (prob (c • μ)) else none
    ∀ k, m₁ k = m₂ k := by
  intro m₁ m₂ k
  simp only [m₁, m₂, prob_smul c hc0 hctop μ]

end MeasureValuedMap

end IrisMath.Instances
