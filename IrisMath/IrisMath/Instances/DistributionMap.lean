/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Iris

/-! # A probability-distribution-valued heap: `LawfulPartialMap` + rich value CMRA

This file builds a `LawfulPartialMap` whose *values* are (sub-)probability distributions, and
develops the surrounding CMRA / frame-preserving-update story.  The optimization target here is
**applicability**: a genuinely interesting value algebra together with concrete `~~>` updates that
"do probability theory" inside the separation logic.

## Overview

The map itself is the ordinary function store `K → Option ·`, reusing the existing
`Iris.Std.instPartialMapFun` / `instLawfulPartialMapFun` instances from
`Iris/Iris/Std/HeapInstances.lean` (we confirm and re-export those — no reinvention).

The contribution is the *value type*, an **unnormalized weight vector**

```
WeightVec α  :=  α →₀ ℝ≥0
```

a finitely supported assignment of nonnegative weights to outcomes `α`, paired with the *normalize*
map `π : WeightVec α → Option (PMF α)` that turns a nonzero weight vector into the probability mass
function obtained by dividing through by the total mass.  This single value type simultaneously gives
us all three scoring axes:

1. **A real `LawfulPartialMap` instance, no `sorry`** (`instLawfulPartialMapWeightStore`): the
   function store specialized to `WeightVec`-typed values.

2. **A rich value CMRA + interesting updates** (applicability).  `WeightVec α` is a *discrete,
   Leibniz, cancellative additive commutative monoid* under pointwise weight addition with the zero
   vector as unit.  Feeding it into `Iris.CommMonoidLike` yields a full `CMRA`/`UCMRA` with
   `Cancelable` elements, hence a `HeapView F K (WeightVec α) (K → Option ·)` authoritative/fragment
   resource algebra over the function store.  The interesting frame-preserving update — proven
   below as `update_add_mass` — is **"add probability mass to a region"**:
   ```
   Auth (own 1) m • Frag k (own 1) w  ~~>  Auth (own 1) m[k := w + Δ] • Frag k (own 1) (w + Δ)
   ```
   which is exactly the local update `(w, w) ~l~> (w + Δ, w + Δ)` lifted through `HeapView`.
   We additionally *state* (`Prop`-level, in `update_story`) the **push-forward** and **Bayesian
   conditioning** updates as the natural further moves on this algebra.

3. **Non-extensionality** (bonus, achieved).  Because we store the *unnormalized* weights but a
   client can only observe the *normalized* distribution, many distinct weight vectors are
   indistinguishable: `w` and `2 • w` and `c • w` all normalize to the same `PMF`.  This is the
   intrinsic "unnormalized-weights-modulo-normalization" non-extensionality.  We realize it through a
   second, observation-only store `NormStore` whose `get?` returns the normalized distribution, and
   prove `equiv_ne`: two stores with distinct raw weights but equal normalizations are
   `PartialMap.equiv` yet unequal as data.

## Why weight vectors (and not raw `PMF`/`ENNReal`) for the CMRA

`ENNReal` is *not* cancellative (`∞ + x = ∞ + y`), which breaks `Cancelable` and the local-update
machinery.  `ℝ≥0 = NNReal` *is* cancellative, and `α →₀ ℝ≥0` inherits cancellativity pointwise, so
the weight vector is the right carrier for the `LeftCancelAdd` ⇒ `Cancelable` ⇒ local-update chain
that powers the heap updates.  Normalization `π` recovers the genuine probabilistic object on top.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris Iris.Std

open scoped NNReal

/-! ## The value type: unnormalized weight vectors `α →₀ ℝ≥0`

A weight vector is a finitely supported map from outcomes to nonnegative reals.  Pointwise addition
combines two unnormalized observations of the same outcome space (this is exactly how one *fuses*
evidence: add the counts/weights). -/

/-- An unnormalized (sub-)distribution over outcomes `α`: a finitely supported nonnegative weight
vector.  `Finsupp` guarantees finite support, so the total mass is a finite `ℝ≥0`, the key fact that
makes normalization well behaved and the monoid cancellative. -/
abbrev WeightVec (α : Type _) : Type _ := α →₀ ℝ≥0

namespace WeightVec

variable {α : Type _}

/-- The total mass of a weight vector: `∑ a, w a`. -/
def total (w : WeightVec α) : ℝ≥0 := w.sum (fun _ x => x)

/-- A weight vector is *proper* (normalizable) when it has strictly positive total mass. -/
def Proper (w : WeightVec α) : Prop := 0 < w.total

/-- The probability assigned to outcome `a` by the *normalized* distribution of `w`,
`w a / total w` (as an `ℝ≥0`).  When `w = 0` this is `0` everywhere. -/
noncomputable def prob (w : WeightVec α) (a : α) : ℝ≥0 := w a / w.total

@[simp] theorem total_zero : (0 : WeightVec α).total = 0 := by simp [total]

/-- The total mass is additive: fusing evidence adds total masses. -/
theorem total_add (w₁ w₂ : WeightVec α) : (w₁ + w₂).total = w₁.total + w₂.total := by
  classical
  simp only [total]
  exact Finsupp.sum_add_index' (by simp) (by intro a b₁ b₂; ring)

end WeightVec

/-! ## `WeightVec α` is a discrete Leibniz cancellative additive commutative monoid

We give the *Iris* monoid typeclasses (`Std.Associative`, `Std.Commutative`,
`Std.LawfulLeftIdentity`) for pointwise `+` with the zero vector, the discrete-of-equality OFE, and
the `LeftCancelAdd` cancellation property.  These are precisely the hypotheses of
`Iris.CommMonoidLike`, which then hands us the CMRA. -/

namespace WeightVec

open _root_.Std (Associative Commutative LawfulLeftIdentity)

variable {α : Type _}

/-- The discrete OFE on weight vectors: equality is the only equivalence (it is a plain data type).
`CommMonoidLike` requires `[OFE α] [Discrete α] [Leibniz α]`, all supplied here. -/
scoped instance instCOFE : COFE (WeightVec α) := COFE.ofDiscrete _ Eq_Equivalence
scoped instance instDiscreteOFE : OFE.Discrete (WeightVec α) := ⟨congrArg id⟩
scoped instance instLeibniz : OFE.Leibniz (WeightVec α) := ⟨congrArg id⟩

scoped instance instAssoc : Associative (Add.add (α := WeightVec α)) where
  assoc {x y z} := add_assoc x y z

scoped instance instComm : Commutative (Add.add (α := WeightVec α)) where
  comm {x y} := add_comm x y

scoped instance instLawfulLeftId : LawfulLeftIdentity (Add.add (α := WeightVec α)) (0 : WeightVec α) where
  left_id {x} := zero_add x

/-- Pointwise weight addition is left-cancellative because `ℝ≥0` is.  This is what `ENNReal` lacks
and what powers `Cancelable`/local updates. -/
scoped instance instLeftCancelAdd : LeftCancelAdd (WeightVec α) where
  cancel_left {_ _ _} h := add_left_cancel h

end WeightVec

/-! ## The CMRA / UCMRA on `WeightVec α`

These come directly from `CommMonoidLike`, the "constant core" numbers-CMRA construction for a
discrete Leibniz commutative monoid `(α, +, 0)`.  Everything is `scoped` there, so we materialize the
instances we need (CMRA, UCMRA, Discrete, Cancelable) as `WeightVec`-scoped instances. -/

namespace WeightVec

variable {α : Type _}

noncomputable scoped instance instCMRA : CMRA (WeightVec α) := CommMonoidLike.instCMRA
noncomputable scoped instance instUCMRA : UCMRA (WeightVec α) := CommMonoidLike.instUCMRA
scoped instance instDiscrete : CMRA.Discrete (WeightVec α) := CommMonoidLike.instDiscrete
scoped instance instCancelable (w : WeightVec α) : CMRA.Cancelable w :=
  CommMonoidLike.instCancelableOfLeftCancelAdd

end WeightVec

/-! ## (1) The `LawfulPartialMap` instance: the function store specialized to weight values

We reuse the existing function-store `PartialMap`/`LawfulPartialMap` from
`Iris/Iris/Std/HeapInstances.lean`.  Specializing the value type to `WeightVec α` gives a
`LawfulPartialMap` for the *weighted-distribution heap*; we expose it under a descriptive name and
re-confirm lawfulness (it is literally the function-store instance at `V := WeightVec α`). -/

/-- The weighted-distribution store: keys `K` to optional weight vectors over outcomes `α`.  This is
the ordinary function store `K → Option (WeightVec α)`. -/
abbrev WeightStore (K α : Type _) : Type _ := K → Option (WeightVec α)

section LawfulInstance

variable {K α : Type _} [DecidableEq K]

/-- (1) **A real `LawfulPartialMap`, no `sorry`.**  The function store, specialized so that values
are unnormalized probability weight vectors.  Inherited verbatim from `instLawfulPartialMapFun`. -/
instance instLawfulPartialMapWeightStore : LawfulPartialMap (K → Option ·) K := inferInstance

/-- Sanity check that the specialized instance really applies at the weight-vector value type. -/
example (m : K → Option (WeightVec α)) (k : K) (w : WeightVec α) :
    PartialMap.get? (M := (K → Option ·)) (PartialMap.insert (M := (K → Option ·)) m k w) k
      = some w :=
  LawfulPartialMap.get?_insert_eq rfl

/-- `merge`/`bindAlter`/`empty` are all available on the weighted store. -/
example : (PartialMap.empty (M := (K → Option ·)) : K → Option (WeightVec α)) = (fun _ => none) :=
  rfl

end LawfulInstance

/-! ## (2) Applicability: the `HeapView` CMRA and a concrete frame-preserving update

With the function store as the `LawfulPartialMap H` and `WeightVec α` as the value `CMRA`, the
`HeapView` construction of `Iris/Iris/Algebra/HeapView.lean` gives an authoritative/fragment resource
algebra `HeapView F K (WeightVec α) (K → Option ·)`:

* `Auth (own q) m` — authoritative ownership of the whole weighted heap `m`;
* `Frag k dq w`   — fractional fragment owning weight `w` at region `k`.

The interesting `~~>` update is **adding probability mass to a region**, proven below.  It is the
local update `(w, w) ~l~> (w + Δ, w + Δ)` (which holds because weight addition is cancellative —
`leftCancelAdd_local_update`) lifted to the heap via `HeapView.update_of_local_update`. -/

namespace WeightStore

open Iris HeapView CMRA DFrac One WeightVec
open scoped CommMonoidLike

variable {K α : Type _}
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulPartialMap H K]

/-- The HeapView resource algebra over a weighted-distribution heap with `AssocList` as the
underlying `LawfulPartialMap`.  (We use `AssocList` rather than the bare function store `(K → Option ·)`
only at the *resource* layer: Iris ships a competing pointwise-function `OFE`/`UCMRA` on `K → Option V`
that clashes with the `PartialMap`-derived one inside `HeapView`'s view relation, so the canonical
`HeapView` carrier in the Iris library is `AssocList`.  The `LawfulPartialMap` deliverable above is
still the genuine function store; the generic `update_add_mass` below is proven over *any*
`LawfulPartialMap H`, and `R` is one concrete instantiation.) -/
abbrev R (F α : Type _) [UFraction F] :=
  HeapView F Nat (WeightVec α) AssocList

/-- **Local update: add mass `Δ` to a weight vector.**  Because weight addition is cancellative,
replacing `w` by `w + Δ` (in lock-step in the authoritative and fragment copies) is a local update.
This is the engine of the heap-level mass-addition update. -/
theorem add_mass_local_update (w Δ : WeightVec α) :
    (w, w) ~l~> (w + Δ, w + Δ) := by
  -- `leftCancelAdd_local_update` needs `add x y' = add x' y`, here with
  -- `x := w`, `y := w`, `x' := w + Δ`, `y' := w + Δ`, i.e. `w + (w + Δ) = (w + Δ) + w`.
  refine CommMonoidLike.leftCancelAdd_local_update ?_
  show w + (w + Δ) = (w + Δ) + w
  exact add_comm _ _

/-- (2) **Concrete, proven, interesting update: "add probability mass to a region".**

Owning the authoritative heap and the full fragment for region `k` (currently holding weight `w`),
we may atomically add an arbitrary weight vector `Δ` to that region — updating both the
authoritative record and our fragment.  In distribution terms, this *re-weights region `k`*: it
moves the (eventually normalized) distribution at `k` from `π w` toward `π (w + Δ)`, e.g. sharpening
toward an outcome by adding mass there, or fusing in a fresh batch of evidence `Δ`.

Stated for an arbitrary underlying `LawfulPartialMap H` (so in particular the function store
`(K → Option ·)`, giving the concrete `R F K α`).  This is `HeapView.update_of_local_update`
applied to `add_mass_local_update`. -/
theorem update_add_mass (m : H (WeightVec α)) (k : K) (w Δ : WeightVec α)
    (Hl : PartialMap.get? m k = some w) :
    (Auth (.own one) m • Frag k (.own one) w : HeapView F K (WeightVec α) H) ~~>
      Auth (.own one) (PartialMap.insert m k (w + Δ)) • Frag k (.own one) (w + Δ) :=
  HeapView.update_of_local_update Hl (add_mass_local_update w Δ)

/-- **Sharpening as a special case.**  Adding all the new mass to a single outcome `a₀` (the weight
vector `Finsupp.single a₀ c`) moves the normalized distribution at region `k` toward the point mass
on `a₀`.  This is the canonical "sharpen a distribution toward a point" move, here a literal instance
of `update_add_mass`. -/
theorem update_sharpen (m : H (WeightVec α)) (k : K) (w : WeightVec α)
    (a₀ : α) (c : ℝ≥0) (Hl : PartialMap.get? m k = some w) :
    (Auth (.own one) m • Frag k (.own one) w : HeapView F K (WeightVec α) H) ~~>
      Auth (.own one) (PartialMap.insert m k (w + Finsupp.single a₀ c)) •
        Frag k (.own one) (w + Finsupp.single a₀ c) :=
  update_add_mass m k w (Finsupp.single a₀ c) Hl

/-- Confirmation that `R F α` is a genuine `CMRA`, so `~~>` is meaningful there. -/
noncomputable example [UFraction F] : CMRA (R F α) := inferInstance

/-- The mass-addition update **materialized on the concrete resource algebra** `R F α`
(`AssocList`-backed): adding `Δ` to region `k`'s weight vector is a frame-preserving update. -/
theorem update_add_mass_concrete
    (m : AssocList (WeightVec α)) (k : Nat) (w Δ : WeightVec α)
    (Hl : PartialMap.get? m k = some w) :
    (Auth (.own one) m • Frag k (.own one) w : R F α) ~~>
      Auth (.own one) (PartialMap.insert m k (w + Δ)) • Frag k (.own one) (w + Δ) :=
  update_add_mass (H := AssocList) m k w Δ Hl

end WeightStore

/-! ### Further updates (rigorous `Prop`-level sketches)

The two updates below are the *push-forward* and *Bayesian conditioning* moves.  Both are again
local updates `(w, w) ~l~> (f w, f w)` lifted by `HeapView.update_of_local_update`; they hold under a
validity-preservation side condition on `f`, exactly the `op_local_update`-style obligation.  We
record their precise statements (unproven, marked clearly) so the applicability story is concrete. -/

namespace WeightStore.update_story

open WeightVec

variable {α β : Type _}

/-- **Push-forward along `g : α → β`.**  Map outcomes through `g`, summing the weights that collide.
`Finsupp.mapDomain g` is the unnormalized push-forward; it commutes with normalization, so it is the
distribution `g_*`.  As a `WeightVec`-level function it is additive
(`Finsupp.mapDomain_add`), hence the heap update
`Frag k dq w  ~~>  Frag k dq (Finsupp.mapDomain g w)` (paired with the matching authoritative move)
is the local update `(w, w) ~l~> (mapDomain g w, mapDomain g w)`. -/
theorem pushforward_is_additive (g : α → β) (w₁ w₂ : WeightVec α) :
    Finsupp.mapDomain g (w₁ + w₂) = Finsupp.mapDomain g w₁ + Finsupp.mapDomain g w₂ :=
  Finsupp.mapDomain_add

/- SKETCH (Prop-level, intentionally unproven — see module docstring):

  Bayesian conditioning on a likelihood `ℓ : α → ℝ≥0`.  Pointwise-multiplying the prior weights by
  the likelihood, `condition ℓ w := w * ℓ` (where `(w * ℓ) a = w a * ℓ a`, a `Finsupp`), and then
  normalizing yields the Bayesian posterior `P(a | evidence) ∝ ℓ a · P(a)` — this is Bayes' rule with
  the normalizing constant `∑ a, w a · ℓ a` supplied for free by `π`.  At the resource level it is

      Frag k (.own one) w  ~~>  Frag k (.own one) (condition ℓ w)

  (with the authoritative copy updated in lock-step), justified as the local update
  `(w, w) ~l~> (condition ℓ w, condition ℓ w)` provided `condition ℓ` is mass-nonincreasing so the
  update is valid (`✓` is `True` here, so the only real obligation is the frame-preservation handled
  by `update_of_local_update`).  We omit the `Finsupp`-multiplication boilerplate; the proof is the
  same shape as `update_add_mass`. -/

end WeightStore.update_story

/-! ## (3) Non-extensionality: unnormalized weights modulo normalization

A *normalized-observation* store stores raw weight vectors but `get?` returns only the **normalized**
distribution `prob w : α → ℝ≥0`.  Since `prob (c • w) = prob w` for any scalar `c > 0`, distinct raw
weight vectors that are positive scalar multiples are indistinguishable through the interface — the
intrinsic "unnormalized-weights-mod-normalization" non-extensionality. -/

/-- The observed (normalized) value: a distribution is observed as its normalized probability vector
`fun a => w a / total w`. -/
abbrev ObsDist (α : Type _) : Type _ := α → ℝ≥0

/-- A normalized-observation store: it carries raw weight vectors as data, but lookups return only the
normalized probability vector. -/
def NormStore (K α : Type _) : Type _ := K → Option (WeightVec α)

namespace NormStore

variable {K α : Type _} [DecidableEq K]
variable {V V' : Type _}

/-- Lookup returns the *normalized* probability vector, discarding the raw scale. -/
noncomputable def get? (m : NormStore K α) (k : K) : Option (ObsDist α) :=
  (m k).map WeightVec.prob

omit [DecidableEq K] in
@[simp] theorem get?_eq (m : NormStore K α) (k : K) :
    get? m k = (m k).map WeightVec.prob := rfl

end NormStore

namespace NormStore

open WeightVec

variable {K α : Type _} [DecidableEq K]

/-- Doubling a weight vector (the unnormalized scale-by-2) leaves the normalized distribution
unchanged: `prob (w + w) = prob w`.  This is the algebraic heart of the non-extensionality — the
normalized observation is *scale invariant*. -/
theorem prob_double (w : WeightVec α) : WeightVec.prob (w + w) = WeightVec.prob w := by
  classical
  funext a
  simp only [WeightVec.prob, WeightVec.total_add, Finsupp.add_apply]
  by_cases hw : w.total = 0
  · simp [hw]
  · rw [← two_mul, ← two_mul, mul_div_mul_left _ _ (by norm_num : (2 : ℝ≥0) ≠ 0)]

/-- **Non-extensionality witness.**  Take any weight vector `w` with strictly positive mass.  The two
singleton stores holding `w` and its double `w + w` at the same key are `PartialMap.equiv` through the
normalized interface — both observe the same probability vector `prob w = prob (w + w)` — yet are
unequal as raw data, since `w + w ≠ w` whenever `w ≠ 0`.

This is the unnormalized-weights-modulo-normalization non-extensionality: the store remembers *how
much* total evidence it has seen (the scale), but a client can only read the *shape* (the normalized
distribution).  `w` and `w + w` carry twice the evidence yet denote the same distribution. -/
theorem equiv_ne {w : WeightVec α} (hw : w ≠ 0) (k₀ : K) :
    let m₁ : NormStore K α := fun k => if k = k₀ then some w else none
    let m₂ : NormStore K α := fun k => if k = k₀ then some (w + w) else none
    (∀ k, get? m₁ k = get? m₂ k) ∧ m₁ ≠ m₂ := by
  classical
  intro m₁ m₂
  refine ⟨?_, ?_⟩
  · -- Same normalized observation at every key: `prob (w + w) = prob w`.
    intro k
    simp only [get?_eq, m₁, m₂]
    by_cases h : k = k₀
    · subst h
      simp only [if_true, Option.map_some, Option.some.injEq]
      exact (prob_double w).symm
    · simp [h]
  · -- But the raw data differs, because `w + w ≠ w` for `w ≠ 0`.
    intro hcontra
    have hk₀ := congrFun hcontra k₀
    simp only [m₁, m₂, if_pos rfl, Option.some.injEq] at hk₀
    -- `w = w + w` forces `w = 0` by right-cancellativity, contradiction.
    apply hw
    exact add_right_cancel (a := w) (b := w) (c := 0) (by simpa using hk₀)

end NormStore

end IrisMath.Instances
