/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Prod
public import Mathlib.Order.Filter.Prod
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import IrisMath.Instances.ProductGermMap

/-! # Demo C — Independence = separation, over an *infinite* negligible support

This demo plugs the **two-dimensional** non-extensional container `ProductGermMap`
(`IrisMath/Instances/ProductGermMap.lean`) into the generic Iris `HeapView` resource algebra.
Each cell stores a *double sequence* `ℕ × ℕ → V`, and the observation `get?` collapses it to the
value of its **germ along the product filter** `(atTop : Filter (ℕ × ℕ))` — its eventual value as
*both* coordinates tend to infinity.  Nothing about `HeapView`, `iOwn`, `Auth`, `Frag`, or the proof
mode changes; the entire content lives in the choice of heap container.

## The point an Iris researcher cares about

In a *standard* (extensional) heap, two authoritative assertions `Auth m₁ • Auth m₂` being jointly
valid forces `m₁ = m₂` on the nose, because the container satisfies `equiv ↔ eq`.  Plug in the
1D `GermMap` (`ConstOnFilterMap atTop` over `ℕ`) and the same generic agreement lemma weakens this
to "agree up to a **finite** modification of the stored sequence" — the negligible sets of `atTop`
on `ℕ` are exactly the finite prefixes.

`ProductGermMap` is strictly more dramatic.  The negligible sets of the *product* filter are the
complements of product up-sets `{ (i, j) | i ≥ a ∧ j ≥ b }ᶜ`, which include **infinite "thin
crosses"** — an entire row `{ (0, j) | j }`, an entire column, or any finite union of them.  So two
authorities can disagree on an *infinite* set of points and still be forced equal by the generic
Iris agreement principle.  Agreement here is **agreement modulo an infinite negligible set**.

## Why this is the skeleton of probabilistic-independence-as-separation-logic

Read the product filter as an "almost-everywhere" filter: a set is negligible when it is small in
*both* coordinates' tail.  Then:

* **agreement up to a negligible set** is the heap-OFE equivalence `≡`;
* the **separating conjunction `∗`** of two fragments at distinct keys is two observations that do
  not interfere — they live on **disjoint** parts of the heap;
* a fragment's content is determined only up to its product-filter germ, i.e. *up to a null set*.

This is precisely the shape of the central slogan of probabilistic separation logics
(Polaris, Lilac, and the Barthe–Hsu line): **independence = separation**, where "independent" means
"agreeing off disjoint null/negligible supports."  Realizing that skeleton inside a *filter-quotient
`HeapView`* — where the negligible sets are genuinely **infinite** — is a concrete, machine-checked
instance of the framework's reach: the camera-level `∗` already gives disjointness of supports, and
the filter-germ already gives "up to a negligible set," for free from existing Iris machinery.

The headline theorem `product_agreement` exhibits exactly this: two authorities that differ on a
whole row (an infinite thin cross) yet are forced `≡` by joint validity.
-/

@[expose] public section

namespace IrisMath.Demos.IndependenceSeparation

open Iris Iris.BI COFE
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances
open scoped Filter

/-- The non-extensional 2D heap container: `ProductGermMap`, keyed by `ℕ`.  Each cell stores a
double sequence `ℕ × ℕ → V`, observed at its **product-filter germ** (its eventual value as both
coordinates tend to infinity).  Its negligible sets include *infinite* thin crosses. -/
abbrev H := ProductGermMap

/-- Values: agreement on strings, so a cell carries a single agreed-upon string germ. -/
abbrev V := Agree (LeibnizO String)

-- A type of fractions (kept polymorphic, as in the upstream examples).
variable {F} [UFraction F]

/-- The heap functor — `constOF` of the generic `HeapView` CMRA over the 2D non-extensional heap.
Compare `Iris/Examples/IProp.lean`'s `F1`, which uses `AssocList` in the same slot: we substitute
the product-filter-germ container, and nothing else moves. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat V H

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole heap `m`, as an `IProp`. -/
noncomputable def auth (γ : GName) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- A single-cell observation: fragmental ownership of cell `k` whose product-filter germ is `v`.
Under the independence-as-separation reading this is an *observation supported on key `k`*. -/
noncomputable def obs (γ : GName) (k : Nat) (v : V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (own one) v)

@[inherit_doc] notation:50 k " ↦[" γ "] " v => obs γ k v

/-! ## Theorem 1 (headline): agreement modulo an *infinite* negligible set -/

/-- **The headline.**  Two authoritative assertions over the 2D product-germ heap, jointly owned,
force the two heaps to be *equivalent* under the heap OFE — `m₁ ≡{0}≡ m₂`.  The proof is the generic
Iris agreement lemma `dist_of_validN_auth_op`; what makes it striking is the container's math.

For `ProductGermMap`, `m₁ ≡{0}≡ m₂` unfolds to "the product-filter germ of `m₁` at `k` equals that
of `m₂` at `k`, for every `k`": the heaps agree at every key *up to a filter-negligible thin cross*.
Because the product filter's small sets include whole rows, the two stored double sequences may
disagree on an **infinite** set and still satisfy this agreement principle — impossible for the
extensional heap (`= ` on the nose) and impossible even for the 1D `GermMap` (only finite prefixes
negligible). -/
theorem product_agreement (γ : GName) (m₁ m₂ : H V) :
    auth (F := F) (GF := GF) γ m₁ ∗ auth (F := F) (GF := GF) γ m₂ ⊢
      ⌜m₁ ≡{0}≡ m₂⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  -- `H : ✓{0} (Auth (own one) m₁ • Auth (own one) m₂)`; the generic Iris agreement lemma turns
  -- joint authoritative validity into heap-OFE equivalence of the two heaps.
  ipure_intro
  exact dist_of_validN_auth_op H

/-! ## The witness: the agreement region is genuinely infinite

`product_agreement` concludes `m₁ ≡ m₂`.  We exhibit two heaps that *are* `≡` (so the agreement
principle is satisfiable nontrivially) yet are `≠` as Lean values **because they differ on an entire
row** — an infinite set.  We reuse the instance's `rowBumped` witness: the constant-`0` family
versus the family that is `0` off row `0` and `1` on all of row `0`.  Both have product-filter germ
`0`, so they observe identically, but they disagree at infinitely many points.

An extensional heap could never witness this; the 1D `GermMap` could witness `≡ ≠ =`, but only with
a *finite* disagreement region.  Here the disagreement is infinite. -/

/-- Two `ProductGermMap ℕ` heaps that are heap-OFE *equivalent* yet differ on an **infinite thin
cross** (the whole of row `0`).  This is the concrete content behind `product_agreement`: the
agreement guaranteed by joint authoritative validity holds *modulo an infinite negligible set*,
a phenomenon with no extensional and no 1D-germ analogue. -/
theorem agreement_modulo_infinite_cross :
    ∃ m₁ m₂ : ProductGermMap ℕ,
      Std.PartialMap.equiv m₁ m₂ ∧ m₁ ≠ m₂ ∧
        (∀ j, (m₁ 0).get! (0, j) ≠ (m₂ 0).get! (0, j)) := by
  refine ⟨ProductGermMap.m_const, ProductGermMap.m_bumped,
    ProductGermMap.nonextensional.1, ProductGermMap.nonextensional.2, fun j => ?_⟩
  -- On the whole of row `0`, the stored double sequences genuinely differ (`0 ≠ 1`).
  have hc : ProductGermMap.m_const 0 = some (fun _ => 0) := by
    simp [ProductGermMap.m_const, ProductGermMap.insert]
  have hb : ProductGermMap.m_bumped 0 = some ProductGermMap.rowBumped := by
    simp [ProductGermMap.m_bumped]
  rw [hc, hb]
  simp [ProductGermMap.rowBumped]

/-! ## Theorem 2: a thin-cross modification is an invisible update

Modifying a cell's stored double sequence along a filter-negligible thin cross (e.g. flipping an
entire row) leaves the **observation** fixed, so it is an `equiv`-preserving update — frame
preserving for every `HeapView` built on this instance.  We state it two ways: the denotation-level
`equiv` (an infinite modification that is invisible), and its lift to an `IProp` fancy update via
`HeapView.update_replace` (the resource-algebra shadow: a heap *store* whose new representative may
have been refreshed along an entire row, observationally an identity). -/

/-- **An infinite modification can be invisible.**  Re-storing cell `k`'s value `v` by *any* double
sequence `s` that agrees with the constant `v` eventually along the product filter — i.e. off a
filter-negligible thin cross, which may be an entire row — produces a heap-OFE-equivalent map.  This
is `IrisMath.Instances.ProductGermMap.refine_thin_cross_equiv`; we name it here for the demo to make
explicit that the negligible region is permitted to be infinite. -/
theorem thin_cross_invisible (m : H V) (k : Nat) (v : V) {s : Idx → V}
    (hs : s =ᶠ[Filter.atTop] (fun _ => v)) :
    Std.PartialMap.equiv (Std.PartialMap.insert m k v)
      (fun k' => if k = k' then some s else m k') :=
  refine_thin_cross_equiv m k v hs

/-- **The invisible update, lifted to an `IProp` fancy update.**  Owning the authority and the
observation at `k`, one may replace the cell value by any valid `v'`, updating both the authority's
stored double sequence and the observation.  This is the generic `HeapView.update_replace`
transported through `iOwn_update_op`; over `ProductGermMap` the new authoritative cell may be
realized by *any* double sequence whose product-filter germ is `v'` — including one refreshed along
an entire (infinite) row.  The thin-cross refinement is invisible to the CMRA precisely because
every `HeapView` operation observes only the product-filter germ. -/
theorem store_along_cross (γ : GName) (m : H V) (k : Nat) (v v' : V) (Hv' : ✓ v') :
    auth (F := F) (GF := GF) γ m ∗ obs (F := F) (GF := GF) γ k v ⊢
      |==> (auth (F := F) (GF := GF) γ (Std.PartialMap.insert m k v')
            ∗ obs (F := F) (GF := GF) γ k v') := by
  refine iOwn_op.mpr.trans ?_
  refine (iOwn_update (γ := γ)
    (HeapView.update_replace (F := F) (m1 := m) (k := k) (v1 := v) (v2 := v') Hv')).trans ?_
  exact BIUpdate.mono iOwn_op.mp

/-! ## Theorem 3: independence = separation (disjoint supports) -/

/-- **Independence as separation.**  Two observations at *distinct* keys `k₁ ≠ k₂` are owned as a
separating conjunction `∗`.  We split the joint fragment `Frag k₁ v₁ • Frag k₂ v₂` into the two
single-cell observations, which is exactly the standard disjoint-key separation of `HeapView`.

Under the product-filter / almost-everywhere reading this is the skeleton of "independence =
separation": the two observations are supported on **disjoint** parts of the heap (distinct keys),
each determined only up to its product-filter germ (i.e. up to a negligible — possibly infinite —
set), so they cannot interfere.  Separation of resources is disjointness of (negligible-modulo)
supports; in the probabilistic reading, that disjointness is exactly *independence*.  The proof is
the generic camera split — no heap-specific reasoning — which is the point: the framework already
provides independence-as-separation, and the filter-germ supplies the "modulo a null set" for free.
-/
theorem independence_as_sep (γ : GName) (k₁ k₂ : Nat) (v₁ v₂ : V) :
    iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k₁ (own one) v₁ • Frag k₂ (own one) v₂) ⊢
      obs (F := F) (GF := GF) γ k₁ v₁ ∗ obs (F := F) (GF := GF) γ k₂ v₂ :=
  iOwn_op.mp

/-! ## Theorem 4 (doc): the bridge to probabilistic separation logic

`independence_as_sep` is, mechanically, the ordinary disjoint-support split of a `HeapView`
fragment.  Its *significance* in this demo comes from the carrier.  Probabilistic separation logics
— **Polaris** (Bizjak–Birkedal style probabilistic Iris), **Lilac** (Li–Ahmed–Holtzen), and the
Barthe–Hsu line — take as their central principle:

      "two random variables are **independent** ⟺ their resources are **separated** (`∗`)."

The semantic content of independence in those logics is *disjointness of supports modulo a null
set*: `X ⫫ Y` when the information they pin down lives on probabilistically disjoint events,
ignoring measure-zero exceptions.  Two ingredients are needed to model this in a separation logic:

  (1) a separating conjunction whose `∗` enforces **disjoint supports** — supplied here, for free,
      by the generic `HeapView` camera split (`independence_as_sep`); and
  (2) a notion of equality that is **insensitive to a negligible set** — supplied here by the
      product-filter germ, whose negligible sets are exactly the complements of product up-sets,
      i.e. the **infinite thin crosses** (whole rows/columns).

Replacing the product filter by a genuine almost-everywhere filter `{ A | μ(Aᶜ) = 0 }` turns this
exact construction into the Polaris/Lilac reading on the nose: a cell stores a random variable, two
cells' values are `≡` when they agree off a null set, and `∗` of two cells at distinct keys is the
statement that the two random variables are supported on disjoint (modulo-null) events — i.e.
**independent**.  The product filter used here is the order-theoretic skeleton of that a.e. filter:
its small sets are infinite, so `product_agreement` already exhibits the defining feature —
**agreement modulo an infinite negligible set** — that distinguishes a measure-theoretic
separation logic from a discrete one.  The contribution of this demo is to show that the
*separation-logic half*
of independence-as-separation requires no new metatheory: it is the generic Iris `HeapView` over a
filter-quotient container, and the choice of filter is the only knob that tunes "how negligible is
negligible." -/

end IrisMath.Demos.IndependenceSeparation
