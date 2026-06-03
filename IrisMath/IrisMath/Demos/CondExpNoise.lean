/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Iris
public import IrisMath.Instances.CondExpMap

/-! # Demo — a frame-preserving update that *rewrites the random variable*

The measure-theoretic non-extensional heaps (`AeRandomVar`, `CondExpMap`, `DensityMap`) store a
**random variable** in each cell and observe it only through a measure-theoretic *projection*.  The
invisible updates of `AeRandomVar` (modify on a `μ`-null set) and `DensityMap` (a.e.-equal density)
change the representative only on a *null* set.  When the projection is a **conditional
expectation** there is, *in general*, a strictly stronger phenomenon:

> over a general probability space you may add to a random variable **any conditionally-centered
> noise** `N` (`μ[N | 𝒢] = 0`) — nonzero on a set of **positive measure** — and the conditional
> expectation `μ[· | 𝒢]` is **unchanged**.

This is the kernel of the orthogonal projection onto the `𝒢`-measurable functions (the signal/noise
decomposition of `L²(μ)`): `L¹(μ) / ker(μ[· | 𝒢])` is exactly what a non-extensional condExp heap
would quotient by.

**What this file actually delivers, honestly split:**

* `condExp_invariant_under_centered_noise` — the general theorem above, over any `μ` and `𝒢`. It is
  a short consequence of Mathlib's `condExp_add` (`P` linear, `P N = 0 ⟹ P (X+N) = P X`); the value
  is *naming the phenomenon as a frame-preserving resource move*, not the analysis.
* `centered_iff_mean_zero` — for `𝒢 = ⊥`, "conditionally centered" is "mean zero" (`∫ N ∂μ = 0`),
  an abundant **positive-measure** family. This shows the general theorem is non-degenerate.
* `perturb_rv` — the Iris `|==>` lift, over the in-repo `CondExpMap` `HeapView`. **Caveat (do not
  skip):** `CondExpMap` is instantiated at `μ = dirac true`, so the rewritten r.v. is constrained
  only at the mass point `true` and is free at the **`μ`-null** point `false`. Hence the *lifted*
  update is a null-point rewrite — *identical in strength to `AeRandomVar`'s* — NOT the
  positive-measure rewrite above. The positive-measure phenomenon (general theorem) is **not yet a
  resource update**: that needs a non-degenerate condExp `HeapView` (`get? = μ[·|𝒢]` for ℝ-valued
  r.v.s over a non-dirac `μ`), which the polymorphic-`get?`-vs-`ℝ` tension blocks and which
  is the genuine next construction. So: the *general theorem* is positive-measure but not lifted;
  the *lift* is real Iris `|==>` but degenerate. The two are not yet combined. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory

namespace IrisMath.Demos.CondExpNoise

section General

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : MeasurableSpace α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Headline — the conditional expectation is invariant under conditionally-centered noise.**

Over any measure `μ` and sub-σ-algebra `m`, if `N` is integrable with conditional expectation `0`
(`μ[N | m] = 0` a.e. — a *conditionally-centered* perturbation), then adding `N` to any integrable
`X` does not change the conditional expectation:

> `μ[X + N | m] = μ[X | m]`  (a.e.)

The crucial point is what `N` may be: `μ[N | m] = 0` does **not** force `N = 0` — `N` can be nonzero
on a set of positive measure (see `centered_iff_mean_zero`). So this is a frame-preserving update
that genuinely **rewrites the stored random variable across a positive-measure set**, while the
observed conditional expectation — the resource — is fixed. It is `condExp_add` plus
`μ[N|m] = 0`. -/
theorem condExp_invariant_under_centered_noise {X N : α → E}
    (hX : Integrable X μ) (hN : Integrable N μ) (hc : μ[N | m] =ᵐ[μ] 0) :
    μ[X + N | m] =ᵐ[μ] μ[X | m] := by
  filter_upwards [condExp_add hX hN m, hc] with a h1 h2
  simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 ⊢
  rw [h1, h2, add_zero]

/-- **"Conditionally centered" at `𝒢 = ⊥` is exactly "mean zero".**  For the trivial sub-σ-algebra
(conditional expectation = the mean) over a probability measure, `μ[N | ⊥] = 0` a.e. iff
`∫ N ∂μ = 0`.  Mean-zero noise is an abundant, positive-measure family (e.g. `+c` on half the space,
`-c` on the other half), so the update of `condExp_invariant_under_centered_noise` is genuinely
non-degenerate — it is *not* the null-set / a.e. update of `AeRandomVar`. -/
theorem centered_iff_mean_zero [IsProbabilityMeasure μ] {N : α → E} :
    μ[N | ⊥] =ᵐ[μ] 0 ↔ ∫ x, N x ∂μ = 0 := by
  rw [condExp_bot]
  constructor
  · intro h
    have ⟨a, ha⟩ := h.exists
    simpa using ha
  · intro h
    filter_upwards with a
    simp [h]

end General

/-! ## The same move as an Iris `|==>` update over the `CondExpMap` heap

We connect the phenomenon to the resource layer. `CondExpMap` (`IrisMath.Instances.CondExpMap`) is a
`LawfulPartialMap` whose cells store a random variable `Bool → V` observed through its conditional
expectation; it slots into the generic `HeapView`. The store OFE compares cells **only** through
`get? = condExp`, so two cells storing random variables with the same conditional expectation are
the *same heap resource* — and rewriting a cell's stored r.v. by such a one is an
`equiv`-preserving, hence frame-preserving, update, which we lift to an `IProp` `|==>`.

Honest caveat: the in-repo `CondExpMap` is instantiated at `μ = dirac true`, `𝒢 = ⊥`, where
conditional expectation is "the value at `true`", so the rewritten r.v. differs only on the
`μ`-null point `false`. The *general, positive-measure* phenomenon is `General` above; a
non-degenerate `condExp` `HeapView` instance is the natural next construction. The lift below shows
the end-to-end mechanism: representative rewrite ⟶ heap `equiv` ⟶ frame-preserving `|==>`. -/

section Resource

open Iris Iris.BI COFE Iris.Std
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances IrisMath.Instances.CondExpMap

/-- Cell values: agreement on reals. -/
abbrev V := Agree (LeibnizO ℝ)

variable {F} [UFraction F]

/-- The heap functor over the conditional-expectation container. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Bool V CondExpMap

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole heap of conditional-expectation cells. -/
def auth (γ : GName) (m : CondExpMap V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- **`perturb_rv` — rewrite the stored random variable, frame-preservingly (degenerate instance).**

Owning the authority for a cell at key `k` storing the constant random variable `v`, you may update
to the authority storing any `g` with the same conditional expectation (`g =ᵐ[μ] fun _ ↦ v`); the
update is an `IProp` `|==>` because the two heaps are the *same resource* (the store OFE sees only
`condExp`), via `refine_meanZero_equiv` lifted through heap-`equiv` and `iOwn` non-expansiveness, no
spatial hypothesis consumed.

**Degeneracy caveat:** here `μ = CondExpMap.μ = dirac true`, so `g =ᵐ[μ] fun _ ↦ v` means exactly
`g true = v` — `g` is free only at the **`μ`-null** point `false`. So this lifted rewrite changes
the representative on a *null* set, identical in strength to `AeRandomVar`'s null-set update. The
*positive-measure* rewrite is `condExp_invariant_under_centered_noise` (general theorem), which is
**not** lifted here; combining the two needs a non-degenerate condExp `HeapView` instance (the
genuine next construction). -/
theorem perturb_rv (γ : GName) (m : CondExpMap V) (k : Bool) (v : V) {g : Bool → V}
    (hg : g =ᵐ[CondExpMap.μ] (fun _ => v)) :
    auth (F := F) (GF := GF) γ (PartialMap.insert m k v) ⊢
      iprop(|==> auth (F := F) (GF := GF) γ (fun k' => if k = k' then some g else m k')) := by
  have heqv :
      (PartialMap.insert m k v : CondExpMap V) ≡ (fun k' => if k = k' then some g else m k') :=
    PartialMap.eqv_of_Equiv (refine_meanZero_equiv m k v hg)
  have hown :
      iprop(auth (F := F) (GF := GF) γ (PartialMap.insert m k v)) ⊣⊢
        iprop(auth (F := F) (GF := GF) γ (fun k' => if k = k' then some g else m k')) :=
    equiv_iff.mp (OFE.NonExpansive.eqv
      (f := iOwn (GF := GF) (F := HeapF (F := F)) γ)
      (OFE.NonExpansive.eqv (f := Auth (H := CondExpMap) (own one)) heqv))
  exact hown.1.trans BIUpdate.intro

end Resource

end IrisMath.Demos.CondExpNoise
