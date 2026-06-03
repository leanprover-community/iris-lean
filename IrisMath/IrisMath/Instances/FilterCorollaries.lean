/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Analysis.SpecificLimits.Basic
public import Iris
public import IrisMath.Instances.ConstOnFilterMap

/-! # The reach of the keystone: many non-extensional maps as one-line corollaries

`ConstOnFilterMap.lean` proves, once and for all, that for any `NeBot` filter `l : Filter Idx`
the map `K → Option (Idx → V)` observed by "the `l`-eventually-constant value" is a
`LawfulPartialMap`, non-extensional whenever some `s =ᶠ[l] s'` with `s ≠ s'`.

This file harvests that theorem: each named instance below is *literally* `ConstOnFilterMap l` for
a different filter `l`, and its non-extensionality is `nonextensional_of_eventuallyEq` applied to a
witness adapted to `l`'s small sets.  No new law-proving happens here — that is the whole point.

| filter `l`               | small sets (ignored differences) | flavor                         |
|--------------------------|----------------------------------|--------------------------------|
| `atTop` on `ℕ`           | finite prefixes                  | germ / tail behaviour (GermMap)|
| `atBot` on `ℤ`           | "after some point going down"    | germ at −∞                     |
| `cofinite` on `ℕ`        | finite sets                      | "almost everywhere finite"     |
| `𝓝 x₀` on `ℝ`            | complements of neighborhoods     | germ at a point / stalk        |

The neighborhood-filter instance (`𝓝 x₀`) is the **local-ring / sheaf-stalk** map: it observes a
stored function only through its germ at `x₀`, the algebraic object underlying stalks of the sheaf
of functions and the local ring at a point.  That it is "just another filter" is exactly the
unifying content of the keystone.
-/

@[expose] public section

namespace IrisMath.Instances.FilterCorollaries

open Iris.Std Filter
open scoped Topology
open IrisMath.Instances

/-! ### Germ at `−∞`: `atBot` on `ℤ` -/

/-- A map observing stored `ℤ`-indexed families through their eventual value as the index → −∞. -/
abbrev AtBotMap (K V : Type _) := ConstOnFilterMap (Filter.atBot (α := ℤ)) K V

noncomputable example (K : Type _) [DecidableEq K] (V : Type _) :
    LawfulPartialMap (AtBotMap K) K := inferInstance

/-- Non-extensionality at `−∞`: a `ℤ`-family bumped at index `0` agrees with the constant family
for all sufficiently negative indices, so the two singleton maps collapse. -/
theorem atBot_nonextensional (K : Type _) [DecidableEq K] (k₀ : K) :
    PartialMap.equiv (M := AtBotMap K)
        (fun k => if k = k₀ then some (fun _ : ℤ => (0 : ℕ)) else none)
        (fun k => if k = k₀ then some (fun n : ℤ => if n = 0 then 1 else 0) else none)
      ∧ (fun k => if k = k₀ then some (fun _ : ℤ => (0 : ℕ)) else none)
          ≠ (fun k : K => if k = k₀ then some (fun n : ℤ => if n = 0 then 1 else 0) else none) := by
  refine ConstOnFilterMap.nonextensional_of_eventuallyEq (l := Filter.atBot) k₀ ?_ ?_
  · rw [EventuallyEq, eventually_atBot]
    exact ⟨-1, fun b hb => by simp [show b ≠ 0 by omega]⟩
  · intro h; have := congrFun h 0; simp at this

/-! ### Cofinite on `ℕ`: differences on any finite set ignored -/

/-- A map observing stored families through their value off a finite set (`cofinite` germ). -/
abbrev CofiniteMap (K V : Type _) := ConstOnFilterMap (Filter.cofinite (α := ℕ)) K V

noncomputable example (K : Type _) [DecidableEq K] (V : Type _) :
    LawfulPartialMap (CofiniteMap K) K := inferInstance

/-- Non-extensionality for `cofinite`: a family bumped at a single index agrees with the constant
family off the finite set `{0}`, so they share the cofinite-eventual value. -/
theorem cofinite_nonextensional (K : Type _) [DecidableEq K] (k₀ : K) :
    PartialMap.equiv (M := CofiniteMap K)
        (fun k => if k = k₀ then some (fun _ : ℕ => (0 : ℕ)) else none)
        (fun k => if k = k₀ then some (fun n : ℕ => if n = 0 then 1 else 0) else none)
      ∧ (fun k => if k = k₀ then some (fun _ : ℕ => (0 : ℕ)) else none)
          ≠ (fun k : K => if k = k₀ then some (fun n : ℕ => if n = 0 then 1 else 0) else none) := by
  refine ConstOnFilterMap.nonextensional_of_eventuallyEq (l := Filter.cofinite) k₀ ?_ ?_
  · rw [EventuallyEq, eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton 0) ?_
    intro n hn; by_contra hn0
    exact hn (by simp [show n ≠ 0 from hn0])
  · intro h; have := congrFun h 0; simp at this

/-! ### Germ at a point: `𝓝 x₀` on `ℝ` — the sheaf-stalk / local-ring map -/

/-- The **germ-at-a-point** map: stored functions `ℝ → V` are observed only through their germ at
`x₀` (the neighborhood filter `𝓝 x₀`).  This is the value algebra underlying the stalk of the
sheaf of functions at `x₀` / the local ring at a point. -/
abbrev GermAtMap (x₀ : ℝ) (K V : Type _) := ConstOnFilterMap (𝓝 x₀) K V

noncomputable example (x₀ : ℝ) (K : Type _) [DecidableEq K] (V : Type _) :
    LawfulPartialMap (GermAtMap x₀ K) K := inferInstance

/-- The germ-at-a-point map is non-extensional: a function agreeing with a constant on a
neighborhood of `x₀` but differing far away has the same germ at `x₀`.  Witness at `x₀ = 0`:
`const 0` versus `g` which is `0` on `{|x| < 1}` (a neighborhood of `0`) and `1` outside —
same germ at `0`, different functions. -/
theorem germAt_nonextensional (K : Type _) [DecidableEq K] (k₀ : K) :
    PartialMap.equiv (M := GermAtMap 0 K)
        (fun k => if k = k₀ then some (fun _ : ℝ => (0 : ℕ)) else none)
        (fun k => if k = k₀ then some (fun x : ℝ => if x ∈ Set.Ioo (-1 : ℝ) 1 then 0 else 1)
          else none)
      ∧ (fun k => if k = k₀ then some (fun _ : ℝ => (0 : ℕ)) else none)
          ≠ (fun k : K => if k = k₀ then
              some (fun x : ℝ => if x ∈ Set.Ioo (-1 : ℝ) 1 then 0 else 1) else none) := by
  refine ConstOnFilterMap.nonextensional_of_eventuallyEq (l := 𝓝 (0 : ℝ)) k₀ ?_ ?_
  · -- the two functions agree on the open interval `(-1, 1)`, a neighborhood of `0`
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
      isOpen_Ioo.mem_nhds (by norm_num)
    filter_upwards [hmem] with x hx
    simp [hx]
  · intro h
    -- they differ at `x = 2 ∉ (-1, 1)`
    have := congrFun h 2
    norm_num [Set.mem_Ioo] at this

end IrisMath.Instances.FilterCorollaries
