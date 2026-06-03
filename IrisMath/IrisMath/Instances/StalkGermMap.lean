/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import IrisMath.Instances.ConstOnFilterMap

/-! # `StalkGermMap`: the stalk of the sheaf of functions — germs of functions at a point

This file instantiates the filter-general non-extensional `LawfulPartialMap` construction
`ConstOnFilterMap` (see `IrisMath/Instances/ConstOnFilterMap.lean`) at the **neighbourhood
filter `𝓝 x₀`** of a point `x₀` in a topological space.  The resulting object,

  `StalkGermMap x₀ K V := ConstOnFilterMap (𝓝 x₀) K V`,

stores at each key a *representative function* `X → V` and observes it **only through its
germ at `x₀`** — the equivalence class of the function under "agree on some neighbourhood
of `x₀`".  Everything about the representative away from `x₀` is forgotten.

## Germs of functions: the textbook non-extensional object

The **stalk** of the sheaf of (`V`-valued) functions at a point `x₀` is, by definition, the
filtered colimit of `V`-valued functions over the neighbourhoods of `x₀`:

  `stalk_{x₀} = colim_{U ∋ x₀} (functions on U) = (functions defined near x₀) / (agree near x₀)`.

An element of the stalk is a **germ at `x₀`**: an equivalence class of functions identified
when they coincide on *some* neighbourhood of `x₀`.  Mathlib spells this exactly as
`Filter.Germ (𝓝 x₀) V`, the quotient of `X → V` by `Filter.EventuallyEq (𝓝 x₀)`.  This is
*the* canonical non-extensional object of mathematics: a germ retains only the local data of
a function at `x₀` and discards everything else, so two genuinely different functions that
happen to agree near `x₀` are *the same germ* even though they differ wildly elsewhere.

This local-but-not-pointwise quotient is the engine behind:
* **local rings**: the stalk `𝒪_{X,x₀}` of a sheaf of rings is a local ring; the germ of a
  function is a unit iff the function is nonzero at `x₀`;
* **jets / Taylor data**: the `∞`-jet at `x₀` factors through the germ (the germ determines,
  and is finer than, every finite jet);
* **microlocal analysis / singularity theory**: germs are the ambient objects in which one
  studies local behaviour (Morse theory, catastrophe theory) modulo what happens far away.

Because `𝓝 x₀` is `NeBot` (every neighbourhood filter on a nonempty-neighbourhood point is
proper), the existing `[l.NeBot]` instances of `ConstOnFilterMap` apply verbatim: the seven
`LawfulPartialMap` laws are **inherited for free**, and `get? m k` returns the germ value
(`eventualValue (𝓝 x₀) (m k)`) — the constant value the representative takes *near* `x₀`,
when it is locally constant there.

## Non-extensionality, concretely

Take `X = ℝ`, `x₀ = 0`, and two functions
  `f := fun _ => a`            (constant `a`)
  `g := fun x => if |x| < 1 then a else b`   (`a` near `0`, jumps to `b` outside `(-1,1)`).
With `a ≠ b` these are **distinct Lean functions** (they differ at `x = 2`), yet they
**agree on the neighbourhood `(-1,1) ∈ 𝓝 0`**, hence have the **same germ at `0`**.  Stored
at the same key, the two maps are `PartialMap.equiv` but not equal — genuine
non-extensionality, with a real distinct-representative / same-germ witness.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap Filter Topology
open ConstOnFilterMap

variable {K : Type _} [DecidableEq K] {X : Type _} [TopologicalSpace X] {V V' : Type _}

/-- The **stalk germ map** at a point `x₀ : X`: the non-extensional `PartialMap` that stores a
representative function `X → V` per key and observes only its **germ at `x₀`** (its behaviour
on neighbourhoods of `x₀`).  This is `ConstOnFilterMap` specialized to the neighbourhood
filter `𝓝 x₀`; the `LawfulPartialMap` instance is inherited because `𝓝 x₀` is `NeBot`. -/
abbrev StalkGermMap (x₀ : X) (K V : Type _) : Type _ := ConstOnFilterMap (𝓝 x₀) K V

/-- The `LawfulPartialMap` instance is found automatically for `StalkGermMap`, inherited from
`ConstOnFilterMap` over the `NeBot` filter `𝓝 x₀`. -/
noncomputable example (x₀ : X) : LawfulPartialMap (StalkGermMap x₀ K) K := inferInstance

/-- `get?` of a `StalkGermMap` reads back the **germ value at `x₀`**: the eventual value of the
stored representative along `𝓝 x₀`. -/
theorem StalkGermMap.get?_eq (x₀ : X) (m : StalkGermMap x₀ K V) (k : K) :
    PartialMap.get? m k = (m k).bind (eventualValue (𝓝 x₀)) := rfl

/-! ## The non-extensionality witness — germs of functions on `ℝ` at `x₀ = 0`

This is the crux.  We build two genuinely different real functions agreeing on the open
neighbourhood `(-1, 1)` of `0` and verify they have the same germ at `0`, yet are stored as
distinct cells. -/

namespace StalkGermMap

variable {a b : V}

/-- The constant representative `fun _ => a`. -/
def fConst (a : V) : ℝ → V := fun _ => a

/-- A representative equal to `a` on the open ball `(-1, 1)` around `0`, and `b` outside it.
For `a ≠ b` this is a *different Lean function* from `fConst a` (they differ at `x = 2`), but
it agrees with `fConst a` on the neighbourhood `(-1, 1) ∈ 𝓝 0`. -/
noncomputable def gJump (a b : V) : ℝ → V := fun x => if |x| < 1 then a else b

/-- **The germ agreement.**  `fConst a` and `gJump a b` agree eventually along `𝓝 0`: they
coincide on the open neighbourhood `{x | |x| < 1} = (-1, 1)` of `0`, hence have the same germ
at `0`.  This holds for *every* `a b` — no hypothesis on `a, b` is needed; the agreement is
purely local. -/
theorem germ_agree (a b : V) : gJump a b =ᶠ[𝓝 (0 : ℝ)] fConst a := by
  -- The set `{x | |x| < 1}` is an open neighbourhood of `0` on which the two agree.
  have hmem : {x : ℝ | |x| < 1} ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) continuous_const
    · simp
  filter_upwards [hmem] with x hx
  simp only [gJump, fConst] at hx ⊢
  rw [if_pos hx]

/-- `fConst a` and `gJump a b` are **distinct Lean functions** when `a ≠ b`: they differ at
`x = 2`, where `|2| < 1` is false, so `gJump a b 2 = b ≠ a = fConst a 2`. -/
theorem fConst_ne_gJump (h : a ≠ b) : fConst a ≠ gJump a b := by
  intro heq
  have := congrFun heq 2
  simp only [fConst, gJump] at this
  rw [if_neg (by norm_num)] at this
  exact h this

/-- First witness: key `k₀` stores the constant representative `fConst a`. -/
def m_const (k₀ : K) (a : V) : StalkGermMap (0 : ℝ) K V :=
  fun k => if k = k₀ then some (fConst a) else none

/-- Second witness: key `k₀` stores the jumping representative `gJump a b` (same germ at `0`,
different representative). -/
noncomputable def m_jump (k₀ : K) (a b : V) : StalkGermMap (0 : ℝ) K V :=
  fun k => if k = k₀ then some (gJump a b) else none

/-- **Non-extensionality of the stalk germ map.**  For `a ≠ b`, `m_const k₀ a` and
`m_jump k₀ a b` are observationally equal (`PartialMap.equiv`) — both denote "key `k₀` ↦ germ
value `a` at `0`, everything else absent" — yet they are **distinct** Lean values, because the
stored representatives (`fConst a` vs `gJump a b`) differ away from `0` (at `x = 2`).

This is the real distinct-representative / same-germ witness: the two functions are *equal on
a neighbourhood of `0`* (hence equal germs at `0`, hence `get?`-equal) but *unequal as
functions*.  Impossible for any `ExtensionalPartialMap`, so `StalkGermMap` is genuinely
non-extensional — it is precisely the sheaf stalk forgetting all non-local data. -/
theorem nonextensional (k₀ : K) (h : a ≠ b) :
    PartialMap.equiv (M := StalkGermMap (0 : ℝ) K) (m_const k₀ a) (m_jump k₀ a b)
      ∧ m_const k₀ a ≠ m_jump k₀ a b := by
  -- `m_const`/`m_jump` unfold to exactly the singleton maps of the general lemma.
  unfold m_const m_jump
  exact nonextensional_of_eventuallyEq (l := 𝓝 (0 : ℝ)) (K := K) k₀
    (germ_agree a b).symm (fConst_ne_gJump h)

/-- Consequently this instance is genuinely non-extensional: `equiv` does NOT imply `=`. -/
theorem not_extensionalPartialMap :
    ¬ ∀ {m₁ m₂ : StalkGermMap (0 : ℝ) ℕ (ULift Bool)},
        PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro hext
  have h : (ULift.up false : ULift Bool) ≠ ULift.up true := fun he => by
    simpa using congrArg ULift.down he
  have hwit := nonextensional (K := ℕ) (a := ULift.up false) (b := ULift.up true) 0 h
  exact hwit.2 (hext hwit.1)

end StalkGermMap

/-! ## A frame-preserving update: perturbing the representative *away from* `x₀`

The stalk germ structure makes a class of updates **free** (`equiv`-preserving, hence
frame-preserving for any `HeapView` built on this instance): **modifying the representative
function anywhere off some neighbourhood of `x₀` leaves the germ at `x₀` invariant.**  This is
the "local = all that matters" move — the denotation only sees the germ, so any refinement on
the complement of a neighbourhood of `x₀` is observationally invisible.

This is the stalk analogue of `ConstOnFilterMap`'s `nonextensional_of_eventuallyEq` /
`ProductGermMap.refine_thin_cross_equiv`: distinct representatives, identical germ, hence a
trivial frame-preserving update between them. -/

/-- **Germ invariance under perturbation away from `x₀`**, machine-checked.  Replacing the
constant representative stored at a key `k` by *any* function `s` that agrees with it on some
neighbourhood of `x₀` (equivalently, off the complement of a neighbourhood of `x₀`) yields an
`equiv` map.  Concretely the premise `hs : s =ᶠ[𝓝 x₀] (fun _ => v)` says `s` has germ `v` at
`x₀`; nothing is assumed about `s` away from `x₀`.  Such a rewrite is therefore frame-preserving
for every `HeapView` update built on `StalkGermMap` (it is the denotation-level content of
`HeapView.update_replace` / `update_of_local_update`). -/
theorem StalkGermMap.refine_away_equiv (x₀ : X) (m : StalkGermMap x₀ K V) (k : K) (v : V)
    {s : X → V} (hs : s =ᶠ[𝓝 x₀] (fun _ => v)) :
    PartialMap.equiv (PartialMap.insert m k v)
      (fun k' => if k = k' then some s else m k') := by
  intro k'
  show ((ConstOnFilterMap.insert (𝓝 x₀) m k v) k').bind (eventualValue (𝓝 x₀))
    = ((fun k' => if k = k' then some s else m k') k').bind (eventualValue (𝓝 x₀))
  by_cases hk : k = k'
  · simp only [ConstOnFilterMap.insert, if_pos hk, Option.bind_some]
    rw [eventualValue_const, eventualValue_of_eventuallyEq hs]
  · simp only [ConstOnFilterMap.insert, if_neg hk]

end IrisMath.Instances
