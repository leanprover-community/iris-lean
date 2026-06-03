/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Iris
public import IrisMath.Instances.ConstOnFilterMap
public import IrisMath.Instances.ConvolutionMap

/-! # `GermConvMap`: non-extensionality (germ) and live updates (convolution) in ONE store

This file refutes the slogan **"a non-extensional store cannot have live, observation-changing,
camera-tracked updates."**  It does so by exhibiting a *single* `HeapView` store that is
simultaneously:

* **genuinely non-extensional** — distinct stored data collapse to the same observation; and
* the carrier of an **interesting live update** — a convolution that genuinely *moves* the
  observation, fused in a camera-tracked, frame-sensitive way.

The trick is that the two phenomena live on **orthogonal dimensions** of the cell contents:

| dimension                    | structure                                  | phenomenon          |
| ---------------------------- | ------------------------------------------ | ------------------- |
| *sequence* (the container)   | `ConstOnFilterMap atTop` — the **germ**    | non-extensionality  |
| *value* (the cell payload)   | `ConvVec G` — **convolution** distribution | live camera update  |

A cell stores a **sequence of distributions** `s : ℕ → ConvVec G`.  The observation `get?` reads
its `atTop`-limit distribution (the **germ**); two sequences with the same limit are the *same
resource* even though they are distinct Lean data — this is the non-extensionality (the *sequence*
dimension collapses).  Independently, the value at the limit lives in the convolution CMRA `ConvVec
G`, where convolving by a point-mass `ℓ` *changes the limit germ* (`v ⤳ v ⋆ ℓ`) and where two
fragments fuse by convolution `Frag k a • Frag k b ≡ Frag k (a ⋆ b)` (`frag_conv_op_equiv`) — this
is the live, observation-changing, camera-tracked update (the *value* dimension).

Because germ-collapse acts on the sequence index and convolution acts on the value, **they do not
interfere**: the same store is non-extensional AND admits the live update.  This is the precise
sense
in which non-extensionality and live camera-tracked updates *coexist*.

This file combines `GermMap`/`ConstOnFilterMap` (non-extensionality, the germ container) with
`ConvolutionMap` (`ConvVec`, the live camera-tracked convolution merge) on these two orthogonal
dimensions.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris Iris.Std Iris.Std.PartialMap Filter ConvVec
open scoped NNReal

/-! ## (1) The two dimensions compose: germ container over a convolution value CMRA

The germ container `ConstOnFilterMap atTop K` is *polymorphic in the value type* `V` — its
`LawfulPartialMap` instance is proved once for any `V`
(`ConstOnFilterMap.instLawfulPartialMap`).  In
particular it applies at `V := ConvVec G`, the convolution value CMRA.  Lifting the result through
`HeapView` gives a single CMRA carrying both structures. -/

section Compose

variable {G : Type _} [CommMonoid G]
variable {F : Type _} [UFraction F]

/-- The germ container holding **sequences of convolution distributions**:
`K → Option (ℕ → ConvVec G)`.  At each key, the stored data is a *sequence* `ℕ → ConvVec G`; the
observation `get?` reads its `atTop`-limit distribution. -/
abbrev GermConvStore (K G : Type _) [CommMonoid G] : Type _ :=
  ConstOnFilterMap (atTop (α := ℕ)) K (ConvVec G)

/-- (1) **The germ container and the convolution value CMRA compose.**  The polymorphic
`LawfulPartialMap (ConstOnFilterMap atTop K) K` instance applies at the convolution value type
`ConvVec G`, so the `HeapView` resource algebra is well-formed. -/
noncomputable example {K : Type _} [DecidableEq K] :
    LawfulPartialMap (ConstOnFilterMap (atTop (α := ℕ)) K) K := inferInstance

/-- The full resource algebra: a `HeapView` over **convolution-valued cells**, with the
**germ container** as the underlying `LawfulPartialMap`.  Both dimensions live here at once. -/
abbrev GermConvView (F K G : Type _) [UFraction F] [CommMonoid G] [DecidableEq K] : Type _ :=
  HeapView F K (ConvVec G) (ConstOnFilterMap (atTop (α := ℕ)) K)

/-- (1) **Typecheck: the composite is a genuine `CMRA`.**  Germ container + convolution value CMRA
compose into a `HeapView` resource algebra, so `•` and `~~>` are meaningful on it. -/
noncomputable example {K : Type _} [DecidableEq K] : CMRA (GermConvView F K G) := inferInstance

end Compose

/-! ## (2) Non-extensionality witness — the germ (sequence) dimension, sorry-free

A cell storing a *non-constant* sequence of distributions that is `atTop`-eventually the constant
`v` collapses, under `get?`, to the same germ as the cell storing the constant sequence
`fun _ => v` — yet the two are distinct Lean data.  This is the germ container's non-extensionality
(`ConstOnFilterMap.nonextensional_of_eventuallyEq`), now exhibited at the convolution value type. -/

namespace GermConvStore

variable {K : Type _} [DecidableEq K] {G : Type _} [CommMonoid G]

/-- A non-constant sequence of distributions that is eventually the constant `v`: it is `w` at index
`0` and `v` at every later index.  When `w ≠ v` this is genuinely non-constant, but its `atTop`-germ
is still `v`. -/
def bumpedSeq (v w : ConvVec G) : ℕ → ConvVec G := fun n => if n = 0 then w else v

/-- `bumpedSeq v w` agrees with the constant-`v` sequence eventually along `atTop` (they coincide
for all `n ≥ 1`), so both have germ `v`. -/
theorem bumpedSeq_eventuallyEq (v w : ConvVec G) :
    bumpedSeq v w =ᶠ[atTop (α := ℕ)] (fun _ => v) := by
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun b hb => by simp [bumpedSeq, Nat.one_le_iff_ne_zero.mp hb]⟩

/-- (2) **Non-extensionality witness (sorry-free) — the germ dimension.**  For any key `k₀` and any
two *distinct* distributions `v ≠ w`, the two singleton stores

* one holding the *non-constant* sequence `bumpedSeq v w` (= `w` at index 0, `v` later), and
* one holding the *constant* sequence `fun _ => v`,

are `PartialMap.equiv` (same `atTop`-limit germ `v` — the sequence dimension collapses) yet are
**distinct Lean data** (they differ at index `0`, since `w ≠ v`).  This is impossible for any
`ExtensionalPartialMap`: the convolution-valued germ store is genuinely non-extensional. -/
theorem nonextensional (k₀ : K) {v w : ConvVec G} (hvw : v ≠ w) :
    PartialMap.equiv (M := ConstOnFilterMap (atTop (α := ℕ)) K)
        (fun k => if k = k₀ then some (bumpedSeq v w) else none)
        (fun k => if k = k₀ then some (fun _ => v) else none)
      ∧ (fun k => if k = k₀ then some (bumpedSeq v w) else none)
          ≠ (fun k : K => if k = k₀ then some (fun _ => v) else none) := by
  refine ConstOnFilterMap.nonextensional_of_eventuallyEq (l := atTop (α := ℕ)) k₀
    (bumpedSeq_eventuallyEq v w) ?_
  intro h
  have h0 := congrFun h 0
  simp only [bumpedSeq] at h0
  exact hvw h0.symm

end GermConvStore

/-! ## (3) Live, observation-CHANGING, camera-tracked update — the value (convolution) dimension

On the value dimension, convolving a cell's (limit) value `v` by a point-mass `ℓ` moves the germ
readout from `some v` to `some (v ⋆ ℓ)`, and that really is a *change* (`v ⋆ ℓ ≠ v` for a suitable
point mass).  And, as a camera operation, two fragments at a key fuse by convolution.  Both facts
are inherited from `ConvolutionMap` and re-exhibited at the **germ container**
`H := ConstOnFilterMap atTop K`. -/

namespace GermConvStore

open Iris HeapView CMRA DFrac One ConvVec ConstOnFilterMap

variable {K : Type _} [DecidableEq K] {G : Type _} [CommMonoid G]

/-- A one-cell germ-convolution store holding the constant sequence `fun _ => v` at key `k`. -/
noncomputable def cell (k : K) (v : ConvVec G) : GermConvStore K G :=
  fun k' => if k = k' then some (fun _ => v) else none

/-- The germ readout of `cell k v` at `k` is exactly `some v` (limit of the constant sequence). -/
theorem cell_get (k : K) (v : ConvVec G) :
    PartialMap.get? (M := ConstOnFilterMap (atTop (α := ℕ)) K) (cell k v) k = some v := by
  change ConstOnFilterMap.get? _ (cell k v) k = some v
  rw [ConstOnFilterMap.get?, cell, if_pos rfl, Option.bind_some]
  exact eventualValue_const v

/-- (3a) **The observation MOVES.**  Convolving the cell's value by `ℓ` (i.e. storing the constant
sequence `v ⋆ ℓ`) changes the germ readout from `some v` to `some (v ⋆ ℓ)`.  The limit distribution
has genuinely advanced by one independent convolution step. -/
theorem cell_conv_get (k : K) (v ℓ : ConvVec G) :
    PartialMap.get? (M := ConstOnFilterMap (atTop (α := ℕ)) K) (cell k (v + ℓ)) k
      = some (v + ℓ) :=
  cell_get k (v + ℓ)

/-- (3b) **The observation change is nontrivial.**  For a self-non-idempotent point mass
`ℓ = single x 1` (i.e. `x * x ≠ x`), convolving the cell value `single x 1` by `ℓ` moves the germ:
the readout becomes `some (single (x*x) 1)`, which is *not* `some (single x 1)` — observation
genuinely changed.  This is the value-dimension analogue of the live update. -/
theorem cell_conv_get_changes (k : K) (x : G) (hx : x * x ≠ x) :
    PartialMap.get? (M := ConstOnFilterMap (atTop (α := ℕ)) K)
        (cell k (single x 1 + single x 1)) k
      ≠ PartialMap.get? (M := ConstOnFilterMap (atTop (α := ℕ)) K) (cell k (single x 1)) k := by
  rw [cell_get, cell_get]
  intro h
  exact conv_moves_support x hx (Option.some.inj h)

section Fusion

variable {F : Type _} [UFraction F]
variable {k : K} {q1 q2 : F} {a b : ConvVec G}

/-- (3c) **Camera-tracked structural fusion at the germ container (sorry-free) — the value
dimension.**  Two convolution fragments at a key `k` compose, via the *camera operation* `•`, into a
single fragment carrying the **convolution** `a ⋆ b` of the two distributions:
```
Frag k a  •  Frag k b   ≡   Frag k (a ⋆ b)
```
This is `HeapView.frag_add_op_equiv` instantiated at the convolution value CMRA, **over the germ
container** `H := ConstOnFilterMap atTop K`.  It is genuinely tracked by the camera op (the resource
`•` computes the deep convolution sum over both supports) and frame-sensitive — NOT a full-ownership
replace.  The germ container plays no role here, confirming the dimensions are orthogonal. -/
theorem frag_conv_op_equiv :
    (Frag k (.own q1) a • Frag k (.own q2) b
        : GermConvView F K G) ≡
      Frag k (.own (q1 + q2)) (a + b) :=
  (frag_add_op_equiv (q1 := q1) (q2 := q2)).symm

end Fusion

/-! ### The live camera update as a frame-preserving `~~>` over the germ container -/

section Update

variable {F : Type _} [UFraction F]

/-- (3d) **Convolution update over the germ container (sorry-free).**  Owning the authority and the
full fragment of cell `k` (holding `w`), atomically advance the cell to the convolution `w ⋆ δ` — a
live, frame-preserving `~~>` on the *value* dimension, powered by `HeapView.update_replace` (every
distribution is valid).  The germ container `H := ConstOnFilterMap atTop K` is the underlying
`LawfulPartialMap`, so this is the live update *in the non-extensional store*. -/
theorem update_convolve (m : GermConvStore K G) (k : K) (w δ : ConvVec G) :
    (Auth (.own one) m • Frag k (.own one) w : GermConvView F K G) ~~>
      Auth (.own one) (PartialMap.insert m k (w + δ)) • Frag k (.own one) (w + δ) :=
  HeapView.update_replace (valid_conv (w + δ))

end Update

end GermConvStore

/-! ## (4) THE PUNCHLINE — both, in ONE store, sorry-free

The SAME `GermConvView F K G` store satisfies the non-extensionality witness (#2, germ collapse on
the *sequence* dimension) AND admits the live, observation-changing, camera-tracked convolution
update (#3, on the *value* dimension).  Because the two act on orthogonal dimensions of the cell
contents (sequence index vs. distribution value), they coexist with no interference.  This is the
refutation of "non-extensional ⟹ inert."

We make the coexistence explicit: a single statement, over a single store type, packaging the
non-extensionality witness together with the live observation-changing update. -/

namespace GermConvStore

open Iris HeapView CMRA DFrac One ConvVec

variable {K : Type _} [DecidableEq K] {G : Type _} [CommMonoid G]
variable {F : Type _} [UFraction F]

/-- (4) **THE PUNCHLINE (sorry-free): one store, both phenomena.**

Fix a commutative monoid `G` with a self-non-idempotent point `x` (`x * x ≠ x`) — e.g. a nontrivial
element of a group.  Then the SINGLE store type `GermConvView F K G` simultaneously:

1. **is non-extensional** (germ / sequence dimension): the two singleton stores holding the
   *non-constant* sequence `bumpedSeq (single x 1) (single 1 1)` and the *constant* sequence
   `fun _ => single x 1` are `PartialMap.equiv` (same limit germ) yet distinct Lean data; and

2. **admits a live, observation-CHANGING, camera-tracked update** (convolution / value dimension):
   convolving cell `k`'s value by `ℓ` moves the germ readout `v ⤳ v ⋆ ℓ` (and `single x 1 ⋆ single
   x 1 ≠ single x 1`, so the observation genuinely changes), while two fragments fuse by convolution
   `Frag k a • Frag k b ≡ Frag k (a ⋆ b)` (camera-tracked).

The two are on orthogonal dimensions, so they hold *of the same store at once* — non-extensionality
and live camera-tracked updates **coexist**. -/
theorem nonextensional_and_live (k : K) (x : G) (hx : x * x ≠ x) :
    -- (germ dimension) genuinely non-extensional: equiv but distinct data
    (PartialMap.equiv (M := ConstOnFilterMap (atTop (α := ℕ)) K)
        (fun k' => if k' = k then some (bumpedSeq (single x 1) (single (1 : G) 1)) else none)
        (fun k' => if k' = k then some (fun _ => single x 1) else none)
      ∧ (fun k' => if k' = k then some (bumpedSeq (single x 1) (single (1 : G) 1)) else none)
          ≠ (fun k' : K => if k' = k then some (fun _ => single x 1) else none))
    -- (value dimension) live, observation-CHANGING update: the germ readout moves under convolution
    ∧ (PartialMap.get? (M := ConstOnFilterMap (atTop (α := ℕ)) K)
          (cell k (single x 1 + single x 1)) k
        ≠ PartialMap.get? (M := ConstOnFilterMap (atTop (α := ℕ)) K) (cell k (single x 1)) k)
    -- (value dimension) the update is camera-tracked: fragments fuse by convolution
    ∧ (∀ (q1 q2 : F) (a b : ConvVec G),
        (Frag k (.own q1) a • Frag k (.own q2) b : GermConvView F K G) ≡
          Frag k (.own (q1 + q2)) (a + b)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- non-extensionality: `single 1 1 = 0`, the convolution unit, is distinct from `single x 1`.
    refine nonextensional (G := G) k (v := single x 1) (w := single (1 : G) 1) ?_
    intro h
    have hMA := congrArg toMA h
    rw [toMA_single, toMA_single] at hMA
    -- `single x 1 = single 1 1` forces `x = 1`, contradicting `x * x ≠ x` (`1 * 1 = 1`).
    have hx1 : x = 1 := (Finsupp.single_left_inj (b := (1 : ℝ≥0)) (by norm_num)).mp hMA
    exact hx (by rw [hx1, mul_one])
  · exact cell_conv_get_changes k x hx
  · exact fun q1 q2 a b => frag_conv_op_equiv

end GermConvStore

end IrisMath.Instances
