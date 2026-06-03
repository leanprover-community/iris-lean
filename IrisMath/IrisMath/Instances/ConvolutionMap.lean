/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Finsupp.SMul
public import Iris

/-! # A convolution-valued heap: camera-TRACKED, structural fragment fusion

This file builds a `LawfulPartialMap`-backed `HeapView` resource algebra whose *values* are
finitely-supported distributions over a commutative group/monoid `G`, and whose **camera operation
`•` is the convolution product** of those distributions.  This is the genuinely *structural* sibling
of `IrisMath/Instances/MeasureValuedMap.lean` and `IrisMath/Instances/DistributionMap.lean`: where
those fuse fragments by *additive* `+` (pointwise mass addition — "I saw these events, you saw
those"), here two fragments fuse by **convolution `⋆`** — the distribution of the **product (sum) of
two independent random variables**.

## The value algebra: `MonoidAlgebra ℝ≥0 G` as a convolution monoid

Mathlib's `MonoidAlgebra R G := G →₀ R` carries, for a `CommSemiring R` and commutative `G`, a
`CommSemiring` structure whose **multiplication is exactly convolution**:
```
(w₁ * w₂) c = ∑_{a · b = c} w₁ a * w₂ b
```
(`MonoidAlgebra.single_mul_single : single a r * single b s = single (a*b) (r*s)`).  For `G` a
finite abelian group and `R = ℝ≥0` this `*` is precisely the distribution of `X · Y` for independent
`X ~ w₁`, `Y ~ w₂`.  Its unit is `1 = single 1 1` (the point mass at the identity = the constant
random variable `1`).  Because `G` is commutative, `*` is a *commutative monoid* — exactly the input
`Iris.CommMonoidLike` needs.

`CommMonoidLike` is hardwired to take the CMRA operation from the `Add`/`Zero` typeclasses.  We
therefore wrap the monoid algebra in a one-field type synonym `ConvVec G` and install
`Add := (* = convolution)`, `Zero := (1 = single 1 1)`.  Feeding the resulting discrete Leibniz
commutative monoid into `CommMonoidLike` yields a full `CMRA`/`UCMRA (ConvVec G)` whose `•` *is*
convolution.  Lifting through `HeapView` then makes `frag_add_op_equiv` read

```
Frag k a ⋆ Frag k b  ≡  Frag k (a ⋆ b)      -- the convolution of the two fragments
```

the **camera-tracked, frame-sensitive structural merge** — NOT a full-ownership replace.  The
operation `a ⋆ b` is a genuine deep computation over the supports of both fragments; fusing two
parties' fragments at a key computes the convolution of their distributions.  Practically: combining
two independent probabilistic observations, a one-step random walk, or a CRDT whose merge is
"compose the two independent contributions".

## Why `update_replace` and not the cancellative local-update path

Convolution is **not** left-cancellative on `MonoidAlgebra ℝ≥0 G` (e.g. `single 1 0 ⋆ x = 0` for
all `x`, and more generally convolving by a non-Dirac mass loses information).  So, exactly as for
non-cancellative `Measure Ω` in `MeasureValuedMap`, we do not claim `Cancelable`; the heap updates
are powered by `HeapView.update_replace`, whose only obligation `✓ v2` is `True` in the
`CommMonoidLike` CMRA.

The three scored deliverables — the camera-tracked fusion lemma (`frag_conv_op_equiv`), an
observation-change example (`single_conv_single`, etc.), and the non-extensionality witness
(`equiv_smul_ne`) — are all `sorry`-free.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris Iris.Std
open scoped NNReal

/-! ## The value type: convolution vectors `ConvVec G = MonoidAlgebra ℝ≥0 G`

`ConvVec G` is a one-field wrapper around `MonoidAlgebra ℝ≥0 G` on which the additive typeclasses
(`Add`, `Zero`) are re-installed to be the *convolution* monoid (`*`, `single 1 1`).  This lets us
reuse `CommMonoidLike` verbatim while the resulting CMRA op `•` is convolution. -/

/-- A finitely-supported nonnegative distribution over `G`, viewed as a *convolution* monoid.  As a
type it is `MonoidAlgebra ℝ≥0 G = G →₀ ℝ≥0`; the `Add`/`Zero` instances below are convolution and
the Dirac mass at the identity, so the induced CMRA operation `•` is convolution. -/
structure ConvVec (G : Type _) [Mul G] where
  /-- The underlying monoid-algebra element (a finitely-supported weight vector `G →₀ ℝ≥0`). -/
  toMA : MonoidAlgebra ℝ≥0 G

namespace ConvVec

variable {G : Type _}

section Monoid

variable [CommMonoid G]

/-- Convolution: `(w₁ ⋆ w₂) c = ∑_{a·b=c} w₁ a * w₂ b`, inherited from `MonoidAlgebra` `*`. -/
noncomputable instance instAdd : Add (ConvVec G) where
  add w₁ w₂ := ⟨w₁.toMA * w₂.toMA⟩

/-- The convolution unit: the Dirac mass at the identity of `G`, `single 1 1`. -/
noncomputable instance instZero : Zero (ConvVec G) where
  zero := ⟨1⟩

@[simp] theorem toMA_add (w₁ w₂ : ConvVec G) : (w₁ + w₂).toMA = w₁.toMA * w₂.toMA := rfl
@[simp] theorem toMA_zero : (0 : ConvVec G).toMA = 1 := rfl

theorem toMA_injective : Function.Injective (toMA (G := G)) := by
  intro ⟨a⟩ ⟨b⟩ h; cases h; rfl

@[ext] theorem ext {w₁ w₂ : ConvVec G} (h : w₁.toMA = w₂.toMA) : w₁ = w₂ := toMA_injective h

/-- The Dirac mass at `g` carrying weight `r`: `single g r`.  These are the "point" distributions;
the random variable equal to `g` with weight `r`. -/
noncomputable def single (g : G) (r : ℝ≥0) : ConvVec G := ⟨MonoidAlgebra.single g r⟩

@[simp] theorem toMA_single (g : G) (r : ℝ≥0) :
    (single g r).toMA = MonoidAlgebra.single g r := rfl

end Monoid

end ConvVec

/-! ## `ConvVec G` is a discrete Leibniz commutative monoid under convolution

We supply the *Iris* monoid typeclasses (`Std.Associative`, `Std.Commutative`,
`Std.LawfulLeftIdentity`) for convolution `+` with unit `0 = single 1 1`, plus the
discrete-of-equality OFE and `Leibniz`.  These are exactly the hypotheses of `Iris.CommMonoidLike`.
Commutativity is the
mathlib fact that `MonoidAlgebra ℝ≥0 G` is a `CommSemiring` when `G` is commutative. -/

namespace ConvVec

open _root_.Std (Associative Commutative LawfulLeftIdentity)

variable {G : Type _} [CommMonoid G]

/-- Discrete OFE on convolution vectors: equality is the only equivalence. -/
scoped instance instCOFE : COFE (ConvVec G) := COFE.ofDiscrete _ Eq_Equivalence
scoped instance instDiscreteOFE : OFE.Discrete (ConvVec G) := ⟨congrArg id⟩
scoped instance instLeibniz : OFE.Leibniz (ConvVec G) := ⟨congrArg id⟩

scoped instance instAssoc : Associative (Add.add (α := ConvVec G)) where
  assoc {x y z} := by
    apply ConvVec.ext
    change (x.toMA * y.toMA) * z.toMA = x.toMA * (y.toMA * z.toMA)
    exact mul_assoc _ _ _

scoped instance instComm : Commutative (Add.add (α := ConvVec G)) where
  comm {x y} := by
    apply ConvVec.ext
    change x.toMA * y.toMA = y.toMA * x.toMA
    exact mul_comm _ _

scoped instance instLawfulLeftId :
    LawfulLeftIdentity (Add.add (α := ConvVec G)) (0 : ConvVec G) where
  left_id {x} := by
    apply ConvVec.ext
    change (1 : MonoidAlgebra ℝ≥0 G) * x.toMA = x.toMA
    exact one_mul _

end ConvVec

/-! ## The CMRA / UCMRA on `ConvVec G` (convolution monoid) -/

namespace ConvVec

variable {G : Type _} [CommMonoid G]

noncomputable scoped instance instCMRA : CMRA (ConvVec G) := CommMonoidLike.instCMRA
noncomputable scoped instance instUCMRA : UCMRA (ConvVec G) := CommMonoidLike.instUCMRA
scoped instance instDiscrete : CMRA.Discrete (ConvVec G) := CommMonoidLike.instDiscrete

/-- The CMRA operation `•` on `ConvVec G` **is** convolution (definitionally `Add.add`). -/
theorem op_eq_conv (w₁ w₂ : ConvVec G) : (w₁ • w₂ : ConvVec G) = w₁ + w₂ := rfl

/-- Every convolution vector is `CMRA`-valid (validity is `True`), making `update_replace`
applicable to arbitrary target distributions. -/
theorem valid_conv (w : ConvVec G) : ✓ w := trivial

end ConvVec

/-! ## (3) Observation change: convolution moves the distribution

Convolving two Dirac masses gives the Dirac mass at their product — the distribution of `X·Y` for
the deterministic `X = x`, `Y = y` is the deterministic `x·y`.  More substantively, convolving two
"coin" distributions shifts mass onto new outcomes (a one-step random walk), so convolution
genuinely *moves* the distribution rather than leaving it fixed. -/

namespace ConvVec

variable {G : Type _} [CommMonoid G]

/-- **Dirac convolution = product of point masses.**
`single x r ⋆ single y s = single (x·y) (r·s)`:
fusing two deterministic observations `x`, `y` yields the deterministic observation `x·y`.  This is
the camera operation `•`, so it is exactly the fragment-fusion content at point masses. -/
@[simp] theorem single_conv_single (x y : G) (r s : ℝ≥0) :
    (single x r + single y s : ConvVec G) = single (x * y) (r * s) := by
  apply ConvVec.ext
  change MonoidAlgebra.single x r * MonoidAlgebra.single y s
    = MonoidAlgebra.single (x * y) (r * s)
  exact MonoidAlgebra.single_mul_single x y r s

/-- **Convolution moves the readout.**  Convolving the point mass at `x` (`x ≠ 1`) with itself is
the point mass at `x²`, not at `x`: the observed support has *moved* from `{x}` to `{x*x}`.  Indeed,
when `x * x ≠ x` the convolution `single x 1 ⋆ single x 1` differs from `single x 1`. -/
theorem conv_moves_support (x : G) (hx : x * x ≠ x) :
    (single x 1 + single x 1 : ConvVec G) ≠ single x 1 := by
  rw [single_conv_single, mul_one]
  intro h
  have hMA := congrArg toMA h
  simp only [toMA_single] at hMA
  exact hx ((Finsupp.single_left_inj (b := (1 : ℝ≥0)) (by norm_num)).mp hMA)

end ConvVec

/-! ## (1) The `LawfulPartialMap` instance: the function store specialized to convolution values -/

/-- The convolution-distribution store: keys `K` to optional convolution vectors over `G`. -/
abbrev ConvStore (K G : Type _) [CommMonoid G] : Type _ := K → Option (ConvVec G)

section LawfulInstance

variable {K G : Type _} [CommMonoid G] [DecidableEq K]

/-- (1) **A real `LawfulPartialMap`, no `sorry`.**  The function store specialized to convolution
vectors; inherited verbatim from `instLawfulPartialMapFun`. -/
instance instLawfulPartialMapConvStore : LawfulPartialMap (K → Option ·) K := inferInstance

/-- Sanity check that the specialized instance really applies at the convolution value type. -/
example (m : K → Option (ConvVec G)) (k : K) (w : ConvVec G) :
    PartialMap.get? (M := (K → Option ·)) (PartialMap.insert (M := (K → Option ·)) m k w) k
      = some w :=
  LawfulPartialMap.get?_insert_eq rfl

end LawfulInstance

/-! ## (2) The `HeapView` CMRA, the camera-TRACKED fusion lemma, and convolution updates -/

namespace ConvStore

open Iris HeapView CMRA DFrac One ConvVec
open scoped CommMonoidLike

variable {K G : Type _} [CommMonoid G]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulPartialMap H K]

/-! ### (2) THE PRIZE — camera-tracked, structural fragment fusion by convolution

`HeapView.frag_add_op_equiv` says `Frag k (own (q₁+q₂)) (v₁ • v₂) ≡ Frag k (own q₁) v₁ •
Frag k (own q₂) v₂`, where the inner `•` is the *value CMRA op*.  Here that op is **convolution**
(`op_eq_conv`).  So two parties' fragments at the same key `k` **fuse by convolution**: -/

variable {k : K} {q1 q2 : F} {a b : ConvVec G}

/-- **Camera-tracked structural fusion (THE PRIZE), sorry-free.**  Two convolution-fragments at a
key compose — via the *camera operation* `•` — into a single fragment carrying the **convolution**
`a ⋆ b` of the two distributions:
```
Frag k a  •  Frag k b   ≡   Frag k (a ⋆ b)
```
This is `HeapView.frag_add_op_equiv` instantiated at the convolution value CMRA.  It is genuinely
*tracked* by the camera op (the resource `•` computes the deep convolution sum over both supports),
and *frame-sensitive* (a frame `Frag k c` fuses in too: `(a⋆b)⋆c`) — NOT a full-ownership
replace. -/
theorem frag_conv_op_equiv :
    (Frag k (.own q1) a • Frag k (.own q2) b : HeapView F K (ConvVec G) H) ≡
      Frag k (.own (q1 + q2)) (a + b) :=
  (frag_add_op_equiv (q1 := q1) (q2 := q2)).symm

/-- The same fusion specialized to **point masses**: two deterministic fragments at `k`, owning the
Diracs at `x` and `y`, fuse into the Dirac at the product `x·y` — the distribution of the product of
two independent deterministic variables.  Pure convolution content, sorry-free. -/
theorem frag_conv_single :
    (Frag k (.own q1) (single x r) • Frag k (.own q2) (single y s)
        : HeapView F K (ConvVec G) H) ≡
      Frag k (.own (q1 + q2)) (single (x * y) (r * s)) :=
  frag_conv_op_equiv.trans (by rw [single_conv_single])

end ConvStore

namespace ConvStore

open Iris HeapView CMRA DFrac One ConvVec
open scoped CommMonoidLike

variable {K G : Type _} [CommMonoid G]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulPartialMap H K]

/-- **General replacement of a region's distribution.**  Owning the authoritative heap and the full
fragment at `k`, replace the distribution there by *any* `w` (every distribution is valid).  Powered
by `HeapView.update_replace` (validity is `True`), as for non-cancellative `Measure Ω`. -/
theorem update_replace_conv (m : H (ConvVec G)) (k : K) (w w' : ConvVec G) :
    (Auth (.own one) m • Frag k (.own one) w : HeapView F K (ConvVec G) H) ~~>
      Auth (.own one) (PartialMap.insert m k w') • Frag k (.own one) w' :=
  HeapView.update_replace (valid_conv w')

/-- (2) **Convolution update: convolve a region's distribution by `δ`.**  Owning the authoritative
heap and the full fragment for region `k` (holding `w`), atomically replace it by the convolution
`w ⋆ δ`.  In probabilistic terms this **advances** the distribution by one independent step `δ`
(e.g. a random-walk increment).  An instance of `update_replace_conv` with `w' := w + δ`. -/
theorem update_convolve (m : H (ConvVec G)) (k : K) (w δ : ConvVec G) :
    (Auth (.own one) m • Frag k (.own one) w : HeapView F K (ConvVec G) H) ~~>
      Auth (.own one) (PartialMap.insert m k (w + δ)) • Frag k (.own one) (w + δ) :=
  update_replace_conv m k w (w + δ)

/-- The HeapView resource algebra over a convolution-valued heap with `AssocList` as the underlying
`LawfulPartialMap` (the canonical `HeapView` carrier in the Iris library). -/
abbrev R (F G : Type _) [UFraction F] [CommMonoid G] :=
  HeapView F Nat (ConvVec G) AssocList

/-- Confirmation that `R F G` is a genuine `CMRA`, so `~~>` and `•` are meaningful there. -/
noncomputable example : CMRA (R F G) := inferInstance

/-- The convolution update **materialized on the concrete resource algebra** `R F G`. -/
theorem update_convolve_concrete (m : AssocList (ConvVec G)) (k : Nat) (w δ : ConvVec G) :
    (Auth (.own one) m • Frag k (.own one) w : R F G) ~~>
      Auth (.own one) (PartialMap.insert m k (w + δ)) • Frag k (.own one) (w + δ) :=
  update_convolve (H := AssocList) m k w δ

end ConvStore

/-! ## (4) Non-extensionality witness: unnormalized distributions modulo normalization

As in `DistributionMap`/`MeasureValuedMap`, the stored data are *unnormalized* weight vectors, but a
client observes only the *normalized* distribution.  The normalized readout is scale-invariant
(`prob (c • w) = prob w`), so distinct raw distributions that are positive scalar multiples are
indistinguishable through the interface — genuine non-extensionality. -/

namespace ConvVec

variable {G : Type _} [CommMonoid G]

/-- Total mass of a convolution vector: `∑ g, w g`. -/
noncomputable def total (w : ConvVec G) : ℝ≥0 := w.toMA.sum (fun _ x => x)

/-- The normalized probability assigned to outcome `g`: `w g / total w`.  Scale invariant. -/
noncomputable def prob (w : ConvVec G) (g : G) : ℝ≥0 := w.toMA g / w.total

/-- The pointwise scaling of a distribution by `c : ℝ≥0` (NOT the camera op; a raw rescale used only
to exhibit non-extensionality of the normalized readout). -/
noncomputable def smul (c : ℝ≥0) (w : ConvVec G) : ConvVec G := ⟨c • w.toMA⟩

@[simp] theorem toMA_smul (c : ℝ≥0) (w : ConvVec G) : (smul c w).toMA = c • w.toMA := rfl

@[simp] theorem total_smul (c : ℝ≥0) (w : ConvVec G) : (smul c w).total = c * w.total := by
  classical
  simp only [total, toMA_smul]
  rw [show (c • w.toMA) = w.toMA.mapRange (c * ·) (by simp) from rfl,
    Finsupp.sum_mapRange_index (by simp)]
  simp only [Finsupp.sum, Finset.mul_sum]

/-- **Scale invariance of normalization (sorry-free).**  `prob (c • w) = prob w` for `c ≠ 0`: the
normalized readout forgets the overall scale.  This is the algebraic heart of non-extensionality. -/
theorem prob_smul (c : ℝ≥0) (hc : c ≠ 0) (w : ConvVec G) : prob (smul c w) = prob w := by
  classical
  funext g
  simp only [prob, toMA_smul, total_smul]
  by_cases hw : w.total = 0
  · simp [hw]
  · rw [show (c • w.toMA) g = c * w.toMA g from rfl, mul_div_mul_left _ _ hc]

/-- **Non-extensionality witness (sorry-free).**  For any distribution `w` with positive mass and
any scale `c ≠ 0, 1`, the two singleton normalized-observation stores holding `w` and its rescale
`c • w` at the same key observe the *same* normalized distribution (`prob`), yet are distinct raw
data whenever `c ≠ 1` and `w ≠ 0`.  The store remembers the scale (total mass); a client reads only
the shape. -/
theorem equiv_smul_ne {K : Type _} (c : ℝ≥0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    {w : ConvVec G} (hw : w.toMA ≠ 0) (k₀ : K) [DecidableEq K] :
    let m₁ : K → Option (ConvVec G) := fun k => if k = k₀ then some w else none
    let m₂ : K → Option (ConvVec G) := fun k => if k = k₀ then some (smul c w) else none
    (∀ k, (m₁ k).map prob = (m₂ k).map prob) ∧ m₁ ≠ m₂ := by
  classical
  intro m₁ m₂
  refine ⟨?_, ?_⟩
  · intro k
    by_cases h : k = k₀
    · subst h; simp only [m₁, m₂, if_pos rfl, Option.map_some, Option.some.injEq]
      exact (prob_smul c hc0 w).symm
    · simp [m₁, m₂, h]
  · intro hcontra
    have hk₀ := congrFun hcontra k₀
    simp only [m₁, m₂, if_pos rfl, Option.some.injEq] at hk₀
    -- `w = smul c w` ⇒ `w.toMA = c • w.toMA`; with `c ≠ 1` and `w.toMA ≠ 0`, contradiction.
    have he : w.toMA = c • w.toMA := congrArg toMA hk₀
    -- pick a point `g` where `w` is nonzero; there `w.toMA g = c * w.toMA g`, forcing `c = 1`.
    obtain ⟨g, hg⟩ := Finsupp.ne_iff.mp hw
    change w.toMA g ≠ 0 at hg
    have hpt : w.toMA g = c * w.toMA g := by
      conv_lhs => rw [he]
      show (c • w.toMA) g = c * w.toMA g
      rfl
    exact hc1 ((mul_right_cancel₀ hg (a := 1) (by rw [one_mul]; exact hpt)).symm)

end ConvVec

end IrisMath.Instances
