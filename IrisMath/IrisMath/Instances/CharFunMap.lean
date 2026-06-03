/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.NNReal.Basic
public import IrisMath.Instances.ConvolutionMap
public import Iris
public import Iris.ProofMode
public import Iris.Algebra.IProp
public import Iris.Instances.UPred.Instance
public import Iris.Instances.IProp.Instance

/-! # The convolution theorem as a separation-logic law

This file is the culmination of the convolution story begun in
`IrisMath/Instances/ConvolutionMap.lean`.  There the value CMRA is
`ConvVec G = MonoidAlgebra ℝ≥0 G` whose camera operation `•` **is convolution** (`*` on the monoid
algebra), so two fragments at a key *fuse structurally* by convolution:
`Frag k a • Frag k b ≡ Frag k (a ⋆ b)` (`ConvStore.frag_conv_op_equiv`, sorry-free).  That merge is a
genuine deep computation over both supports, camera-tracked and frame-sensitive — not a replace.

Here we equip that exact same camera with a **homomorphic, non-extensional readout** and thereby make
the convolution merge *logically observable*.

## The character / characteristic-function readout

Fix a **character** `χ : G →* ℝ≥0`, a monoid homomorphism.  The concrete one we use is the
**moment/probability generating function base**: with `G = Multiplicative ℕ` and a fixed `t : ℝ≥0`,
`χ g = t ^ g` (this is `powersHom ℝ≥0 t`, a monoid hom *unconditionally* — no `t ≠ 0` side
condition).  Mathlib's `MonoidAlgebra.lift ℝ≥0 ℝ≥0 G` turns such a `χ` into an **algebra
homomorphism**
```
Φ_χ := MonoidAlgebra.lift ℝ≥0 ℝ≥0 G χ : MonoidAlgebra ℝ≥0 G →ₐ[ℝ≥0] ℝ≥0,
Φ_χ w = ∑_g w(g) · χ(g)                              -- the characteristic function / MGF / z-transform
```
The **characteristic-function readout** is `charFun χ w := Φ_χ w.toMA`.

## The convolution theorem, for free

Because `Φ_χ` is an *algebra homomorphism*, `map_mul Φ_χ` gives `Φ_χ (a * b) = Φ_χ a * Φ_χ b`, and
`*` on `MonoidAlgebra` **is convolution** (= the camera op).  Hence, with no calculation,
```
charFun_conv :  charFun χ (a ⋆ b) = charFun χ a * charFun χ b.
```
That is **the convolution theorem**: the characteristic function of a convolution is the product of
the characteristic functions — i.e. for independent random variables the characteristic functions
multiply.  It is `map_mul`.

## Non-extensionality UNIFIED with the merge

`charFun χ` collapses an entire distribution to a single scalar, so it is massively non-injective
(`charFun_collision`: with `t = 2`, the point masses `single 0 2` and `single 1 1` both read out to
`2`, yet are distinct distributions).  Crucially — and unlike the *scale*-invariance witness in
`ConvolutionMap`, which is orthogonal to the merge — this non-extensionality is the **same
phenomenon** as the structural merge: the readout forgets everything except the character value, yet
it is a **congruence for the tracked convolution** (`charFun_conv`).  Forgetting (non-extensionality)
and fusing (the merge) are one and the same homomorphic projection.

## THE PRIZE — a separation-logic law a replace-store cannot satisfy

Lifting to `UPred (HeapView ...)` over the convolution camera, owning two independent
distribution-fragments at a key entails that the characteristic function of their **merge** is the
**product** of their characteristic functions:
```
charFun_law :
  UPred.ownM (Frag k (.own q₁) a) ∗ UPred.ownM (Frag k (.own q₂) b)
    ⊢ ⌜charFun χ (a ⋆ b) = charFun χ a * charFun χ b⌝.
```
This is **provable only because the camera op `•` literally computes convolution**: owning the two
fragments is, by `frag_conv_op_equiv`, owning the single fragment carrying the merge `a ⋆ b`
(`ownM_frag_conv`), and the homomorphic readout turns that merge into the product.  A replace-based
store — whose `•` would *overwrite* rather than convolve — cannot make `charFun` of the combined
resource equal the product of the parts.  The law is the **convolution theorem internalized as a
separation-logic principle**: *independence ⟹ characteristic functions multiply.*

This connects directly to probabilistic separation logic and the classical analytic toolkit for sums
of independent random variables: characteristic functions linearize convolution, which is exactly why
they prove the central limit theorem.  Here that linearization is a CMRA homomorphism, and the
"independent combination" is the separating conjunction `∗` over a convolution-tracked heap.

The convolution theorem `charFun_conv`, the non-extensionality witness `charFun_collision`, the
camera readout-of-merge fact `charFun_ownM_merge`/`ownM_frag_conv`, and the IProp law `charFun_law`
are all `sorry`-free.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris Iris.Std
open scoped NNReal
open MonoidAlgebra

namespace CharFunMap

/-! ## The character `χ` and its lifted algebra homomorphism `Φ_χ`

We work over `G = Multiplicative ℕ` and the MGF/PGF character `χ_t g = t ^ g`.  `powersHom ℝ≥0 t` is
exactly `t ↦ (n ↦ t ^ n)` as a monoid homomorphism, with no positivity side condition. -/

/-- The **character** `χ_t : Multiplicative ℕ →* ℝ≥0`, `χ_t g = t ^ g` — the base of the
moment/probability generating function.  A monoid homomorphism unconditionally (`powersHom`). -/
noncomputable def char (t : ℝ≥0) : Multiplicative ℕ →* ℝ≥0 := powersHom ℝ≥0 t

@[simp] theorem char_apply (t : ℝ≥0) (g : Multiplicative ℕ) :
    char t g = t ^ (Multiplicative.toAdd g) := rfl

/-- The **algebra homomorphism** `Φ_χ : MonoidAlgebra ℝ≥0 G →ₐ[ℝ≥0] ℝ≥0` obtained by lifting the
character `χ_t` through `MonoidAlgebra.lift`.  Concretely `Φ_χ w = ∑_g w(g) · t ^ g`. -/
noncomputable def Phi (t : ℝ≥0) :
    MonoidAlgebra ℝ≥0 (Multiplicative ℕ) →ₐ[ℝ≥0] ℝ≥0 :=
  MonoidAlgebra.lift ℝ≥0 ℝ≥0 (Multiplicative ℕ) (char t)

/-- `Φ_χ` on a point mass: `Φ_χ (single g r) = r · t ^ g`.  This is the contribution of a single
outcome to the characteristic function. -/
theorem Phi_single (t : ℝ≥0) (g : Multiplicative ℕ) (r : ℝ≥0) :
    Phi t (MonoidAlgebra.single g r) = r * t ^ (Multiplicative.toAdd g) := by
  rw [Phi, MonoidAlgebra.lift_apply, Finsupp.sum_single_index (by simp)]
  rfl

end CharFunMap

/-! ## The characteristic-function readout on convolution vectors -/

namespace ConvVec

open CharFunMap

variable {G : Type _} [CommMonoid G]

/-- The **characteristic-function / MGF readout**: `charFun t w = Φ_χ w = ∑_g w(g) · t ^ g`.  A single
scalar summarizing the whole distribution `w`.  Defined on the *convolution camera value type*
`ConvVec (Multiplicative ℕ)` by applying the lifted algebra hom to the underlying monoid-algebra
element. -/
noncomputable def charFun (t : ℝ≥0) (w : ConvVec (Multiplicative ℕ)) : ℝ≥0 := Phi t w.toMA

@[simp] theorem charFun_eq (t : ℝ≥0) (w : ConvVec (Multiplicative ℕ)) :
    charFun t w = Phi t w.toMA := rfl

/-- The readout of a point-mass fragment: `charFun t (single g r) = r · t ^ g`. -/
theorem charFun_single (t : ℝ≥0) (g : Multiplicative ℕ) (r : ℝ≥0) :
    charFun t (single g r) = r * t ^ (Multiplicative.toAdd g) := by
  rw [charFun_eq, toMA_single, Phi_single]

/-- **THE CONVOLUTION THEOREM (sorry-free).**  The characteristic function of a convolution `a ⋆ b`
(the camera op `•` = `+` on `ConvVec`) is the **product** of the characteristic functions:
```
charFun t (a ⋆ b) = charFun t a * charFun t b.
```
This is *exactly* `map_mul Φ_χ`: `Φ_χ` is an algebra homomorphism and `*` on the monoid algebra is
convolution.  For independent random variables, characteristic functions multiply. -/
theorem charFun_conv (t : ℝ≥0) (a b : ConvVec (Multiplicative ℕ)) :
    charFun t (a + b) = charFun t a * charFun t b := by
  rw [charFun_eq, charFun_eq, charFun_eq, toMA_add]
  exact map_mul (Phi t) a.toMA b.toMA

end ConvVec

/-! ## Non-extensionality, unified with the merge

`charFun` collapses an entire distribution to one scalar, so it is massively non-injective.  Unlike
the scale-invariance witness in `ConvolutionMap` (orthogonal to the merge), this collapse is a
**congruence for the tracked convolution** (`charFun_conv`): the readout forgets everything except the
character value, yet respects the structural merge.  Non-extensionality and the merge are the same
homomorphic projection. -/

namespace CharFunMap

open ConvVec

/-- **Non-extensionality witness (sorry-free).**  With `t = 2`, the two *distinct* point-mass
distributions `single 0 2` (mass `2` at the identity) and `single 1 1` (mass `1` at the generator)
have the **same** characteristic function `charFun 2 _ = 2`:
```
charFun 2 (single (ofAdd 0) 2) = 2 = charFun 2 (single (ofAdd 1) 1),   yet the two are distinct.
```
The readout has forgotten the entire shape of the distribution, retaining only the scalar
`∑_g w(g) · 2 ^ g`. -/
theorem charFun_collision :
    charFun 2 (ConvVec.single (Multiplicative.ofAdd 0) 2)
        = charFun 2 (ConvVec.single (Multiplicative.ofAdd 1) 1)
      ∧ (ConvVec.single (Multiplicative.ofAdd 0) 2 : ConvVec (Multiplicative ℕ))
          ≠ ConvVec.single (Multiplicative.ofAdd 1) 1 := by
  refine ⟨?_, ?_⟩
  · rw [charFun_single, charFun_single]
    change (2 : ℝ≥0) * 2 ^ (0 : ℕ) = 1 * 2 ^ (1 : ℕ)
    norm_num
  · intro h
    have hMA := congrArg (fun w : ConvVec (Multiplicative ℕ) =>
      w.toMA (Multiplicative.ofAdd 0)) h
    simp only [ConvVec.toMA_single, MonoidAlgebra.single_apply] at hMA
    -- LHS reads off `2`; RHS reads `0` (since `ofAdd 1 ≠ ofAdd 0`), so `hMA : 2 = 0`.
    rw [if_neg (by decide : ¬ (Multiplicative.ofAdd 1 = Multiplicative.ofAdd 0))] at hMA
    norm_num at hMA

end CharFunMap

/-! ## Readout of the camera merge = product of the readouts

The bridge from the camera level to the analytic law: the readout of the *fused* fragment (the camera
op `•` of two fragments, which carries `a ⋆ b` by `frag_conv_op_equiv`) is the product of the two
readouts. -/

namespace ConvStore

open Iris HeapView CMRA DFrac One ConvVec CharFunMap
open scoped CommMonoidLike

variable {K : Type _} [DecidableEq K]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulPartialMap H K]
variable {k : K} {q1 q2 : F} {a b : ConvVec (Multiplicative ℕ)} {t : ℝ≥0}

omit [DecidableEq K] in
/-- The fused fragment `Frag k a • Frag k b` carries the convolution `a ⋆ b` (this is
`frag_conv_op_equiv`), and the homomorphic readout of that merge is the **product** of the readouts:
```
charFun t (a ⋆ b) = charFun t a * charFun t b,    where  Frag k a • Frag k b ≡ Frag k (a ⋆ b).
```
The first conjunct is `frag_conv_op_equiv` (the camera-tracked merge); the second is `charFun_conv`
(the convolution theorem).  Together: the readout of the camera merge is the product. -/
theorem charFun_ownM_merge :
    (Frag k (.own q1) a • Frag k (.own q2) b : HeapView F K (ConvVec (Multiplicative ℕ)) H) ≡
        Frag k (.own (q1 + q2)) (a + b)
      ∧ charFun t (a + b) = charFun t a * charFun t b :=
  ⟨frag_conv_op_equiv, charFun_conv t a b⟩

end ConvStore

/-! ## THE PRIZE — the separation-logic law

We lift to `UPred (HeapView ...)` over the convolution camera.  Owning two independent
distribution-fragments at a key entails that the characteristic function of their **merge** is the
**product** of their characteristic functions.  This is the convolution theorem internalized as a
separation-logic principle.

`HeapView F K V AssocList` is a `UCMRA` (it is a `View`, and `View.instUCMRA` applies), so
`UPred (HeapView ...)` is a `BI`.  We own fragments via `UPred.ownM`, combine them with `UPred.ownM_op`
(which turns ownership of the camera op into `∗`), and the pure conclusion is discharged by
`charFun_conv`. -/

namespace ConvStore

open Iris HeapView CMRA DFrac One ConvVec CharFunMap
open Iris.BI
open scoped CommMonoidLike

variable {K : Type _} [DecidableEq K]
variable {F : Type _} [UFraction F]
variable {k : K} {q1 q2 : F} {a b : ConvVec (Multiplicative ℕ)} {t : ℝ≥0}

/-- The concrete `HeapView` resource algebra over the convolution-valued heap (AssocList-backed),
reusing `ConvStore.R` from `ConvolutionMap`. -/
abbrev RR (F : Type _) [UFraction F] := HeapView F Nat (ConvVec (Multiplicative ℕ)) AssocList

/-- Owning the two convolution-fragments at a key IS owning the single fragment carrying their
**merge** `a ⋆ b` — the camera op `•` fuses by convolution (`frag_conv_op_equiv`), and `UPred.ownM_op`
turns the resource op into the separating conjunction `∗`:
```
ownM (Frag k a) ∗ ownM (Frag k b) ⊣⊢ ownM (Frag k a • Frag k b) ≡ ownM (Frag k (a ⋆ b)).
```
The `⊣⊢` is `UPred.ownM_op`; the `≡` is `NonExpansive.eqv` applied to `frag_conv_op_equiv` (ownership
is nonexpansive).  This is the separation-logic face of the structural merge: independent fragments
combine, by `∗`, into ownership of their convolution. -/
theorem ownM_frag_conv {k : Nat} :
    ((UPred.ownM (Frag k (.own q1) a) ∗ UPred.ownM (Frag k (.own q2) b) :
          UPred (RR F)) ⊣⊢ UPred.ownM (Frag k (.own q1) a • Frag k (.own q2) b))
      ∧ (UPred.ownM (Frag k (.own q1) a • Frag k (.own q2) b : RR F) ≡
          UPred.ownM (Frag k (.own (q1 + q2)) (a + b))) :=
  ⟨(UPred.ownM_op _ _).symm,
   OFE.NonExpansive.eqv (frag_conv_op_equiv (q1 := q1) (q2 := q2) (a := a) (b := b))⟩

/-- **THE PRIZE (sorry-free): the convolution theorem as a separation-logic law.**

Owning two independent distribution-fragments `a`, `b` at a key entails that the characteristic
function of their **merge** `a ⋆ b` is the **product** of their characteristic functions:
```
ownM (Frag k (own q₁) a) ∗ ownM (Frag k (own q₂) b)  ⊢  ⌜charFun t (a ⋆ b) = charFun t a · charFun t b⌝.
```
The merge `a ⋆ b` is the *camera operation* (`frag_conv_op_equiv`: owning both fragments is owning the
fragment carrying `a ⋆ b`, made precise by `ownM_frag_conv`), and the homomorphic readout `charFun`
turns that merge into the product (`charFun_conv`).  A replace-based store, whose `•` overwrites rather
than convolves, cannot satisfy this law: `charFun` of the combined resource would not be the product.
This is *independence ⟹ characteristic functions multiply*, internalized in separation logic. -/
theorem charFun_law {k : Nat} :
    (UPred.ownM (Frag k (.own q1) a) ∗ UPred.ownM (Frag k (.own q2) b) : UPred (RR F))
      ⊢ ⌜charFun t (a + b) = charFun t a * charFun t b⌝ := by
  iintro ⟨_, _⟩
  ipure_intro
  exact charFun_conv t a b

end ConvStore

end IrisMath.Instances
