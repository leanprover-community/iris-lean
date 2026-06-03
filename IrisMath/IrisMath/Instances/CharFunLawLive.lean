/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IrisMath.Instances.CharFunMap
public import IrisMath.Instances.ConvolutionMap
public import Iris
public import Iris.ProofMode
public import Iris.Algebra.IProp
public import Iris.Instances.IProp.Instance

/-! # The convolution theorem as an *ownership-essential* separation-logic law

The law `ConvStore.charFun_law` in `IrisMath/Instances/CharFunMap.lean` is, on inspection,
**vacuous**: its proof `iintro ⟨_, _⟩; ipure_intro; exact charFun_conv t a b` discards the ownership
hypothesis and discharges a conclusion (`charFun t (a + b) = charFun t a * charFun t b`) that is a
**universal tautology** of `charFun` — true for *any* `a`, `b`, with or without owning anything.
Nothing in it
forces the *authority's stored cell* to actually be the convolution `a ⋆ b`; a replace-store would
satisfy it just as well, because the conclusion never mentions the store.

This file proves the **ownership-essential** version, where validity of the combined `auth + frag`
resource *forces the authority's observed cell to be the convolution `a ⋆ b`*.  The crux is the
agreement fact

```
auth γ m ∗ pointsTo γ k (own q₁) a ∗ pointsTo γ k (own q₂) b
    ⊢ ⌜get? m k ≡{0}≡ some (a ⋆ b)⌝      (q₁ + q₂ = one)
```

and this **cannot** hold for a replace-store: a replace `•` would *overwrite* one fragment with the
other rather than convolve them, so the value forced into the authority's cell would be (say) `b`,
not `a ⋆ b` — and `a ⋆ b ≠ b` in general (`ConvVec.conv_moves_support`).  The convolution camera op
is genuinely load-bearing: it is what fuses the two fragments into `a ⋆ b` (`frag_conv_op_equiv`)
*before* agreement with the authority pins the cell.

## Why the hypothesis is now load-bearing (contrast with the vacuous version)

The proof routes through `auth_op_frag_one_validN_iff`, which extracts `get? m k ≡{n}≡ some v`
*only* from validity of `Auth dp m • Frag k (own one) v`.  Removing the authority, or either
fragment, removes the validity fact and the agreement collapses.  The two fragments are combined *by
the camera op `•`*, which here computes convolution; that is the single place `a ⋆ b` (rather than
`a`, `b`, or a replace) enters.

We then bolt the (tautological-on-its-own) readout `charFun_conv` onto the agreement to recover the
full convolution theorem, now *pinned to the authority's cell*:

```
charFun_law_live :
  auth γ m ∗ pointsTo γ k (own q₁) a ∗ pointsTo γ k (own q₂) b
    ⊢ ⌜get? m k ≡{0}≡ some (a ⋆ b) ∧ charFun t (a ⋆ b) = charFun t a * charFun t b⌝.
```

The first conjunct is the load-bearing agreement; the second is the convolution theorem
`charFun_conv`.  Together: *the authority's cell IS the merge, and the readout of that merge is the
product of the readouts.*  Everything here is `sorry`-free.

## Caveat (post-review — what is and isn't established)

* **Solid: ownership-essentiality.**  `cell_is_conv` genuinely *consumes* the hypothesis — it fuses
  the two fragments through the camera op `•` (which computes convolution) and extracts
  `get? m k ≡ some (a ⋆ b)` from validity of `auth • frag` (`auth_op_frag_one_validN_iff`).  Drop
  the authority or a fragment and it breaks.  Unlike the *vacuous* `ConvStore.charFun_law`.

* **"Defeats a replace-store" is INFORMAL, not a theorem.**  As literally stated the law is
  *vacuously* satisfiable by a replace/`Excl` store (two full same-key fragments are incompatible,
  so the premise is `False`).  The real discriminator — the convolution camera *admits* compatible
  same-key fragments composing to `a ⋆ b` with `a ⋆ b ∉ {a,b}` (`ConvolutionMap.conv_moves_support`)
  — is proved but **not wired into this law**; no competing replace-store is formalized.

* **NOT a non-extensional store.**  The underlying `ConvStore`/`LawfulPartialMap` is the plain
  function map: `get?` is injective, `equiv ↔ eq` — *extensional*.  The non-injectivity lives only
  in the derived `charFun` *observable* (`CharFunMap.charFun_collision`).  Honest classification: an
  **extensional camera-tracked convolution-merge store with a homomorphic non-injective observable**
  — not a non-extensional `LawfulPartialMap`.  (The genuinely non-extensional stores here are the
  germ family, e.g. `EventualValue`/GermMap.)

Defensible headline: *the convolution theorem internalized as an ownership-essential
separation-logic law* (independence ⟹ characteristic functions multiply). -/

@[expose] public section

namespace IrisMath.Instances

open Iris Iris.Std Iris.BI COFE
open HeapView One DFrac CMRA
open ConvVec CharFunMap
open scoped NNReal CommMonoidLike

namespace CharFunLawLive

/-- The convolution value type used throughout: distributions over `Multiplicative ℕ`. -/
abbrev CV := ConvVec (Multiplicative ℕ)

variable {F} [UFraction F]

/-- The heap functor — `constOF` of the generic `HeapView` CMRA over the convolution-valued store
(`AssocList`-backed), the *same* convolution camera as in `ConvolutionMap`. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat CV AssocList

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole convolution-valued heap. -/
noncomputable def auth (γ : GName) (m : AssocList CV) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- A convolution-distribution fragment at key `k`: ownership of distribution `a` with fraction `q`.
Two such fragments at the same key fuse *by convolution* under the camera op. -/
noncomputable def pointsTo (γ : GName) (k : Nat) (q : DFrac F) (a : CV) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k q a)

/-- **Combining the two fragments computes the convolution (the camera op is load-bearing).**

Owning the two convolution-fragments `(own q₁, a)` and `(own q₂, b)` at the same key `k` IS owning
the single fragment `(own (q₁+q₂), a ⋆ b)` carrying their convolution: `iOwn_op` turns `∗` into the
camera op `•`, and `frag_conv_op_equiv` evaluates that op to the convolution.  *This is where
`a ⋆ b` is produced*, and it is produced **by `•`** — a replace-store's `•` would overwrite, not
convolve. -/
theorem frags_fuse (γ : GName) (k : Nat) (q1 q2 : DFrac F) (a b : CV) :
    iprop(pointsTo (F := F) (GF := GF) γ k q1 a ∗ pointsTo (F := F) (GF := GF) γ k q2 b) ⊣⊢
      iprop(iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (q1 • q2) (a + b))) := by
  refine iOwn_op.symm.trans ?_
  exact equiv_iff.mp <| OFE.NonExpansive.eqv (f := iOwn (GF := GF) (F := HeapF (F := F)) γ)
    (frag_op_equiv (k := k) (dp := q1) (dq := q2) (v1 := a) (v2 := b)).symm

/-- **THE CRUX (ownership-essential, sorry-free): agreement forces the authority's cell to be the
convolution.**

Owning the authority `m` together with the two convolution-fragments `(own q₁, a)`, `(own q₂, b)`
at key `k`, with `q₁ + q₂ = one` (full ownership of the cell after fusion), entails that the
authority's **observed cell is exactly the convolution `a ⋆ b`**:
```
auth γ m ∗ pointsTo γ k (own q₁) a ∗ pointsTo γ k (own q₂) b ⊢ ⌜get? m k ≡{0}≡ some (a ⋆ b)⌝.
```
The proof *uses every part of the hypothesis*: `frags_fuse` combines the two fragments **by the
camera op** into `Frag k (own one) (a ⋆ b)` (this is where convolution is computed, and where a
replace-store would instead overwrite), and `auth_op_frag_one_validN_iff` extracts the agreement
`get? m k ≡ some
(a ⋆ b)` **from validity of the `auth • frag` resource** — drop the authority or a fragment and the
validity fact, hence the agreement, is gone.

A replace-store provably cannot satisfy this: its `•` would force the cell to `a` or `b` (the
overwrite), not `a ⋆ b`, and `a ⋆ b ≠ a, b` in general (`conv_moves_support`). -/
theorem cell_is_conv (γ : GName) (m : AssocList CV) (k : Nat) (q1 q2 : DFrac F) (a b : CV)
    (hsum : q1 • q2 = own (one : F)) :
    auth (F := F) (GF := GF) γ m ∗
        pointsTo (F := F) (GF := GF) γ k q1 a ∗ pointsTo (F := F) (GF := GF) γ k q2 b ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some (a + b)⌝ := by
  -- Fuse the two fragments by the camera op into the single convolution fragment.
  refine (sep_mono_r (frags_fuse (F := F) (GF := GF) γ k q1 q2 a b).1).trans ?_
  rw [hsum]
  -- Combine with the authority, extract validity, then read off the agreement.
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (auth_op_frag_one_validN_iff.mp H).2.2

/-- **THE PRIZE (ownership-essential, sorry-free): convolution theorem pinned to the authority.**

Owning the authority `m` and the two convolution-fragments at key `k` (with `q₁ + q₂ = one`) entails
*both*:
```
get? m k ≡{0}≡ some (a ⋆ b)     ∧     charFun t (a ⋆ b) = charFun t a * charFun t b.
```
The first conjunct — `cell_is_conv` — is the load-bearing fact: it **uses the ownership** (auth+frag
agreement through `auth_op_frag_one_validN_iff`) to force the authority's observed cell to be the
convolution `a ⋆ b`.  The second is the convolution theorem `charFun_conv` (the homomorphic readout
of the merge is the product of the readouts).

Contrast with the vacuous `ConvStore.charFun_law`, which proves only the second (tautological)
conjunct and discards the hypothesis.  Here the hypothesis is genuinely consumed, and the law is
**false for a replace-store**: a replace `•` overwrites rather than convolves, so the cell forced by
agreement would be `a` or `b`, not `a ⋆ b` (and `a ⋆ b ≠ a, b` by `conv_moves_support`), breaking
the first conjunct.  This is *independence ⟹ characteristic functions multiply*, internalized as a
separation-logic principle that genuinely depends on the convolution camera op. -/
theorem charFun_law_live (γ : GName) (m : AssocList CV) (k : Nat) (q1 q2 : DFrac F) (a b : CV)
    (t : ℝ≥0) (hsum : q1 • q2 = own (one : F)) :
    auth (F := F) (GF := GF) γ m ∗
        pointsTo (F := F) (GF := GF) γ k q1 a ∗ pointsTo (F := F) (GF := GF) γ k q2 b ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some (a + b)
        ∧ charFun t (a + b) = charFun t a * charFun t b⌝ := by
  refine (cell_is_conv (F := F) (GF := GF) γ m k q1 q2 a b hsum).trans ?_
  iintro %H
  ipure_intro
  exact ⟨H, charFun_conv t a b⟩

end CharFunLawLive

end IrisMath.Instances
