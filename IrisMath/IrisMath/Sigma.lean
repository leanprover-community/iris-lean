/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris

@[expose] public section

open Iris OFE

namespace IrisMath.Sigma

/-! # Dependent sum as an OFE / COFE

The dependent sum `Σ x : α, β x` is the natural dependent generalisation of the
product OFE `α × β` and the sum OFE `α ⊕ β` from `Iris.Algebra.OFE`. Iris-Lean
already exposes the underlying `OFE`, `IsCOFE`, and `Discrete` instances on
`Sigma P` directly; in this module we package them under the `IrisMath.Sigma`
namespace, provide a convenience type alias `SigmaO`, and prove a handful of
ergonomic lemmas that are useful for downstream developments.

The subtlety inherent in this construction is that, unlike `Prod` and `Sum`,
the type of the second component depends on the first. To compare
`⟨x, b⟩` and `⟨x', b'⟩` for `n`-equivalence we therefore require a proof
`heq : x = x'`, transport `b` along `heq`, and only then compare in
`β x'`. The bundled definition reads

```
Equiv p q := ∀ n, ∃ h : p.1 = q.1, h ▸ p.2 ≡{n}≡ q.2
Dist n p q := ∃ h : p.1 = q.1, h ▸ p.2 ≡{n}≡ q.2
```

The Iris-Lean library proves this is a (C)OFE — see `Iris.instOFESigma`,
`Iris.OFE.instDiscreteSigma`, and the `IsCOFE (Sigma P)` instance in
`Iris/Algebra/OFE.lean`. Note that the first component carries no OFE
constraint: it is treated discretely, with literal equality of fibres.

When `α` *itself* carries an OFE, the canonical projection
`Sigma.fst : Sigma P → α` is already non-expansive (`Iris.OFE.Sigma.fst_ne`)
because two `Sigma`-values can only be `n`-equivalent if their fibres are
literally equal — which forces a fortiori `Dist n` equality in `α`. We expose
the bundled `Hom` form `fstHom`. Promoting `Sigma.fst` to a *Leibniz*-style
identity requires that `α` be a Leibniz OFE, in which case OFE-equivalence on
the first component is honest equality.
-/

variable {α : Type _} {β : α → Type _}

/-- The dependent sum, packaged so it can be referred to with a name carrying
its OFE structure (compare `Iris.OFE.LeibnizO`, `IrisMath.Stream.StreamO`).
Definitionally identical to `Sigma β`. -/
abbrev SigmaO (β : α → Type _) [∀ x, OFE (β x)] : Type _ := Sigma β

/-- The OFE structure on the dependent sum, inherited from
`Iris.instOFESigma`. -/
instance instOFE [∀ x, OFE (β x)] : OFE (SigmaO β) := inferInstance

/-- The COFE structure on the dependent sum, inherited from
`Iris.COFE.instSigmaCOFE` (the `IsCOFE (Sigma P)` instance). -/
instance instCOFE [∀ x, COFE (β x)] : COFE (SigmaO β) := inferInstance

/-- If every fibre is a discrete OFE, then so is the dependent sum. -/
instance instDiscrete [∀ x, OFE (β x)] [∀ x, Discrete (β x)] :
    Discrete (SigmaO β) := inferInstance

/-- If every fibre is a Leibniz OFE and `α` itself has decidable equality (so
that transport is canonically determined), then `SigmaO β` is a Leibniz OFE.

This instance does not appear in core Iris; we prove it here directly from
`Sigma.equiv_eq_alt` and the fibrewise Leibniz lemma. -/
instance instLeibniz [∀ x, OFE (β x)] [∀ x, Leibniz (β x)] :
    Leibniz (SigmaO β) where
  eq_of_eqv {x y} h := by
    obtain ⟨heq, hsnd⟩ := Iris.OFE.Sigma.equiv_eq_alt.mp h
    rcases x with ⟨x, b⟩
    rcases y with ⟨y, b'⟩
    simp only at heq
    subst heq
    simp only at hsnd
    rw [eq_of_eqv hsnd]

/-! ## Constructor and projection lemmas

These are slim wrappers around the Iris-level lemmas, restated to mention
`SigmaO` so they can be discovered through dot notation on the dependent
sum-as-OFE. -/

variable [∀ x, OFE (β x)]

/-- `n`-equivalence of dependent pairs unfolds to a heterogeneous equation on
the fibres together with a transported `n`-equivalence on the carriers. -/
theorem dist_iff {n} {p q : SigmaO β} :
    p ≡{n}≡ q ↔ ∃ heq : p.fst = q.fst, heq ▸ p.snd ≡{n}≡ q.snd :=
  Iff.rfl

/-- Equivalence of dependent pairs unfolds to a fibrewise equation together
with a transported equivalence on the carriers. This is `Sigma.equiv_eq_alt`,
restated under the `SigmaO` name. -/
theorem equiv_iff {p q : SigmaO β} :
    p ≡ q ↔ ∃ heq : p.fst = q.fst, heq ▸ p.snd ≡ q.snd :=
  Iris.OFE.Sigma.equiv_eq_alt

/-- Smart constructor: from a fibre-level equality and a transported
`n`-equivalence on the second components, build a `Dist` of dependent pairs. -/
protected theorem mk_dist {n} {i₁ i₂ : α} {v₁ : β i₁} {v₂ : β i₂}
    (heq : i₁ = i₂) (h : heq ▸ v₁ ≡{n}≡ v₂) :
    (⟨i₁, v₁⟩ : SigmaO β) ≡{n}≡ ⟨i₂, v₂⟩ :=
  Iris.OFE.Sigma.mk_dist heq h

/-- Smart constructor: from a fibre-level equality and a transported
equivalence on the second components, build an equivalence of dependent pairs.
-/
protected theorem mk_equiv {i₁ i₂ : α} {v₁ : β i₁} {v₂ : β i₂}
    (heq : i₁ = i₂) (h : heq ▸ v₁ ≡ v₂) :
    (⟨i₁, v₁⟩ : SigmaO β) ≡ ⟨i₂, v₂⟩ :=
  Iris.OFE.Sigma.mk_equiv heq h

/-- For a fixed fibre index `a : α`, the constructor `Sigma.mk a` is
non-expansive `β a → SigmaO β`. -/
instance mk_ne (a : α) : NonExpansive (Sigma.mk a : β a → SigmaO β) :=
  Iris.OFE.Sigma.mk_ne a

/-- Projection of the first component, packaged as the bundled
`Sigma.fst_ne` instance from Iris. -/
theorem dist_fst {n} {p q : SigmaO β} (h : p ≡{n}≡ q) : p.fst = q.fst := h.1

/-- The second component is preserved by `n`-equivalence, modulo transport
along the fibrewise equality. -/
theorem dist_snd {n} {p q : SigmaO β} (h : p ≡{n}≡ q) :
    h.1 ▸ p.snd ≡{n}≡ q.snd := h.2

/-- A reflexive form of `mk_dist`: replacing the second component by an
`n`-equivalent one yields an `n`-equivalent pair. -/
theorem mk_dist_of_dist {n} (a : α) {v₁ v₂ : β a} (h : v₁ ≡{n}≡ v₂) :
    (⟨a, v₁⟩ : SigmaO β) ≡{n}≡ ⟨a, v₂⟩ :=
  ⟨rfl, h⟩

/-- A reflexive form of `mk_equiv`. -/
theorem mk_equiv_of_equiv (a : α) {v₁ v₂ : β a} (h : v₁ ≡ v₂) :
    (⟨a, v₁⟩ : SigmaO β) ≡ ⟨a, v₂⟩ :=
  fun _ => ⟨rfl, h.dist⟩

/-! ## Functoriality

`Sigma.mapO` from Iris-Lean is a non-expansive map between dependent sums; we
restate it here at the `SigmaO` type so it is findable by users of this module.
-/

/-- Non-expansive lift of a fibrewise family of non-expansive maps to the
dependent sum, inherited from `Iris.Sigma.mapO`. -/
def mapO {β₁ β₂ : α → Type _} [∀ x, OFE (β₁ x)] [∀ x, OFE (β₂ x)] :
    ((a : α) → β₁ a -n> β₂ a) -n> SigmaO β₁ -n> SigmaO β₂ :=
  Iris.Sigma.mapO

end IrisMath.Sigma

namespace IrisMath.Sigma

/-! ## The case where the index has its own OFE

If `α` already carries an OFE (not merely the discrete one used implicitly by
`instOFESigma`), then the first projection is non-expansive into `α`. This is
inherited from `Iris.OFE.Sigma.fst_ne`. We package it as a bundled `Hom`. -/

variable {α : Type _} [OFE α] {β : α → Type _} [∀ x, OFE (β x)]

/-- The first projection, bundled as a non-expansive homomorphism `SigmaO β -n> α`.
Available when `α` carries its own OFE. -/
def fstHom : SigmaO β -n> α where
  f := Sigma.fst
  ne := Iris.OFE.Sigma.fst_ne

@[simp] theorem fstHom_apply (p : SigmaO β) : fstHom (β := β) p = p.fst := rfl

end IrisMath.Sigma

namespace IrisMath.Sigma

/-! ## Specialisation to a `LeibnizO`-indexed family

The most common usage of dependent OFEs in Iris-style developments is to index
a family of OFEs by a *plain* type (no OFE structure on the index, equivalently
the Leibniz OFE). We package this directly as `LeibnizSigma`. -/

variable {α : Type _} {β : α → Type _}

/-- Dependent sum indexed by a plain type, with each fibre carrying an OFE.
The index type is wrapped in `LeibnizO` only morally — at the term level we use
the bare `Sigma β`, but the OFE structure obtained is identical to working with
the Leibniz OFE on `α`. -/
abbrev LeibnizSigma (β : α → Type _) [∀ x, OFE (β x)] : Type _ := SigmaO β

instance [∀ x, OFE (β x)] : OFE (LeibnizSigma β) := inferInstance
instance [∀ x, COFE (β x)] : COFE (LeibnizSigma β) := inferInstance
instance [∀ x, OFE (β x)] [∀ x, Discrete (β x)] :
    Discrete (LeibnizSigma β) := inferInstance

/-- For a discrete-index family with each fibre a Leibniz OFE, the whole
dependent sum is Leibniz. -/
example [∀ x, OFE (β x)] [∀ x, Leibniz (β x)] : Leibniz (LeibnizSigma β) :=
  inferInstance

end IrisMath.Sigma
