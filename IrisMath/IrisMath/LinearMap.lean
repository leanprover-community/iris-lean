module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Iris

@[expose] public section

open Iris OFE

/-! # OFE on linear maps

For a semiring `R`, additive commutative monoids `M` and `N` carrying `R`-module structures,
and an Iris `OFE` structure on `N`, the type `M →ₗ[R] N` of `R`-linear maps inherits an `OFE`
structure pointwise:

* `f ≡ g`        iff `∀ x, f x ≡ g x`;
* `f ≡{n}≡ g`    iff `∀ x, f x ≡{n}≡ g x`.

All five `OFE` axioms reduce directly to the corresponding pointwise statements in `N`.

## COFE caveat

Note that we do *not* attempt to lift the `IsCOFE` structure from `N` to `M →ₗ[R] N`. Given a
chain `c : Chain (M →ₗ[R] N)` we may define the pointwise limit
`x ↦ IsCOFE.compl (chainAt c x)`, but in general this limit fails to be `R`-linear: pointwise
`n`-convergence in the OFE sense need not preserve addition or scalar multiplication, so the
limit of a chain of `R`-linear maps need not be `R`-linear. Obtaining `IsCOFE (M →ₗ[R] N)`
requires additional hypotheses on the interaction of `N`'s `IsCOFE.compl` with its module
structure, and is not pursued here.

## Connecting back to `N`

We provide:

* `NonExpansive (fun f : M →ₗ[R] N ↦ f x)` — evaluation at a fixed `x : M`;
* `evalHom x : (M →ₗ[R] N) -n> N` — the same as a non-expansive Hom.
-/

namespace IrisMath.LinearMap

variable {R : Type*} {M : Type*} {N : Type*}
  [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The Iris `OFE` structure on `M →ₗ[R] N`, inherited pointwise from `N`.

`f ≡ g` means `∀ x, f x ≡ g x`, and `f ≡{n}≡ g` means `∀ x, f x ≡{n}≡ g x`. -/
instance instOFE [OFE N] : OFE (M →ₗ[R] N) where
  Equiv f g := ∀ x, f x ≡ g x
  Dist n f g := ∀ x, f x ≡{n}≡ g x
  dist_eqv :=
    { refl _ _ := dist_eqv.refl _
      symm h _ := dist_eqv.symm (h _)
      trans h₁ h₂ _ := dist_eqv.trans (h₁ _) (h₂ _) }
  equiv_dist {_ _} := by
    simp only [equiv_dist]
    exact forall_comm
  dist_lt h₁ h₂ _ := dist_lt (h₁ _) h₂

section
variable [OFE N]

@[simp] theorem equiv_def {f g : M →ₗ[R] N} : f ≡ g ↔ ∀ x, f x ≡ g x := Iff.rfl

@[simp] theorem dist_def {n : Nat} {f g : M →ₗ[R] N} :
    f ≡{n}≡ g ↔ ∀ x, f x ≡{n}≡ g x := Iff.rfl

/-- Evaluation `f ↦ f x : (M →ₗ[R] N) → N` at a fixed point `x : M` is non-expansive. -/
instance eval_ne (x : M) : NonExpansive (fun (f : M →ₗ[R] N) ↦ f x) where
  ne _ _ _ h := h x

/-- Two linear maps that are equivalent in `M →ₗ[R] N` are equivalent pointwise. -/
theorem Equiv.apply {f g : M →ₗ[R] N} (h : f ≡ g) (x : M) : f x ≡ g x := h x

/-- Two linear maps that are `n`-equivalent in `M →ₗ[R] N` are `n`-equivalent pointwise. -/
theorem Dist.apply {n : Nat} {f g : M →ₗ[R] N} (h : f ≡{n}≡ g) (x : M) : f x ≡{n}≡ g x := h x

/-- Evaluation at `x : M` packaged as a non-expansive Hom `(M →ₗ[R] N) -n> N`. -/
def evalHom (x : M) : (M →ₗ[R] N) -n> N where
  f g := g x
  ne := eval_ne x

@[simp] theorem evalHom_apply (x : M) (f : M →ₗ[R] N) : evalHom x f = f x := rfl

end

/-! ### Leibniz transfer

If `N` is `Leibniz` (i.e. its OFE equivalence coincides with `=`), then so is `M →ₗ[R] N`,
since extensionality for `R`-linear maps is precisely pointwise equality. -/

instance instLeibniz [OFE N] [Leibniz N] : Leibniz (M →ₗ[R] N) where
  eq_of_eqv h := _root_.LinearMap.ext fun x ↦ Leibniz.eq_of_eqv (h x)

end IrisMath.LinearMap
