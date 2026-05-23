module

public import Mathlib.Topology.ContinuousMap.Basic
public import Iris

@[expose] public section

open Iris OFE ContinuousMap

/-! # OFE on continuous maps

For a topological space `X` and a target type `Y` carrying an Iris `OFE` structure, the type
`C(X, Y) = ContinuousMap X Y` of continuous maps from `X` to `Y` inherits an `OFE` structure
pointwise:

* `f ≡ g`        iff `∀ x, f x ≡ g x`;
* `f ≡{n}≡ g`    iff `∀ x, f x ≡{n}≡ g x`.

All five `OFE` axioms reduce directly to the corresponding pointwise statements in `Y`.

## COFE caveat

Note that we do *not* attempt to lift the `IsCOFE` structure from `Y` to `C(X, Y)`. Given a
chain `c : Chain C(X, Y)` we may define the pointwise limit `x ↦ IsCOFE.compl (chainAt c x)`,
but in general this limit fails to be continuous: pointwise `n`-convergence in the OFE sense
is *not* uniform in the topological sense, so the limit of a chain of continuous maps need
not be continuous. Obtaining `IsCOFE C(X, Y)` requires additional hypotheses (e.g. some form
of uniform convergence interacting with the topology of `Y`), and is not pursued here.

## Connecting back to `Y`

We provide:

* `NonExpansive (ContinuousMap.const X : Y → C(X, Y))` — the constant-map operation;
* `NonExpansive (ContinuousMap.eval x : C(X, Y) → Y)` — evaluation at a fixed point `x : X`.

These witnesses connect the OFE on `C(X, Y)` back to the OFE on `Y`.
-/

namespace IrisMath.Continuous

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The Iris `OFE` structure on `C(X, Y) = ContinuousMap X Y`, inherited pointwise from `Y`.

`f ≡ g` means `∀ x, f x ≡ g x`, and `f ≡{n}≡ g` means `∀ x, f x ≡{n}≡ g x`. -/
instance instOFE [OFE Y] : OFE C(X, Y) where
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
variable [OFE Y]

@[simp] theorem equiv_def {f g : C(X, Y)} : f ≡ g ↔ ∀ x, f x ≡ g x := Iff.rfl

@[simp] theorem dist_def {n : Nat} {f g : C(X, Y)} : f ≡{n}≡ g ↔ ∀ x, f x ≡{n}≡ g x := Iff.rfl

/-- Evaluation `f ↦ f x : C(X, Y) → Y` at a fixed point `x : X` is non-expansive. -/
instance eval_ne (x : X) : NonExpansive (fun (f : C(X, Y)) ↦ f x) where
  ne _ _ _ h := h x

/-- The constant-map operation `y ↦ ContinuousMap.const X y : Y → C(X, Y)` is non-expansive. -/
instance const_ne : NonExpansive (ContinuousMap.const X (β := Y)) where
  ne _ _ _ h _ := h

/-- Two continuous maps that are equivalent in `C(X, Y)` are equivalent pointwise. -/
theorem Equiv.apply {f g : C(X, Y)} (h : f ≡ g) (x : X) : f x ≡ g x := h x

/-- Two continuous maps that are `n`-equivalent in `C(X, Y)` are `n`-equivalent pointwise. -/
theorem Dist.apply {n : Nat} {f g : C(X, Y)} (h : f ≡{n}≡ g) (x : X) : f x ≡{n}≡ g x := h x

/-- Evaluation at `x : X` packaged as a non-expansive Hom `C(X, Y) -n> Y`. -/
def evalHom (x : X) : C(X, Y) -n> Y where
  f g := g x
  ne := eval_ne x

@[simp] theorem evalHom_apply (x : X) (f : C(X, Y)) : evalHom x f = f x := rfl

/-- The constant-map operation packaged as a non-expansive Hom `Y -n> C(X, Y)`. -/
def constHom : Y -n> C(X, Y) where
  f := ContinuousMap.const X
  ne := const_ne

@[simp] theorem constHom_apply (y : Y) (x : X) : (constHom (X := X) y) x = y := rfl

end

section
variable {Z : Type*} [TopologicalSpace Z] [OFE Y] [OFE Z]

/-! ### Composition

Composition `g.comp f : C(X, Z)` of continuous maps `g : C(Y, Z)` and `f : C(X, Y)` is
non-expansive in the *left* argument `g` without further assumptions, since changing `g` to
`g'` with `g ≡{n}≡ g'` gives `g (f x) ≡{n}≡ g' (f x)` directly.

Non-expansiveness in the *right* argument `f` requires `g` to itself be non-expansive on `Y`,
since one must transport an `n`-equivalence `f x ≡{n}≡ f' x` through `g`. Hence we do not
obtain `NonExpansive₂` for `ContinuousMap.comp` unconditionally; we only provide the
conditional right-argument version.
-/

/-- Composition `g ↦ g.comp f : C(Y, Z) → C(X, Z)` on the left is non-expansive in `g`. -/
instance comp_left_ne (f : C(X, Y)) :
    NonExpansive (fun (g : C(Y, Z)) ↦ g.comp f) where
  ne _ _ _ h x := h (f x)

/-- Composition `f ↦ g.comp f : C(X, Y) → C(X, Z)` on the right is non-expansive in `f`
when `g` is non-expansive on the underlying OFE of `Y`. -/
theorem comp_right_ne (g : C(Y, Z)) [NonExpansive g] :
    NonExpansive (fun (f : C(X, Y)) ↦ g.comp f) where
  ne _ _ _ h x := NonExpansive.ne (h x)

end

/-! ### Leibniz transfer

If `Y` is `Leibniz` (i.e. its OFE equivalence coincides with `=`), then so is `C(X, Y)`,
since extensionality for continuous maps is precisely pointwise equality. -/

instance instLeibniz [OFE Y] [Leibniz Y] : Leibniz C(X, Y) where
  eq_of_eqv h := ContinuousMap.ext fun x ↦ Leibniz.eq_of_eqv (h x)

end IrisMath.Continuous
