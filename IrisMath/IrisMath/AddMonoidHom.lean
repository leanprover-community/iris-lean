module

public import Mathlib.Algebra.Group.Hom.Defs
public import Iris

@[expose] public section

open Iris OFE

/-! # OFE on additive monoid homomorphisms

For an additive commutative monoid `α` and a target type `β` carrying both an `AddCommMonoid`
structure and an Iris `OFE` structure, the type `α →+ β` of additive monoid homomorphisms
inherits an `OFE` structure pointwise:

* `f ≡ g`        iff `∀ x, f x ≡ g x`;
* `f ≡{n}≡ g`    iff `∀ x, f x ≡{n}≡ g x`.

All five `OFE` axioms reduce directly to the corresponding pointwise statements in `β`.

## UCMRA caveat

We do *not* lift a `UCMRA` structure on `β` to `α →+ β`. Although `AddMonoidHom` carries a
pointwise `+` (which is itself an `AddMonoidHom`), the Iris CMRA `op` on `β` is in general
unrelated to `β`'s `+`. Hence the OFE-level pointwise structure on `α →+ β` may fail to align
with any candidate CMRA `op`, and a careful case-by-case alignment of `β`'s CMRA-`op` with
`β`'s `+` (e.g. via `LeibnizO (Additive _)`) is required. We leave the CMRA construction to
specialized instances.

## Connecting back to `β`

We provide:

* `NonExpansive (AddMonoidHom.eval x : (α →+ β) → β)` — evaluation at a fixed `x : α`;
* `evalHom x : (α →+ β) -n> β` — the same as a non-expansive Hom.
-/

namespace IrisMath.AddMonoidHom

variable {α : Type*} {β : Type*} [AddCommMonoid α] [AddCommMonoid β]

/-- The Iris `OFE` structure on `α →+ β`, inherited pointwise from `β`.

`f ≡ g` means `∀ x, f x ≡ g x`, and `f ≡{n}≡ g` means `∀ x, f x ≡{n}≡ g x`. -/
instance instOFE [OFE β] : OFE (α →+ β) where
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
variable [OFE β]

@[simp] theorem equiv_def {f g : α →+ β} : f ≡ g ↔ ∀ x, f x ≡ g x := Iff.rfl

@[simp] theorem dist_def {n : Nat} {f g : α →+ β} : f ≡{n}≡ g ↔ ∀ x, f x ≡{n}≡ g x := Iff.rfl

/-- Evaluation `f ↦ f x : (α →+ β) → β` at a fixed point `x : α` is non-expansive. -/
instance eval_ne (x : α) : NonExpansive (fun (f : α →+ β) ↦ f x) where
  ne _ _ _ h := h x

/-- Two additive monoid homs that are equivalent in `α →+ β` are equivalent pointwise. -/
theorem Equiv.apply {f g : α →+ β} (h : f ≡ g) (x : α) : f x ≡ g x := h x

/-- Two additive monoid homs that are `n`-equivalent in `α →+ β` are `n`-equivalent
pointwise. -/
theorem Dist.apply {n : Nat} {f g : α →+ β} (h : f ≡{n}≡ g) (x : α) : f x ≡{n}≡ g x := h x

/-- Evaluation at `x : α` packaged as a non-expansive Hom `(α →+ β) -n> β`. -/
def evalHom (x : α) : (α →+ β) -n> β where
  f g := g x
  ne := eval_ne x

@[simp] theorem evalHom_apply (x : α) (f : α →+ β) : evalHom x f = f x := rfl

end

/-! ### Leibniz transfer

If `β` is `Leibniz` (i.e. its OFE equivalence coincides with `=`), then so is `α →+ β`,
since extensionality for additive monoid homs is precisely pointwise equality. -/

instance instLeibniz [OFE β] [Leibniz β] : Leibniz (α →+ β) where
  eq_of_eqv h := _root_.AddMonoidHom.ext fun x ↦ Leibniz.eq_of_eqv (h x)

end IrisMath.AddMonoidHom
