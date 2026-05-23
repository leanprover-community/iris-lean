module

public import Mathlib.Order.Hom.Basic
public import Iris

@[expose] public section

open Iris OFE

/-! # OFE on order-preserving maps

For a preorder `α` and a target preorder `β` carrying an Iris `OFE` structure, the type
`α →o β` of order-preserving maps inherits an `OFE` structure pointwise:

* `f ≡ g`        iff `∀ x, f x ≡ g x`;
* `f ≡{n}≡ g`    iff `∀ x, f x ≡{n}≡ g x`.

All five `OFE` axioms reduce directly to the corresponding pointwise statements in `β`.

## COFE caveat

Note that we do *not* attempt to lift the `IsCOFE` structure from `β` to `α →o β`. Given a
chain `c : Chain (α →o β)` we may define the pointwise limit `x ↦ IsCOFE.compl (chainAt c x)`,
but in general this limit fails to be monotone: pointwise `n`-convergence in the OFE sense
need not preserve the order, so the limit of a chain of order-preserving maps need not be
order-preserving. Obtaining `IsCOFE (α →o β)` requires additional hypotheses (e.g. order
continuity of `β`'s `IsCOFE.compl`), and is not pursued here.

## Connecting back to `β`

We provide:

* `NonExpansive (fun f : α →o β ↦ f x)` — evaluation at a fixed `x : α`;
* `evalHom x : (α →o β) -n> β` — the same as a non-expansive Hom.
-/

namespace IrisMath.OrderHom

variable {α : Type*} {β : Type*} [Preorder α] [Preorder β]

/-- The Iris `OFE` structure on `α →o β`, inherited pointwise from `β`.

`f ≡ g` means `∀ x, f x ≡ g x`, and `f ≡{n}≡ g` means `∀ x, f x ≡{n}≡ g x`. -/
instance instOFE [OFE β] : OFE (α →o β) where
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

@[simp] theorem equiv_def {f g : α →o β} : f ≡ g ↔ ∀ x, f x ≡ g x := Iff.rfl

@[simp] theorem dist_def {n : Nat} {f g : α →o β} : f ≡{n}≡ g ↔ ∀ x, f x ≡{n}≡ g x := Iff.rfl

/-- Evaluation `f ↦ f x : (α →o β) → β` at a fixed point `x : α` is non-expansive. -/
instance eval_ne (x : α) : NonExpansive (fun (f : α →o β) ↦ f x) where
  ne _ _ _ h := h x

/-- Two order-preserving maps that are equivalent in `α →o β` are equivalent pointwise. -/
theorem Equiv.apply {f g : α →o β} (h : f ≡ g) (x : α) : f x ≡ g x := h x

/-- Two order-preserving maps that are `n`-equivalent in `α →o β` are `n`-equivalent
pointwise. -/
theorem Dist.apply {n : Nat} {f g : α →o β} (h : f ≡{n}≡ g) (x : α) : f x ≡{n}≡ g x := h x

/-- Evaluation at `x : α` packaged as a non-expansive Hom `(α →o β) -n> β`. -/
def evalHom (x : α) : (α →o β) -n> β where
  f g := g x
  ne := eval_ne x

@[simp] theorem evalHom_apply (x : α) (f : α →o β) : evalHom x f = f x := rfl

end

/-! ### Leibniz transfer

If `β` is `Leibniz` (i.e. its OFE equivalence coincides with `=`), then so is `α →o β`,
since extensionality for order-preserving maps is precisely pointwise equality. -/

instance instLeibniz [OFE β] [Leibniz β] : Leibniz (α →o β) where
  eq_of_eqv h := _root_.OrderHom.ext _ _ <| funext fun x ↦ Leibniz.eq_of_eqv (h x)

end IrisMath.OrderHom
