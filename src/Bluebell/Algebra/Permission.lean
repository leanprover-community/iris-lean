import Mathlib.Tactic.TypeStar
import Iris.Algebra.DFrac

namespace Bluebell

open Iris

/-- Permissions as pointwise `DFrac F` over variables of type `α`.
Requires a `UFraction F` instance so that `DFrac F` is a CMRA.
This inherits CMRA/UCMRA structure from function instances. -/
abbrev Permission (α F : Type*) [UFraction F] := α → DFrac F

namespace Permission

variable {α F : Type*} [UFraction F]

/-- Construct permissions from a bounded map `p : α → Frac F` that is ≤ 1 pointwise.
This is a convenience wrapper around `DFrac.own` with a proof that the fraction is proper. -/
def ofFrac (p : α → Frac F)
    (_hp : ∀ a, Fraction.Proper (p a : F)) : Permission α F :=
  fun a => by
    -- `hp a` witnesses properness; we ignore it here since `own` just holds the value.
    exact DFrac.own (p a : F)

end Permission

/-
Old stuff:

/-! ## Permissions -/

/-- A permission on type `α` is a map from `α` to the non-negative rationals `ℚ≥0`.

We need to have the `Multiplicative` tag in order to specify that multiplication is pointwise
addition, and unit is the constant zero map. -/
@[reducible] def Permission (α : Type*) := Multiplicative (α → ℚ≥0)

variable {α : Type*}

instance : Preorder (Permission α) := inferInstanceAs (Preorder (Multiplicative (α → ℚ≥0)))
instance : MulOneClass (Permission α) := inferInstanceAs (MulOneClass (Multiplicative (α → ℚ≥0)))
instance : MulLeftMono (Permission α) := inferInstanceAs (MulLeftMono (Multiplicative (α → ℚ≥0)))

-- /-- Permissions form an `OrderedUnitalResourceAlgebra` where `≤` is defined pointwise, a resource is valid iff it's below `1` pointwise, and composition is pointwise multiplication -/
-- instance : OrderedUnitalResourceAlgebra (Permission α) where
--   valid := fun p => p ≤ 1
--   valid_one := by simp
--   valid_mul := by intro a b hab; simp_all only [le_one_iff_eq_one, LeftCancelMonoid.mul_eq_one,
--     le_refl]
--   valid_mono := by intro a b h h'; simp_all only [le_one_iff_eq_one]
--   -- mul_right_mono := by intro a b c h i; sorry

-/

end Bluebell
