/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Algebra.OFE

namespace Iris.Algebra

/-! # Monoids for Big Operators

- `Monoid` contains the laws and requires an OFE structure
- Use explicit `op` and `unit` parameters to support multiple monoids on the same type
-/

open OFE

/-- A commutative monoid on an OFE, used for big operators.
The operation must be non-expansive, associative, commutative, and have a left identity. -/
class Monoid (M : Type u) [OFE M] (op : M → M → M) (unit : outParam M) where
  /-- The operation is non-expansive in both arguments -/
  op_ne : NonExpansive₂ op
  /-- Associativity up to equivalence -/
  op_assoc : ∀ a b c : M, op (op a b) c ≡ op a (op b c)
  /-- Commutativity up to equivalence -/
  op_comm : ∀ a b : M, op a b ≡ op b a
  /-- Left identity up to equivalence -/
  op_left_id : ∀ a : M, op unit a ≡ a

namespace Monoid

attribute [simp] op_left_id

variable {M : Type u} [OFE M] {op : M → M → M}

/-- The operation is proper with respect to equivalence. -/
theorem op_proper {unit : M} [Monoid M op unit] {a a' b b' : M}
    (ha : a ≡ a') (hb : b ≡ b') : op a b ≡ op a' b' := by
  haveI : NonExpansive₂ op := op_ne
  exact NonExpansive₂.eqv ha hb

/-- Right identity follows from commutativity and left identity. -/
@[simp] theorem op_right_id {unit : M} [Monoid M op unit] (a : M) : op a unit ≡ a :=
  Equiv.trans (op_comm (unit := unit) a unit) (op_left_id a)

/-- Congruence on the left argument. -/
theorem op_congr_l {unit : M} [Monoid M op unit] {a a' b : M} (h : a ≡ a') : op a b ≡ op a' b :=
  op_proper (unit := unit) h Equiv.rfl

/-- Congruence on the right argument. -/
theorem op_congr_r {unit : M} [Monoid M op unit] {a b b' : M} (h : b ≡ b') : op a b ≡ op a b' :=
  op_proper (unit := unit) Equiv.rfl h

/-- Rearrange `(a * b) * (c * d)` to `(a * c) * (b * d)`. -/
theorem op_op_swap {unit : M} [Monoid M op unit] {a b c d : M} :
    op (op a b) (op c d) ≡ op (op a c) (op b d) :=
  calc op (op a b) (op c d)
      _ ≡ op a (op b (op c d)) := op_assoc a b (op c d)
      _ ≡ op a (op (op b c) d) := op_congr_r (Equiv.symm (op_assoc b c d))
      _ ≡ op a (op (op c b) d) := op_congr_r (op_congr_l (op_comm b c))
      _ ≡ op a (op c (op b d)) := op_congr_r (op_assoc c b d)
      _ ≡ op (op a c) (op b d) := Equiv.symm (op_assoc a c (op b d))

/-- Swap inner elements: `a * (b * c)` to `b * (a * c)`. -/
theorem op_swap_inner {unit : M} [Monoid M op unit] {a b c : M} :
    op a (op b c) ≡ op b (op a c) :=
  calc op a (op b c)
      _ ≡ op (op a b) c := Equiv.symm (op_assoc a b c)
      _ ≡ op (op b a) c := op_congr_l (op_comm a b)
      _ ≡ op b (op a c) := op_assoc b a c

/-- Non-expansiveness for dist. -/
theorem op_ne_dist {unit : M} [Monoid M op unit] {n : Nat} {a a' b b' : M}
    (ha : a ≡{n}≡ a') (hb : b ≡{n}≡ b') : op a b ≡{n}≡ op a' b' := by
  haveI : NonExpansive₂ op := op_ne
  exact NonExpansive₂.ne ha hb

end Monoid

/-! ## Monoid Homomorphisms -/

/-- A weak monoid homomorphism preserves the operation but not necessarily the unit. -/
class WeakMonoidHomomorphism {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
    (op₁ : M₁ → M₁ → M₁) (op₂ : M₂ → M₂ → M₂) (unit₁ : M₁) (unit₂ : M₂)
    [Monoid M₁ op₁ unit₁] [Monoid M₂ op₂ unit₂]
    (R : M₂ → M₂ → Prop) (f : M₁ → M₂) where
  /-- The relation is reflexive -/
  rel_refl : ∀ a : M₂, R a a
  /-- The relation is transitive -/
  rel_trans : ∀ {a b c : M₂}, R a b → R b c → R a c
  /-- The relation is proper with respect to equivalence -/
  rel_proper : ∀ {a a' b b' : M₂}, a ≡ a' → b ≡ b' → (R a b ↔ R a' b')
  /-- The operation is proper with respect to R -/
  op_proper : ∀ {a a' b b' : M₂}, R a a' → R b b' → R (op₂ a b) (op₂ a' b')
  /-- The function is non-expansive -/
  f_ne : NonExpansive f
  /-- The homomorphism property -/
  homomorphism : ∀ x y, R (f (op₁ x y)) (op₂ (f x) (f y))

/-- A monoid homomorphism preserves both the operation and the unit. -/
class MonoidHomomorphism {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
    (op₁ : M₁ → M₁ → M₁) (op₂ : M₂ → M₂ → M₂) (unit₁ : M₁) (unit₂ : M₂)
    [Monoid M₁ op₁ unit₁] [Monoid M₂ op₂ unit₂]
    (R : M₂ → M₂ → Prop) (f : M₁ → M₂)
    extends WeakMonoidHomomorphism op₁ op₂ unit₁ unit₂ R f where
  /-- The unit is preserved -/
  map_unit : R (f unit₁) unit₂

end Iris.Algebra
