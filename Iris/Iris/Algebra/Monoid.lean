/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.StepIndexFinite
meta import Iris.Std.RocqPorting

public section

namespace Iris.Algebra

/-! # Monoids for Big Operators

- `Monoid` contains the laws and requires an OFE structure.
- Uses explicit `op` parameters to support multiple monoids on the same type.
-/

open OFE

local stepindex Nat

/-- A commutative monoid on an OFE, used for big operators.
The operation must be non-expansive, associative, commutative, and have a left identity. -/
@[rocq_alias Monoid]
class MonoidOps {M : Type u} [OFE M] (op : M → M → M) (unit : outParam M) where
  /-- The operation is non-expansive in both arguments -/
  op_ne : NonExpansive₂ op
  /-- Associativity -/
  op_assoc : ∀ {a b c : M}, op (op a b) c = op a (op b c)
  /-- Commutativity -/
  op_comm : ∀ {a b : M}, op a b = op b a
  /-- Left identity -/
  op_left_id : ∀ {a : M}, op unit a = a

#rocq_ignore MonoidOps "Not needed"
#rocq_ignore monoid_ops "Not needed"

namespace MonoidOps

attribute [instance] op_ne

variable {M : Type u} [OFE M] {unit : M} {op : M → M → M}

#rocq_ignore monoid_proper "OFE is Leibniz; use equality"

/-- Right identity follows from commutativity and left identity. -/
@[rocq_alias monoid_right_id]
theorem op_right_id [MonoidOps op unit] : op a unit = a :=
  op_comm.trans op_left_id

/-- Rearrange `(a * b) * (c * d)` to `(a * c) * (b * d)`. -/
theorem op_op_op_comm [MonoidOps op unit] {a b c d : M} :
    op (op a b) (op c d) = op (op a c) (op b d) :=
  calc op (op a b) (op c d)
      _ = op a (op b (op c d)) := op_assoc
      _ = op a (op (op b c) d) := congrArg (op a) op_assoc.symm
      _ = op a (op (op c b) d) := congrArg (op a) (congrArg (op · d) op_comm)
      _ = op a (op c (op b d)) := congrArg (op a) op_assoc
      _ = op (op a c) (op b d) := op_assoc.symm

/-- Swap inner elements: `a * (b * c)` to `b * (a * c)`. -/
theorem op_left_comm [MonoidOps op unit] {a b c : M} :
    op a (op b c) = op b (op a c) :=
  calc op a (op b c)
      _ = op (op a b) c := op_assoc.symm
      _ = op (op b a) c := congrArg (op · c) op_comm
      _ = op b (op a c) := op_assoc

/-- Non-expansiveness for dist. -/
theorem op_dist [MonoidOps op unit] (ha : a ≡{n}≡ a') (hb : b ≡{n}≡ b') :
    op a b ≡{n}≡ op a' b' := NonExpansive₂.ne ha hb

end MonoidOps

/-! ## Monoid Homomorphisms -/

/-- A weak monoid homomorphism preserves the operation but not necessarily the unit. -/
@[rocq_alias WeakMonoidHomomorphism]
class WeakMonoidHomomorphism {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
    (op₁ : M₁ → M₁ → M₁) (op₂ : M₂ → M₂ → M₂) (unit₁ : M₁) (unit₂ : M₂)
    [MonoidOps op₁ unit₁] [MonoidOps op₂ unit₂]
    (R : M₂ → M₂ → Prop) (f : M₁ → M₂) where
  /-- The relation is reflexive -/
  rel_refl : ∀ {a : M₂}, R a a
  /-- The relation is transitive -/
  rel_trans : ∀ {a b c : M₂}, R a b → R b c → R a c
  /-- The operation is proper with respect to R -/
  op_proper : ∀ {a a' b b' : M₂}, R a a' → R b b' → R (op₂ a b) (op₂ a' b')
  /-- The function is non-expansive -/
  map_ne : NonExpansive f
  /-- The homomorphism property -/
  map_op : ∀ {x y}, R (f (op₁ x y)) (op₂ (f x) (f y))

#rocq_ignore weak_monoid_homomorphism_proper "OFE is Leibniz; use equality"

/-- A monoid homomorphism preserves both the operation and the unit. -/
@[rocq_alias MonoidHomomorphism]
class MonoidHomomorphism {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
    (op₁ : M₁ → M₁ → M₁) (op₂ : M₂ → M₂ → M₂) (unit₁ : M₁) (unit₂ : M₂)
    [MonoidOps op₁ unit₁] [MonoidOps op₂ unit₂]
    (R : M₂ → M₂ → Prop) (f : M₁ → M₂)
    extends WeakMonoidHomomorphism op₁ op₂ unit₁ unit₂ R f where
  /-- The unit is preserved -/
  map_unit : R (f unit₁) unit₂

end Iris.Algebra
