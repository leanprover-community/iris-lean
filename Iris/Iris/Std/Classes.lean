/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

@[expose] public section

namespace Iris.Std

/-- Represents a binary relation with two arguments of the same type `α`. -/
abbrev Relation (α : Type _) := α → α → Prop

/-- Require that a type `α` has a distinguished top element. -/
class Top (α : Type u) where
  top : α
export Top (top)

notation "⊤" => top

/-- Require that a relation `R` on `a` is reflexive. -/
class Reflexive (R : Relation α) where
  refl {x : α} : R x x
export Reflexive (refl)

/-- Require that a relation `R` on `α` is transitive. -/
class Transitive (R : Relation α) where
  trans {x y z : α} : R x y → R y z → R x z
export Transitive (trans)

/-- Require that a relation `R` on `α` is a preorder, i.e. that it is reflexive and transitive. -/
class Preorder (R : Relation α) extends Reflexive R, Transitive R


/-- Require that a binary function `f` on `α` is idempotent in a relation `R` on `α`. -/
class Idempotent (R : Relation α) (f : α → α → α) where
  idem {x : α} : R (f x x) x
export Idempotent (idem)

/-- Require that a binary function `f` from `β` to `α` is commutative in a relation `R` on `α`. -/
class Commutative (R : Relation α) (f : β → β → α) where
  comm {x y : β} : R (f x y) (f y x)
export Commutative (comm)

/-- Require that an element `i` of `α` is the left unit of a binary function `f` on `α` in a
relation `R` on `α`. -/
class LeftId (R : Relation α) (i : α) (f : α → α → α) where
  left_id {x : α} : R (f i x) x
export LeftId (left_id)

/-- Require that an element `i` of `α` is the right unit of a binary function `f` on `α` in a
relation `R` on `α`. -/
class RightId (R : Relation α) (i : α) (f : α → α → α) where
  right_id {x : α} : R (f x i) x
export RightId (right_id)

class LeftAbsorb (R : Relation α) (i : α) (f : α → α → α) where
  left_absorb {x : α} : R (f i x) i
export LeftAbsorb (left_absorb)

class RightAbsorb (R : Relation α) (i : α) (f : α → α → α) where
  right_absorb {x : α} : R (f x i) i
export RightAbsorb (right_absorb)

/-- Require that a binary function `f` on `α` is associative in a relation `R` on `α`. -/
class Associative (R : Relation α) (f : α → α → α) where
  assoc {x y z : α} : R (f (f x y) z) (f x (f y z))
export Associative (assoc)

/-- Require that a relation `S` on `α` is antisymmetrical with `R` as its equivalence relation. -/
class Antisymmetric (R : Relation α) (S : outParam <| Relation α) where
  antisymm {x y : α} : (left : S x y) → (right : S y x) → R x y
export Antisymmetric (antisymm)

class Disjoint (α : Type u) where
  disjoint : α -> α -> Prop
export Disjoint (disjoint)
infix:50 " ## " => Disjoint.disjoint

end Iris.Std
