/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
namespace Iris.Std

/-- Represents a binary relation with two arguments of the same type `α`. -/
abbrev Relation (α : Type) := α → α → Prop


/-- Require that a relation `R` on `a` is reflexive. -/
class Reflexive (R : Relation α) where
  reflexivity {x : α} : R x x
export Reflexive (reflexivity)
attribute [simp] reflexivity

/-- Require that a relation `R` on `α` is transitive. -/
class Transitive (R : Relation α) where
  transitivity {x y z : α} : R x y → R y z → R x z
export Transitive (transitivity)

/-- Require that a relation `R` on `α` is a preorder, i.e. that it is reflexive and transitive. -/
class PreOrder (R : Relation α) extends Reflexive R, Transitive R


/-- Require that a binary function `f` on `α` is idemotent in a relation `R` on `α`. -/
class Idemp (R : Relation α) (f : α → α → α) : Prop where
  idem {x : α} : R (f x x) x
export Idemp (idem)

/-- Require that a binary function `f` from `β` to `α` is commutative in a relation `R` on `α`. -/
class Comm (R : Relation α) (f : β → β → α) : Prop where
  comm {x y : β} : R (f x y) (f y x)
export Comm (comm)

/-- Require that an element `i` of `α` is the left unit of a binary function `f` on `α` in a relation `R` on `α`. -/
class LeftId (R : Relation α) (i : α) (f : α → α → α) : Prop where
  left_id {x : α} : R (f i x) x
export LeftId (left_id)

/-- Require that an element `i` of `α` is the right unit of a binary function `f` on `α` in a relation `R` on `α`. -/
class RightId (R : Relation α) (i : α) (f : α → α → α) : Prop where
  right_id {x : α} : R (f x i) x
export RightId (right_id)

/-- Require that a binary function `f` on `α` is associative in a relation `R` on `α`. -/
class Assoc (R : Relation α) (f : α → α → α) : Prop where
  assoc {x y z : α} : R (f x (f y z)) (f (f x y) z)
export Assoc (assoc)

/-- Require that a relation `S` on `α` is antisymmetrical with `R` as its equivalence relation. -/
class AntiSymm (R : Relation α) (S : outParam <| Relation α) : Prop where
  anti_symm {x y : α} : (left : S x y) → (right : S y x) → R x y
export AntiSymm (anti_symm)

end Iris.Std
