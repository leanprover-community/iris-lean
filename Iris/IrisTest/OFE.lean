/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang
-/
module

public import Iris.Algebra.OFE

@[expose] public section

namespace IrisTest
open Iris OFE

/-! Tests for `OFE.ne_of_discrete`: every function out of a discrete OFE is non-expansive. -/

section ne_of_discrete

variable {α γ β : Type _} [OFE β]

/-- The basic case: an arbitrary function out of `DiscreteO α`. -/
example (f : DiscreteO α → β) : NonExpansive f := inferInstance

/-- Functions written as lambdas. -/
example (g : α → β) : NonExpansive (fun x : DiscreteO α => g x.car) := inferInstance

example (f : Unit → β) : NonExpansive f := inferInstance

example (f : Empty → β) : NonExpansive f := inferInstance

example (f : Option (DiscreteO α) → β) : NonExpansive f := inferInstance

example (f : DiscreteO α × DiscreteO γ → β) : NonExpansive f := inferInstance

example (f : DiscreteO α ⊕ DiscreteO γ → β) : NonExpansive f := inferInstance

example (P : DiscreteO α → Prop) (f : Subtype P → β) : NonExpansive f := inferInstance

example (f : DiscreteO α → β) {n : Nat} {x y : DiscreteO α} (h : x ≡{n}≡ y) :
    f x ≡{n}≡ f y :=
  NonExpansive.ne h

example (f : DiscreteO α → β) : DiscreteO α -n> β := ⟨f, inferInstance⟩

end ne_of_discrete

end IrisTest
