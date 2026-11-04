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

variable {α β : Type _} [OFE α] [Discrete α] [OFE β]

example (f : α → β) : NonExpansive f := inferInstance

example (g : α → β) : NonExpansive (fun x : α => g x) := inferInstance

example (f : Unit → β) : NonExpansive f := inferInstance

example (f : Empty → β) : NonExpansive f := inferInstance

example (f : Option α → β) : NonExpansive f := inferInstance

variable {γ : Type _} [OFE γ] [Discrete γ]

example (f : α × γ → β) : NonExpansive f := inferInstance

example (f : α ⊕ γ → β) : NonExpansive f := inferInstance

example (P : α → Prop) (f : Subtype P → β) : NonExpansive f := inferInstance

example (f : α → β) {n : Nat} {x y : α} (h : x ≡{n}≡ y) : f x ≡{n}≡ f y :=
  NonExpansive.ne h

example (f : α → β) : α -n> β := ⟨f, inferInstance⟩

end ne_of_discrete

end IrisTest
