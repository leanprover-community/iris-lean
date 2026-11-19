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

variable {SI : Type _} [SIdx SI]
local stepindex SI

/-! Tests for `OFE.ne_of_discrete`: every function out of a discrete OFE is non-expansive. -/

section ne_of_discrete

variable {α β : Type _} [OFEᵢ α] [Discreteᵢ α] [OFEᵢ β]

example (f : α → β) : NonExpansiveᵢ f := inferInstance

example (g : α → β) : NonExpansiveᵢ (fun x : α => g x) := inferInstance

example (f : Unit → β) : NonExpansiveᵢ f := inferInstance

example (f : Empty → β) : NonExpansiveᵢ f := inferInstance

example (f : Option α → β) : NonExpansiveᵢ f := inferInstance

variable {γ : Type _} [OFEᵢ γ] [Discreteᵢ γ]

example (f : α × γ → β) : NonExpansiveᵢ f := inferInstance

example (f : α ⊕ γ → β) : NonExpansiveᵢ f := inferInstance

example (P : α → Prop) (f : Subtype P → β) : NonExpansiveᵢ f := inferInstance

example (f : α → β) {n : SI} {x y : α} (h : x ≡{n}≡ y) : f x ≡{n}≡ f y :=
  NonExpansive.ne h

example (f : α → β) : α -n> β := ⟨f, inferInstance⟩

end ne_of_discrete

section dist_notation

variable {α : Type _} [OFEᵢ α] (x y : α) (n : SI)

/-- info: x ≡{n}≡ y : Prop -/
#guard_msgs in
#check x ≡{n}≡ y

end dist_notation

end IrisTest
