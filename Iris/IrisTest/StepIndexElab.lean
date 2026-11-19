/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.StepIndex
public meta import Iris.Std.StepIndex.Elab

@[expose] public section

namespace IrisTest.StepIndexElab
open Iris

/-- An explicit step index. -/
@[indexed] class Foo (SI : stepindex (Type _)) [SIdx SI] (α : Type _) where
  foo : α → SI → Prop

/-- An implicit step index that nothing else determines. -/
@[indexed] def Bar {SI : stepindex (Type _)} [SIdx SI] (α : Type _) : Type _ := α → SI

namespace A
@[indexed] def Baz {SI : stepindex (Type _)} [SIdx SI] (n : SI) : SI := n
end A

namespace B
def Baz (b : Bool) : Bool := b
end B

-- a notation passes the step index itself: its expansion is not re-read as a token
notation "bar% " α => Bar (SI := stepindex%) α

section
variable {SI : stepindex Type} [SIdx SI]
local stepindex SI

/-- info: SI -/
#guard_msgs in
#stepindex?

/-- info: fun α [Fooᵢ α] => 0 : (α : Type) → [Fooᵢ α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Fooᵢ α] => 0

-- the declaration itself takes the step index as usual, and prints with the notation
/-- info: fun α [Fooᵢ α] => 0 : (α : Type) → [Fooᵢ α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Foo SI α] => 0
/-- info: fun α [Fooᵢ α] => 0 : (α : Type) → [Fooᵢ α] → Nat -/
#guard_msgs in
#check fun (α : Type) [@Foo SI _ α] => 0

-- a bare token
example : (Fooᵢ : Type → Type) = @Foo SI _ := rfl

-- an implicit step index
example (α : Type) : Barᵢ α = (α → SI) := rfl

-- explicit universes
example (α : Type) : Barᵢ.{0} α = (α → SI) := rfl

-- through a notation
example (α : Type) : (bar% α) = (α → SI) := rfl

-- a non-type is spelled only by its qualified name
example (n : SI) : IrisTest.StepIndexElab.A.Bazᵢ n = n := rfl
example (n : SI) : A.Baz n = n := rfl
open A B in
example : Baz true = true := rfl
end

-- outside a `local stepindex` section, the step index is written as usual
example {SI : Type} [SIdx SI] (α : Type) [Foo SI α] : Bar (SI := SI) α = (α → SI) := rfl

end IrisTest.StepIndexElab
