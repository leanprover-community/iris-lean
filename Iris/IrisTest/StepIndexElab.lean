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
@[indexed] def Baz {SI : stepindex (Type _)} [SIdx SI] (_ : SI) : Prop := True
end A

namespace B
def Baz (_ : Bool) : Prop := True
end B

notation "bar% " α => Bar α

section
variable {SI : stepindex Type} [SIdx SI]
local stepindex SI

/-- info: SI -/
#guard_msgs in
#stepindex?

/-- info: fun α [Foo α] => 0 : (α : Type) → [Foo α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Foo α] => 0

-- the step index given by name, or with `@`
/-- info: fun α [Foo α] => 0 : (α : Type) → [Foo α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Foo (SI := SI) α] => 0
/-- info: fun α [Foo α] => 0 : (α : Type) → [Foo α] → Nat -/
#guard_msgs in
#check fun (α : Type) [@Foo SI _ α] => 0

-- a partial application, and a bare constant
example : (Foo : Type → Type) = @Foo SI _ := rfl

-- an implicit step index
example (α : Type) : Bar α = (α → SI) := rfl

-- through a notation
example (α : Type) : (bar% α) = (α → SI) := rfl

-- an overloaded name: only `A.Baz` takes a step index
open A B in
example (n : SI) : Baz n := trivial
open A B in
example : Baz true := trivial
end

-- outside a `local stepindex` section, the step index is written as usual
example {SI : Type} [SIdx SI] (α : Type) [Foo SI α] : Bar (SI := SI) α = (α → SI) := rfl

end IrisTest.StepIndexElab
