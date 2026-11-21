/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.StepIndexFinite
public import Iris.Algebra.OFE
public meta import Iris.Std.StepIndex.Elab

@[expose] public section

namespace IrisTest.StepIndexElab
open Iris

/-- A class over a step index. -/
class Foo (SI : Type _) [SIdx SI] (α : Type _) where
  foo : α → SI → Prop

/-- An implicit step index that nothing else determines. -/
def Bar {SI : Type _} [SIdx SI] (α : Type _) : Type _ := α → SI

namespace A
def Baz {SI : Type _} [SIdx SI] (_ : SI) : Prop := True
end A

namespace B
def Baz (_ : Bool) : Prop := True
end B

notation "bar% " α => Bar α

/-- An `@[indexed SI]` function whose step index comes after an explicit argument. -/
@[indexed SI] def SIFn (_ : Nat) {SI : Type} [SIdx SI] : Type := SI

/-- An `@[indexed SI]` def without an `SIdx` argument. -/
@[indexed SI] def Plain {SI : Type} (α : Type) : Type := α → SI

/-- An `@[indexed SI]` class. -/
@[indexed SI] class Qux {SI : Type _} [SIdx SI] (α : Type _) where
  qux : α → SI → Prop

section
variable {SI : Type} [SIdx SI]
local stepindex SI

/-- info: SI -/
#guard_msgs in
#stepindex?

/-- info: fun α [Foo SI α] => 0 : (α : Type) → [Foo SI α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Foo _ α] => 0

-- the step index given by name, or with `@`
/-- info: fun α [Foo SI α] => 0 : (α : Type) → [Foo SI α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Foo (SI := SI) α] => 0
/-- info: fun α [Foo SI α] => 0 : (α : Type) → [Foo SI α] → Nat -/
#guard_msgs in
#check fun (α : Type) [@Foo SI _ α] => 0

-- a partial application, and a bare constant
example : (Foo SI : Type → Type) = @Foo SI _ := rfl

-- an implicit step index
example (α : Type) : Bar α = (α → SI) := rfl

-- through a notation
example (α : Type) : (bar% α) = (α → SI) := rfl

-- an overloaded name: only `A.Baz` takes a step index
open A B in
example (n : SI) : Baz n := trivial
open A B in
example : Baz true := trivial

-- the section's step index is filled in and hidden; any other one is shown
/-- info: fun α [Qux α] => 0 : (α : Type) → [Qux α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Qux α] => 0
/-- info: fun α [Qux (SI := Nat) α] => 0 : (α : Type) → [Qux (SI := Nat) α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Qux (SI := Nat) α] => 0

-- the index of a bare constant, a nested application, and an imported class
/-- info: Qux (SI := Nat) : Type → Type -/
#guard_msgs in
#check (Qux (SI := Nat) : Type → Type)
/-- info: fun α [Qux (SI := Nat) (List α)] => 0 : (α : Type) → [Qux (SI := Nat) (List α)] → Nat -/
#guard_msgs in
#check fun (α : Type) [Qux (SI := Nat) (List α)] => 0
/-- info: fun α [OFE (SI := Nat) α] [OFE α] => 0 : (α : Type) → [OFE (SI := Nat) α] → [OFE α] → Nat -/
#guard_msgs in
#check fun (α : Type) [OFE (SI := Nat) α] [OFE α] => 0

-- the step index comes after an explicit argument
/-- info: fun n => SIFn n : Nat → Type -/
#guard_msgs in
#check fun (n : Nat) => SIFn n
/-- info: fun n => SIFn n (SI := Nat) : Nat → Type -/
#guard_msgs in
#check fun (n : Nat) => SIFn (SI := Nat) n

-- `pp.explicit` prints every argument
set_option pp.explicit true in
/--
info: fun α [@Qux Nat natSIdx α] [@Qux SI inst✝ α] =>
  @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) : (α : Type) → [@Qux Nat natSIdx α] → [@Qux SI inst✝ α] → Nat
-/
#guard_msgs in
#check fun (α : Type) [Qux (SI := Nat) α] [Qux α] => 0

-- the index is shown under other printing options
set_option pp.notation false in
/-- info: fun α [Qux (SI := Nat) α] => 0 : (α : Type) → [Qux (SI := Nat) α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Qux (SI := Nat) α] => 0
set_option pp.analyze true in
/-- info: fun α [Qux (SI := Nat) α] => 0 : (α : Type) → [Qux (SI := Nat) α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Qux (SI := Nat) α] => 0
set_option pp.universes true in
/-- info: fun α [Qux.{0, 0} (SI := Nat) α] => 0 : (α : Type) → [Qux.{0, 0} (SI := Nat) α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Qux (SI := Nat) α] => 0
end

-- outside a `local stepindex` section, the printer does nothing
/-- info: fun α [Qux α] => 0 : (α : Type) → [Qux α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Qux (SI := Nat) α] => 0

section
local stepindex Nat
local notation "ℕ" => Nat

-- the step index is compared as a term, not by how it prints
/-- info: fun α [Qux α] => 0 : (α : Type) → [Qux α] → ℕ -/
#guard_msgs in
#check fun (α : Type) [Qux α] => 0
end

-- outside a `local stepindex` section, the step index is written as usual
example {SI : Type} [SIdx SI] (α : Type) [Foo (SI := SI) α] : Bar (SI := SI) α = (α → SI) := rfl

-- the step index is resolved once, by `local stepindex`, and is not captured by later names
section
variable {SI : Type} [SIdx SI]
local stepindex SI

-- a local binder named `SI` does not capture the section's step index
def shadow := fun (SI : Nat) (α : Type) [OFE α] => SI

-- an `@[indexed]` constant without an `SIdx` argument
example (α : Type) [HasDist α] (x : α) (n : SI) : HasDist.dist n x x = HasDist.dist n x x := rfl
example (α : Type) : Plain α = (α → SI) := rfl

-- the marker of `fillStepIndex` is not a user-visible hole
/-- info: fun α => (Foo SI α, ?_iris_stepindex_examined) : Type → Type × Nat -/
#guard_msgs in
#check fun (α : Type) => (Foo _ α, (?_iris_stepindex_examined : Nat))

#guard_msgs (substring := true) in
theorem noSI : True := by
  have : ∀ (α : Type) [OFE α], True := fun _ _ => trivial
  trivial

theorem natSI {α : Type} [OFE (SI := Nat) α] (x y : α) (h : x ≡{(3 : Nat)}≡ y) :
    x ≡{(3 : Nat)}≡ y := (OFE.Dist.rfl).trans h

/-- info: fun n => n : SI → SI -/
#guard_msgs in
#check fun (n : stepindex%) => n

/-- error: the section step index `SI` is not in scope here; mention it in the statement or `include SI` -/
#guard_msgs in
theorem noSI' : True := by
  have _ : Type := stepindex%
  trivial
end

example : (fun (n : stepindex%) => n) true = true := rfl

universe u
def PIdx : Type := (fun (_ : Sort u) => Nat) PUnit.{u}
instance : SIdx PIdx.{u} := inferInstanceAs (SIdx Nat)

section
local stepindex PIdx
/-- info: fun α [Qux α] => 0 : (α : Type) → [Qux α] → Nat -/
#guard_msgs in
#check fun (α : Type) [Qux α] => 0
end

abbrev MySI := Nat
namespace Inner
abbrev MySI := Bool
end Inner

section
local stepindex MySI
namespace Inner
-- a namespace constant named `MySI` does not capture the section's step index
example (α : Type) [OFE α] (x : α) : x ≡{(3 : Nat)}≡ x := OFE.Dist.rfl
end Inner
end

-- `@[indexed]` rejects binders it cannot fill
/--
error: `@[indexed]`: the step index `SI` of `IrisTest.StepIndexElab.NotType` must be a type, but it has type
  Nat
-/
#guard_msgs in
@[indexed SI] class NotType {SI : Nat} (α : Type) where
  x : α

/--
error: `@[indexed]`: the step index `SI` of `IrisTest.StepIndexElab.InstBinder` must be implicit, a `local stepindex` section can only fill in an implicit argument
-/
#guard_msgs in
@[indexed SI] class InstBinder [SI : Inhabited Nat] (α : Type) where
  x : α

-- a declaration takes one step index
@[indexed SI] class Twice {SI : Type} [SIdx SI] {SJ : Type} [SIdx SJ] (α : Type) where
  x : α → SI × SJ
/-- error: `@[indexed]`: `IrisTest.StepIndexElab.Twice` already has the step index `SI` -/
#guard_msgs in
attribute [indexed SJ] Twice

end IrisTest.StepIndexElab
