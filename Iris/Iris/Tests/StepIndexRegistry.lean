/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Iris.Algebra.StepIndexRegistry

@[expose] public section

namespace Iris.Tests

/-- info: [anonymous] -/
#guard_msgs in
#stepindex?

/-- error: infer_stepindex: no step index in scope; declare one with `local stepindex T` -/
#guard_msgs in
example : Type := by infer_stepindex

-- Test the error from `stepindex%` when no index is declared

/-- error: stepindex%: no step index in scope; declare one with `local stepindex T` -/
#guard_msgs in
#check (stepindex% : Type)

local stepindex Nat

/-- info: Nat -/
#guard_msgs in
#stepindex?

-- Test that `stepindex%` resolves eagerly to a global constant

/-- info: Nat : Type -/
#guard_msgs in
#check (stepindex% : Type)

/-- info: Nat : Type -/
#guard_msgs in
#check (by infer_stepindex : Type)

section
variable {SI : Type}
local stepindex SI

/-- info: SI -/
#guard_msgs in
#stepindex?

/-- info: SI : Type -/
#guard_msgs in
#check (by infer_stepindex : Type)

-- Test that `stepindex%` also resolves to a section variable

/-- info: SI : Type -/
#guard_msgs in
#check (stepindex% : Type)

def sectionIndex : Type := by infer_stepindex

/-- info: @sectionIndex : {SI : Type} → Type -/
#guard_msgs in
#check @sectionIndex

end

/-- info: Nat -/
#guard_msgs in
#stepindex?

namespace ScopedTest
scoped stepindex Unit
end ScopedTest

/-- info: Nat -/
#guard_msgs in
#stepindex?

/-- info: Unit -/
#guard_msgs in
open ScopedTest in
#stepindex?

/-- error: stepindex must be either `scoped` or `local`. -/
#guard_msgs in
stepindex Nat

/-- info: Nat -/
#guard_msgs in
#stepindex?

class Pointwise {α β : Type} (f : α → β) (SI : Type := by infer_stepindex) where
  ok : SI → True

instance instAmbient (f : Nat → Nat) : Pointwise f := ⟨fun _ => trivial⟩

/-- info: instAmbient : ∀ (f : Nat → Nat), Pointwise f Nat -/
#guard_msgs in
#check @instAmbient

instance instOverride (f : Nat → Nat) : Pointwise f (SI := Unit) := ⟨fun _ => trivial⟩

-- Test that we can explicitly override the step index type in a class instance

/-- info: instOverride : ∀ (f : Nat → Nat), Pointwise f Unit -/
#guard_msgs in
#check @instOverride

theorem binderPosition (f : Nat → Nat) [Pointwise f] : True := trivial

-- Test that the auto_param will correctly infer the current step index type in a class instance

/-- info: binderPosition : ∀ (f : Nat → Nat) [Pointwise f Nat], True -/
#guard_msgs in
#check @binderPosition

structure Bundle (α : Type) (SI : Type := by infer_stepindex) where
  car : SI → α

def natBundle : Bundle Nat := ⟨fun n => n⟩

/-- info: Iris.Tests.natBundle : Bundle Nat Nat -/
#guard_msgs in
#check natBundle

section
variable {SI α : Type}
local stepindex SI

instance instSection (f : α → α) : Pointwise f := ⟨fun _ => trivial⟩

-- Test that local overrides also work for the step index type

/-- info: @instSection : ∀ {SI α : Type} (f : α → α), Pointwise f SI -/
#guard_msgs in
#check @instSection

def mkBundle (f : SI → α) : Bundle α := ⟨f⟩

-- Test that a declaration made under a parametric index stays polymorphic in it

/-- info: @mkBundle : {SI α : Type} → (SI → α) → Bundle α SI -/
#guard_msgs in
#check @mkBundle

end

-- Test that a caller specializes the index by unification, not from the ambient index

/-- info: mkBundle fun x => 0 : Bundle Nat Unit -/
#guard_msgs in
#check mkBundle (fun _ : Unit => (0 : Nat))

section
local stepindex Unit

def unitBundle : Bundle Nat := mkBundle (fun _ => 0)

-- Test that a fresh application of `Bundle` takes the caller's ambient index

/-- info: Iris.Tests.unitBundle : Bundle Nat Unit -/
#guard_msgs in
#check unitBundle

end

-- Still works outside the section

/-- info: @instSection : ∀ {SI α : Type} (f : α → α), Pointwise f SI -/
#guard_msgs in
#check @instSection

section
variable {SI : Type}
local stepindex SI

def onlyIndex : Bundle Nat := ⟨fun _ => 0⟩

-- Test that the index is bound even when it is the only variable the declaration uses

/-- info: @onlyIndex : {SI : Type} → Bundle Nat SI -/
#guard_msgs in
#check @onlyIndex

end

section
universe u v
variable {SIu : Type u} {β : Type v}
local stepindex SIu

structure UBundle (α : Type v) (SI : Type u := by infer_stepindex) where
  ucar : SI → α

def uMk (f : SIu → β) : UBundle β := ⟨f⟩

-- Test that the index is inferred when its universe differs from the carrier's

/-- info: @uMk : {SIu : Type u_1} → {β : Type u_2} → (SIu → β) → UBundle β SIu -/
#guard_msgs in
#check @uMk

end

section
local stepindex Unit

-- Test that a fresh application commits to the ambient index rather than unifying

/--
error: Type mismatch
  b
has type
  Bundle Nat Nat
but is expected to have type
  Bundle Nat Unit
-/
#guard_msgs in
example (b : Bundle Nat Nat) : Bundle Nat := b

end

section
local stepindex Nonexistant

-- Test the error from an index name that does not resolve

/-- error: Unknown identifier `Nonexistant` -/
#guard_msgs in
example : Type := by infer_stepindex

end

section EagerVsLate
local stepindex Nat

class TD (α : Type) (SI : Type) where d : SI → α → α → Prop
instance : TD Nat Nat := ⟨fun _ _ _ => True⟩
instance {n : Nat} : Trans (TD.d (α := Nat) (SI := Nat) n) (TD.d (α := Nat) (SI := Nat) n)
    (TD.d (α := Nat) (SI := Nat) n) := ⟨fun _ _ => trivial⟩

notation:40 x " ~[" k "]~ " y:41 => TD.d (SI := stepindex%) k x y
notation:40 x " ~?[" k "]~ " y:41 => TD.d (SI := by infer_stepindex) k x y

-- Test that an eagerly resolved index can be used in `calc`: `Trans` needs the index during
-- elaboration, so this is the property that `stepindex%` exists to provide

example (a b c : Nat) (n : Nat) (h1 : a ~[n]~ b) (h2 : b ~[n]~ c) : a ~[n]~ c := calc
  a ~[n]~ b := h1
  _ ~[n]~ c := h2

-- Test that the tactic form cannot: a `by` block is a synthetic *opaque* metavariable, so
-- `Trans` is unresolvable even though `n : Nat`. Guards the two against being swapped.

/--
error: invalid 'calc' step, failed to synthesize `Trans` instance
  Trans (TD.d ?m.16) (TD.d ?m.22) ?m.25

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example (a b c : Nat) (n : Nat) (h1 : a ~?[n]~ b) (h2 : b ~?[n]~ c) : a ~?[n]~ c := calc
  a ~?[n]~ b := h1
  _ ~?[n]~ c := h2

end EagerVsLate

end Iris.Tests
