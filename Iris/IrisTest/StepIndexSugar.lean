/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.StepIndexFinite
public import IrisTest.StepIndexSugar.Left
public import IrisTest.StepIndexSugar.Right

@[expose] public section

namespace IrisTest.StepIndexSugar

open Iris

@[indexed]
def Family (SI : stepindex (Type u)) (A : Type v) := SI × A

@[indexed]
def ImplicitFamily {SI : stepindex (Type u)} (A : Type v) := SI × A

@[indexed]
def afterArgument (n : Nat) (SI : stepindex (Type)) (A : Type) := (Fin n × SI) × A

@[indexed]
def keep (_SI : stepindex (Type)) {A : Type} (x : A) : A := x

@[indexed]
structure Box (SI : stepindex (Type)) where
  value : SI

attribute [indexed] Box.mk

namespace Other
def Family (n : Nat) := n + 1
end Other

-- Outside the scope, ordinary explicit applications are unchanged.
example : Family Nat Bool = (Nat × Bool) := rfl

-- Macro templates use the explicit API and read the index at their use site.
local notation "sampleFamily" => IrisTest.StepIndexSugar.Family stepindex%

section
local stepindex Nat

section
open Left
-- The two independent imports generate the same spelling; parsing must stay unambiguous.
example : SharedFamily Bool = (Nat × Bool) := rfl
end

section
open Right
example : SharedFamily Bool = (Nat × Bool) := rfl
end

example : Family Bool = (Nat × Bool) := rfl
example : ImplicitFamily Bool = (Nat × Bool) := rfl
example : Family.{0, 1} (ULift.{1} Bool) = (Nat × ULift.{1} Bool) := rfl
example : True := by
  -- The declared universes must be respected, rather than silently inferred again.
  fail_if_success have : Family.{1, 0} Bool := (0, false)
  trivial
example : sampleFamily Bool = (Nat × Bool) := rfl

local notation "relativeFamily" => Family Bool
example : relativeFamily = (Nat × Bool) := rfl

-- Named arguments are handled before implicit arguments are instantiated.
example : Family (A := Bool) = (Nat × Bool) := rfl
example : keep (A := Nat) 3 = 3 := rfl
example : Family (SI := Unit) Bool = (Unit × Bool) := rfl
example : ImplicitFamily (SI := Unit) Bool = (Unit × Bool) := rfl
example : Box := Box.mk 3
example : (Box.mk 3 : Box).value = 3 := rfl

-- A preceding explicit parameter and partial applications need no arity guessing.
example : afterArgument 3 Bool = ((Fin 3 × Nat) × Bool) := rfl
example : (Family : Type → Type) Bool = (Nat × Bool) := rfl
example : (afterArgument 3 : Type → Type) Bool = ((Fin 3 × Nat) × Bool) := rfl

-- Application precedence: the bare notation can itself be a function argument.
example : (fun (F : Type → Type) (A : Type) => F A) Family Bool = (Nat × Bool) := rfl

-- Fully qualified or escaped identifiers provide the ordinary explicit API.
example : IrisTest.StepIndexSugar.Family Unit Bool = (Unit × Bool) := rfl
example : «Family» Unit Bool = (Unit × Bool) := rfl
example : (@IrisTest.StepIndexSugar.ImplicitFamily Unit Bool) = (Unit × Bool) := rfl
example : @Family Unit Bool = (Unit × Bool) := rfl
example : @ImplicitFamily Unit Bool = (Unit × Bool) := rfl
example : @keep Unit Nat 3 = 3 := rfl

/-- info: Family (SI := Unit) Bool : Type -/
#guard_msgs in
#check IrisTest.StepIndexSugar.Family Unit Bool

/-- info: ImplicitFamily (SI := Unit) Bool : Type -/
#guard_msgs in
#check IrisTest.StepIndexSugar.ImplicitFamily (SI := Unit) Bool

/-- info: Iris.OFE Nat Bool : Type -/
#guard_msgs in
set_option pp.fullNames true in
#check Iris.OFE Nat Bool

-- Notation spellings are not reserved keywords, and local variables still shadow globals.
example (Family : Nat) : Nat := Family
example (Family : Nat → Nat) : Family 3 = Family 3 := rfl
example («Family» : Nat → Nat) : Family 3 = Family 3 := rfl
-- Untyped lambda and match binders use term syntax, so colliding names need escaping there.
example : (fun «Family» => Family + 1) 3 = 4 := rfl

-- New declarations get notation even when the scope is already open.
@[indexed]
def DeclaredInScope (SI : stepindex (Type)) (A : Type) := SI × A

example : DeclaredInScope Bool = (Nat × Bool) := rfl

section
local stepindex Unit
example : Family Bool = (Unit × Bool) := rfl
example : sampleFamily Bool = (Unit × Bool) := rfl
example : relativeFamily = (Unit × Bool) := rfl
end

example : Family Bool = (Nat × Bool) := rfl

-- Existing imported classes use generated notation as well.
example (A : Type) : OFE A = Iris.OFE Nat A := rfl
example (A : Type) [OFE A] : Iris.OFE Nat A := inferInstance

end

section
variable {SI : stepindex (Type)} [SIdx SI]
local stepindex SI
example : Family Bool = (SI × Bool) := rfl
example (A : Type) : OFE A = Iris.OFE SI A := rfl
end

-- Section exit restores the explicit spelling.
example : Family Unit Bool = (Unit × Bool) := rfl

namespace Quoted
local stepindex Nat
scoped notation "quotedFamilyForSugar" => Family Bool
end Quoted

end IrisTest.StepIndexSugar

namespace IrisTest.QuotationClient

open Iris
open scoped IrisTest.StepIndexSugar.Quoted
local stepindex Unit

-- The quoted name keeps its original namespace; its step index comes from the use site.
example : quotedFamilyForSugar = (Unit × Bool) := rfl

end IrisTest.QuotationClient

namespace IrisTest

open Iris StepIndexSugar StepIndexSugar.Other

section
local stepindex Nat
-- Indexed and unindexed overloads retain ordinary type-directed resolution.
example : Family Bool = (Nat × Bool) := rfl
example : Family 3 = 4 := rfl
end

end IrisTest
