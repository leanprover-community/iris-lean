/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Lib.Atomic

@[expose] public section

namespace IrisTest
open Iris Iris.Std BI ProofMode

/-! Tests for the `AU`/`AACC` notation inside `iprop(…)`: every combination of (non-)empty
telescopes parses, elaborates to the corresponding `atomic_update`/`atomic_acc` application, and
prints back in notation form. -/

section atomicNotation
variable {PROP : Type} [BI PROP] [BIFUpdate PROP] (Eo Ei : CoPset) (P Q : PROP)
  (α : Nat → PROP) (β : Nat → Bool → PROP) (Ψ : Nat → Bool → PROP)

/-! Both telescopes non-empty. -/

/-- info: iprop(AU <{ ∃∃ x, α x }> @ Eo, Ei <{ ∀∀ y, β x y, COMM Ψ x y }>) : PROP -/
#guard_msgs in
#check iprop(AU <{ ∃∃ x, α x }> @ Eo, Ei <{ ∀∀ y, β x y, COMM Ψ x y }>)

/-- info: iprop(AACC <{ ∃∃ x, α x, ABORT P }> @ Eo, Ei <{ ∀∀ y, β x y, COMM Ψ x y }>) : PROP -/
#guard_msgs in
#check iprop(AACC <{ ∃∃ x, α x, ABORT P }> @ Eo, Ei
  <{ ∀∀ y, β x y, COMM Ψ x y }>)

/-! Empty `∀∀` telescope. -/

/-- info: iprop(AU <{ ∃∃ x, α x }> @ Eo, Ei <{ α 0, COMM Q }>) : PROP -/
#guard_msgs in
#check iprop(AU <{ ∃∃ x, α x }> @ Eo, Ei <{ α 0, COMM Q }>)

/-- info: iprop(AACC <{ ∃∃ x, α x, ABORT P }> @ Eo, Ei <{ α 0, COMM Q }>) : PROP -/
#guard_msgs in
#check iprop(AACC <{ ∃∃ x, α x, ABORT P }> @ Eo, Ei <{ α 0, COMM Q }>)

/-! Empty `∃∃` telescope. -/

/-- info: iprop(AU <{ P }> @ Eo, Ei <{ ∀∀ y, β 0 y, COMM Q }>) : PROP -/
#guard_msgs in
#check iprop(AU <{ P }> @ Eo, Ei <{ ∀∀ y, β 0 y, COMM Q }>)

/-- info: iprop(AACC <{ P, ABORT P }> @ Eo, Ei <{ ∀∀ y, β 0 y, COMM Q }>) : PROP -/
#guard_msgs in
#check iprop(AACC <{ P, ABORT P }> @ Eo, Ei <{ ∀∀ y, β 0 y, COMM Q }>)

/-! Both telescopes empty. -/

/-- info: iprop(AU <{ P }> @ Eo, Ei <{ Q, COMM Q }>) : PROP -/
#guard_msgs in
#check iprop(AU <{ P }> @ Eo, Ei <{ Q, COMM Q }>)

/-- info: iprop(AACC <{ P, ABORT P }> @ Eo, Ei <{ Q, COMM Q }>) : PROP -/
#guard_msgs in
#check iprop(AACC <{ P, ABORT P }> @ Eo, Ei <{ Q, COMM Q }>)

/-! Several binders, type ascriptions, dependent binders, and anonymous binders. Binder types are
inferred from the bodies, so they are not printed. -/

/--
info: iprop(AU <{ ∃∃ x₁ x₂, α x₁ ∗ α x₂ }> @ Eo, Ei
    <{ ∀∀ y₁ y₂, β x₁ y₁ ∗ β x₂ y₂, COMM Q }>) : PROP
-/
#guard_msgs (whitespace := lax) in
#check iprop(AU <{ ∃∃ x₁ x₂, α x₁ ∗ α x₂ }> @ Eo, Ei
  <{ ∀∀ y₁ y₂, β x₁ y₁ ∗ β x₂ y₂, COMM Q }>)

/-- info: iprop(AU <{ ∃∃ x, α x }> @ Eo, Ei <{ ∀∀ y, β x y, COMM Q }>) : PROP -/
#guard_msgs in
#check iprop(AU <{ ∃∃ (x : Nat), α x }> @ Eo, Ei <{ ∀∀ (y : Bool), β x y, COMM Q }>)

/-- info: iprop(AU <{ ∃∃ n v, α n }> @ Eo, Ei <{ α 0, COMM Q }>) : PROP -/
#guard_msgs in
set_option linter.unusedVariables false in
#check iprop(AU <{ ∃∃ (n : Nat) (v : Fin n), α n }> @ Eo, Ei <{ α 0, COMM Q }>)

/-- info: iprop(AU <{ ∃∃ x, P }> @ Eo, Ei <{ ∀∀ x, Q, COMM Q }>) : PROP -/
#guard_msgs in
#check iprop(AU <{ ∃∃ (_ : Nat), P }> @ Eo, Ei <{ ∀∀ (_ : Bool), Q, COMM Q }>)

/-! The notation composes with surrounding `iprop(…)` connectives. -/

/-- info: iprop(P ∗ AU <{ ∃∃ x, α x }> @ Eo, Ei <{ ∀∀ y, β x y, COMM Ψ x y }>) : PROP -/
#guard_msgs in
#check iprop(P ∗ AU <{ ∃∃ x, α x }> @ Eo, Ei <{ ∀∀ y, β x y, COMM Ψ x y }>)

/-! The masks may be compound terms. -/

/-- info: iprop(AU <{ ∃∃ x, α x }> @ ⊤ \ Eo, Eo ∩ Ei <{ ∀∀ y, β x y, COMM Ψ x y }>) : PROP -/
#guard_msgs in
#check iprop(AU <{ ∃∃ x, α x }> @ ⊤ \ Eo, Eo ∩ Ei
  <{ ∀∀ y, β x y, COMM Ψ x y }>)

/-! `AU` and `AACC` are not reserved tokens. -/
example (AU AACC : Nat) : Nat := AU + AACC

/-! The notation elaborates to exactly the terms the lemmas about `atomic_update` and
`atomic_acc` are stated with. -/
example : (AU <{ ∃∃ x, α x }> @ Eo, Ei <{ ∀∀ y, β x y, COMM Ψ x y }>) ⊢
    AACC <{ ∃∃ x, α x,
        ABORT AU <{ ∃∃ x, α x }> @ Eo, Ei <{ ∀∀ y, β x y, COMM Ψ x y }> }>
      @ Eo, Ei <{ ∀∀ y, β x y, COMM Ψ x y }> :=
  aupd_aacc

end atomicNotation
end IrisTest
