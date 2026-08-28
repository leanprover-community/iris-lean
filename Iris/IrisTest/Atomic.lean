/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.ProgramLogic.Atomic

@[expose] public section

namespace IrisTest
open Iris ProgramLogic BI ProofMode Std

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

/-! Tests for the logically atomic Hoare triple notation. -/

section atomicWpNotation
variable {hlc : HasLC} {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} [IrisGS_gen hlc Expr GF]
variable (e : Expr) (E : CoPset) (w : Val) (P : IProp GF)
  (α : Nat → IProp GF) (β : Nat → Bool → IProp GF) (γ : Nat → Bool → Unit → IProp GF)
  (g : Nat → Bool → Unit → Val)

/-! All binder groups and the private postcondition present. -/

/--
info: iprop(<<{ ∀∀ x, α x }>> e @ E <<{ ∃∃ y, β x y | z, RET g x y z ; γ x y z }>>) : IProp GF
-/
#guard_msgs (whitespace := lax) in
#check iprop(<<{ ∀∀ x, α x }>> e @ E <<{ ∃∃ y, β x y | z, RET g x y z ; γ x y z }>>)

/-! No `RET` binders. -/

/-- info: iprop(<<{ ∀∀ x, α x }>> e @ E <<{ ∃∃ y, β x y | RET w ; P }>>) : IProp GF -/
#guard_msgs in
#check iprop(<<{ ∀∀ x, α x }>> e @ E <<{ ∃∃ y, β x y | RET w ; P }>>)

/-! No private postcondition. -/

/-- info: iprop(<<{ ∀∀ x, α x }>> e @ E <<{ ∃∃ y, β x y | RET w }>>) : IProp GF -/
#guard_msgs in
#check iprop(<<{ ∀∀ x, α x }>> e @ E <<{ ∃∃ y, β x y | RET w }>>)

/-! Empty `∀∀` telescope. -/

/-- info: iprop(<<{ P }>> e @ E <<{ ∃∃ y, β 0 y | RET w }>>) : IProp GF -/
#guard_msgs in
#check iprop(<<{ P }>> e @ E <<{ ∃∃ y, β 0 y | RET w }>>)

/-! Empty `∃∃` telescope. -/

/-- info: iprop(<<{ ∀∀ x, α x }>> e @ E <<{ β 0 true | RET w }>>) : IProp GF -/
#guard_msgs in
#check iprop(<<{ ∀∀ x, α x }>> e @ E <<{ β 0 true | RET w }>>)

/-! All telescopes empty, no private postcondition. -/

/-- info: iprop(<<{ P }>> e @ E <<{ P | RET w }>>) : IProp GF -/
#guard_msgs in
#check iprop(<<{ P }>> e @ E <<{ P | RET w }>>)

/-! The implementation mask may be a compound term, in parentheses. -/

/-- info: iprop(<<{ P }>> e @ (⊤ \ E) <<{ P | RET w ; P }>>) : IProp GF -/
#guard_msgs in
#check iprop(<<{ P }>> e @ (⊤ \ E) <<{ P | RET w ; P }>>)

/-! Several binders per group, with type ascriptions. Binder types are inferred from the bodies,
so they are not printed. -/

/--
info: iprop(<<{ ∀∀ x₁ x₂, α x₁ ∗ α x₂ }>> e @ E
    <<{ ∃∃ y₁ y₂, β x₁ y₁ ∗ β x₂ y₂ | RET w }>>) : IProp GF
-/
#guard_msgs (whitespace := lax) in
#check iprop(<<{ ∀∀ (x₁ : Nat) (x₂ : Nat), α x₁ ∗ α x₂ }>> e @ E
  <<{ ∃∃ (y₁ : Bool) (y₂ : Bool), β x₁ y₁ ∗ β x₂ y₂ | RET w }>>)

/-! The notation elaborates to exactly the term the theory is stated with. -/
example : (<<{ ∀∀ x, α x }>> e @ E <<{ ∃∃ y, β x y | RET w }>>) ⊢
    <<{ ∀∀ x, α x }>> e @ ⊤ <<{ ∃∃ y, β x y | RET w }>> :=
  atomic_wp_mask_weaken CoPset.subseteq_top

end atomicWpNotation
section ProofModeTactics

variable {PROP : Type u} [instBI : BI PROP] [instBIFUpd : BIFUpdate PROP] {TA TB : Tele}
variable {Eo Ei : CoPset} {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP}

/--
  Tests `iauintro` for reducing `atomic_update Eo Ei α β β` to `atomic_acc Eo Ei α (α x) β β`.
  Tests `iaaccintro` with `α x` for abort and `β x y` for commit.
-/
example (HEi : Ei ⊆ Eo) (x : TA.Arg) : α x ⊢ atomic_update Eo Ei α β β := by
  iintro Hα
  iauintro
  iaaccintro Hα
  · iintro Hα !> //
  · iintro %y Hβ !> //

/--
  Tests `iaaccintro` with `α x` for abort and `β x y` for commit.
  The argument for the telescopic quantifier is supplied.
-/
example (HEi : Ei ⊆ Eo) (x : TA.Arg) : α x ⊢ atomic_acc Eo Ei α (α x) β β := by
  iintro Hα
  iaaccintro %x Hα
  · iintro Hα !> //
  · iintro %y Hβ !> //

/-- Tests `iaaccintro` with the pre-condition `α x` obtained from several hypotheses. -/
example (HEi : Ei ⊆ Eo) (x : TA.Arg) {Q R : PROP} (hα : α x = iprop(Q ∗ R)) :
    Q ∗ R ⊢ atomic_acc Eo Ei α (α x) β β := by
  iintro ⟨HQ, HR⟩
  iaaccintro [HQ HR]
  · rw [hα]; iframe
  · iintro Hα !> //
  · iintro %y Hβ !> //

/-- error: iauintro: the goal Q is not an atomic update -/
#guard_msgs in
example (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iauintro

/-- error: iaaccintro: the goal Q is not an atomic accessor -/
#guard_msgs in
example {Q : PROP} : Q ⊢ Q := by
  iintro HQ
  iaaccintro HQ

/-- error: iaaccintro:
  the specialisation patterns must discharge the atomic precondition only,
  leaving atomic_acc Eo Ei α (α x) β β
-/
#guard_msgs (whitespace := lax) in
example (HEi : Ei ⊆ Eo) (x : TA.Arg) : α x ⊢ atomic_acc Eo Ei α (α x) β β := by
  iintro Hα
  iaaccintro %x Hα []

end ProofModeTactics

end IrisTest
