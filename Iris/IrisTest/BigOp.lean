/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI.BigOp
public import Iris.ProofMode

@[expose] public section

namespace IrisTest
open Iris BI ProofMode Std

section ProofModeInstances

variable {PROP : Type} [BI PROP] {A B : Type} (p : Bool)
variable (Φ : Nat → A → PROP) (Ψ : Nat → A → B → PROP) (Ξ : A → PROP)
variable (x x' : A) (y : B) (l l1 l2 : List A) (k1 k2 : List B)
variable {MS : Type} [LawfulFiniteMultiSet MS A] (X1 X2 : MS)

/-
  Tests `fromSep_bigSepL_cons` after `fromSep_bigSepL_app` fails to apply
  and causes backtracking.
-/
/-- info:
  solution: FromSep ([∗list] k ↦ y ∈ x :: l, Φ k y) (Φ 0 x) ([∗list] k ↦ y ∈ l, Φ (k + 1) y),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth FromSep ([∗list] k ↦ y ∈ x :: l, Φ k y) _ _

/- Tests `fromSep_bigSepL_app`. -/
/-- info:
  solution: FromSep ([∗list] k ↦ y ∈ l1 ++ l2, Φ k y) ([∗list] k ↦ y ∈ l1, Φ k y)
    ([∗list] k ↦ y ∈ l2, Φ (k + l1.length) y),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth FromSep ([∗list] k ↦ y ∈ l1 ++ l2, Φ k y) _ _

/-
  Tests `fromSep_bigSepL2_cons` after `fromSep_bigSepL2_app` fails to apply
  and causes backtracking.
-/
/-- info:
  solution: FromSep ([∗list] k ↦ y₁;y₂ ∈ x :: l;y :: k1, Ψ k y₁ y₂) (Ψ 0 x y)
    ([∗list] k ↦ y₁;y₂ ∈ l;k1, Ψ (k + 1) y₁ y₂),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth FromSep ([∗list] k ↦ y1;y2 ∈ x :: l; y :: k1, Ψ k y1 y2) _ _

/- Tests `fromSep_bigSepL2_app`. -/
/-- info:
  solution: FromSep ([∗list] k ↦ y₁;y₂ ∈ l1 ++ l2;k1 ++ k2, Ψ k y₁ y₂)
    ([∗list] k ↦ y₁;y₂ ∈ l1;k1, Ψ k y₁ y₂) ([∗list] k ↦ y₁;y₂ ∈ l2;k2, Ψ (k + l1.length) y₁ y₂),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth FromSep ([∗list] k ↦ y₁;y₂ ∈ l1 ++ l2; k1 ++ k2, Ψ k y₁ y₂) _ _

/- Tests `fromSep_bigSepMS_disjUnion`, matching `X₁ ⊎ X₂` syntactically. -/
/-- info:
  solution: FromSep ([∗mset] y ∈ X1 ⊎ X2, Ξ y) ([∗mset] y ∈ X1, Ξ y) ([∗mset] y ∈ X2, Ξ y),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth FromSep ([∗mset] z ∈ X1 ⊎ X2, Ξ z) _ _

/-
  Synthesis fails as the metavariable `?l` is involved and the guards
  `IsApp` and `IsCons` apply.
-/
/-- info: None -/
#guard_msgs in
#ipm_synth FromSep ([∗list] k ↦ y ∈ ?l, Φ k y) _ _

/- Tests `intoSep_bigSepL_app`. -/
/-- info:
  solution: IntoSep ([∗list] k ↦ y ∈ l1 ++ l2, Φ k y) ([∗list] k ↦ y ∈ l1, Φ k y)
    ([∗list] k ↦ y ∈ l2, Φ (k + l1.length) y),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoSep ([∗list] k ↦ y ∈ l1 ++ l2, Φ k y) _ _

/-
  Tests `intoSep_bigSepL_cons` after `intoSep_bigSepL_app` fails to apply
  and causes backtracking.
-/
/-- info:
  solution: IntoSep ([∗list] k ↦ y ∈ x :: l1, Φ k y) (Φ 0 x) ([∗list] k ↦ y ∈ l1, Φ (k + 1) y),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoSep ([∗list] k ↦ y ∈ x :: l1, Φ k y) _ _

/-
  Tests `fromAnd_bigSepL_cons_persistent` after `fromAnd_bigSepL_app_persistent`
  fails to apply and leads to backtracking.
-/
/-- info:
  solution: FromAnd ([∗list] k ↦ y ∈ x :: l, Φ k y) (Φ 0 x) ([∗list] k ↦ y ∈ l, Φ (k + 1) y),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable [∀ k y, Persistent (Φ k y)] in
#ipm_synth FromAnd ([∗list] k ↦ y ∈ x :: l, Φ k y) _ _

/- Tests `fromAnd_bigSepL_app_persistent`. -/
/-- info:
  solution: FromAnd ([∗list] k ↦ y ∈ l1 ++ l2, Φ k y) ([∗list] k ↦ y ∈ l1, Φ k y)
    ([∗list] k ↦ y ∈ l2, Φ (k + l1.length) y),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable [∀ k y, Persistent (Φ k y)] in
#ipm_synth FromAnd ([∗list] k ↦ y ∈ l1 ++ l2, Φ k y) _ _

/-
  Tests `fromAnd_bigSepL2_cons_persistent` after `fromAnd_bigSepL2_app_persistent`
  fails to apply and leads to backtracking.
-/
/-- info:
  solution: FromAnd ([∗list] k ↦ y₁;y₂ ∈ x :: l;y :: k1, Ψ k y₁ y₂) (Ψ 0 x y)
    ([∗list] k ↦ y₁;y₂ ∈ l;k1, Ψ (k + 1) y₁ y₂),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable [∀ k x1 x2, Persistent (Ψ k x1 x2)] in
#ipm_synth FromAnd ([∗list] k ↦ x1;x2 ∈ x :: l; y :: k1, Ψ k x1 x2) _ _


/- Tests `fromAnd_bigSepMS_disjUnion_persistent`. -/
/-- info:
  solution: FromAnd ([∗mset] y ∈ X1 ⊎ X2, Ξ y) ([∗mset] y ∈ X1, Ξ y) ([∗mset] y ∈ X2, Ξ y),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable [∀ y, Persistent (Ξ y)] in
#ipm_synth FromAnd ([∗mset] z ∈ X1 ⊎ X2, Ξ z) _ _

/- Tests `intoLaterN_bigSepL`: the later modality is stripped. -/
/-- info:
  solution: IntoLaterN true false 1
    ([∗list] k ↦ x ∈ l, iprop(▷ Φ k x)) ([∗list] k ↦ x ∈ l, Φ k x),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoLaterN (progress := true) (only_head := false) 1
  iprop([∗list] k ↦ x ∈ l, ▷ Φ k x) _

/- Tests `intoLaterN_bigSepL` with `only_head = true`: the later modality is not stripped. -/
/-- info: None -/
#guard_msgs in
#ipm_synth IntoLaterN (progress := true) (only_head := true) 1
  iprop([∗list] k ↦ x ∈ l, ▷ Φ k x) _

/- Tests `intoLaterN_bigSepL` along with `intoLaterN_later` and `intoLaterN_and_left`. -/
/-- info:
  solution: IntoLaterN true false 2 ([∗list] k ↦ x ∈ l, iprop(▷ (▷ Φ k x ∧ ▷ Φ k x)))
  ([∗list] k ↦ x ∈ l, iprop(Φ k x ∧ Φ k x)),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IntoLaterN true false 2 iprop([∗list] k ↦ x ∈ l, ▷ (▷ Φ k x ∧ ▷ Φ k x)) _

/- Tests `frame_bigSepL_cons` after backtracking from `frame_bigSepL_app`. -/
example (Φ : Nat → A → PROP) (x : A) (l : List A) :
    ([∗list] k ↦ y ∈ l, Φ (k + 1) y) ∗ Φ 0 x ⊢ [∗list] k ↦ y ∈ x :: l, Φ k y := by
  iintro ⟨H1, H2⟩
  iframe

/- Tests `frame_bigSepL_app`. -/
example (Φ : Nat → A → PROP) (l1 l2 : List A) :
    ([∗list] k ↦ y ∈ l1, Φ k y) ∗ ([∗list] k ↦ y ∈ l2, Φ (k + l1.length) y) ⊢
      [∗list] k ↦ y ∈ l1 ++ l2, Φ k y := by
  iintro ⟨H1, H2⟩
  iframe

/- Tests `frame_bigSepMS_disj_union`. -/
example (Φ : A → PROP) (X Y : MS) :
    ([∗mset] z ∈ X, Φ z) ∗ ([∗mset] z ∈ Y, Φ z) ⊢ [∗mset] z ∈ X ⊎ Y, Φ z := by
  iintro ⟨H1, H2⟩
  iframe

/- Tests that `frame_here` has a higher priority than `Frame` instances for big operators. -/
example (Φ : Nat → A → PROP) (x : A) (l : List A) (P : PROP) :
    ([∗list] k ↦ y ∈ x :: l, Φ k y) ∗ P ⊢ ([∗list] k ↦ y ∈ x :: l, Φ k y) ∗ P := by
  iintro ⟨H1, H2⟩
  iframe

end ProofModeInstances
