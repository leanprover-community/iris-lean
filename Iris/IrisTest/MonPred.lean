/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.ProofMode.MonPred

@[expose] public section

namespace IrisTest.MonPredAsEmpValid
open Iris BI ProofMode MonPred

section AsEmpValid

variable {I : BiIndex} {PROP : Type _} [bi : BI PROP]

/-
  Tests `asEmpValid_monPred_at`, `makeMonPredAt_and` and `makeMonPredAt_pure`:
  the goal becomes `∀ i, ⌜φ⌝ ∧ ⌜ψ⌝`, with no residual `monPred_at` left over.
-/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
φ ψ : Prop
hφ : φ
hψ : ψ
⊢
⊢ ∀ i, ⌜φ⌝ ∧ ⌜ψ⌝
-/
#guard_msgs (whitespace := lax) in
example (φ ψ : Prop) (hφ : φ) (hψ : ψ) : ⊢@{MonPred I PROP} ⌜φ⌝ ∧ ⌜ψ⌝ := by
  istart PROP
  trace_state
  iintro %i
  isplit <;> itrivial

/-
  Tests `asEmpValid_monPred_at`, `makeMonPredAt_or`, `makeMonPredAt_embed`
  and `makeMonPredAt_pure`:
  the goal becomes `∀ i, 𝓟 ∨ ⌜φ⌝`, i.e. the embedding is discharged as well.
-/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
𝓟 : PROP
φ : Prop
hφ : φ
⊢
⊢ ∀ i, 𝓟 ∨ ⌜φ⌝
-/
#guard_msgs (whitespace := lax) in
example (𝓟 : PROP) (φ : Prop) (hφ : φ) : ⊢@{MonPred I PROP} ⎡𝓟⎤ ∨ ⌜φ⌝ := by
  istart PROP
  trace_state
  iintro %i
  iright
  itrivial

/-
  Tests `asEmpValid_monPred_at` with nested `MakeMonPredAt`:
  `makeMonPredAt_intuitionistically` recurses into `makeMonPredAt_embed`,
  so the goal is `∀ i, □ 𝓟 ∨ emp` and not `∀ i, (□ ⎡𝓟⎤ ∨ emp).monPred_at i`.
-/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
𝓟 : PROP
⊢
⊢ ∀ i, □ 𝓟 ∨ emp
-/
#guard_msgs (whitespace := lax) in
example (𝓟 : PROP) : ⊢@{MonPred I PROP} □ ⎡𝓟⎤ ∨ emp := by
  istart PROP
  trace_state
  iintro %i
  iright
  iempintro

/- Without `istart PROP`, the same statement stays in `MonPred I PROP`. -/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
φ : Prop
hφ : φ
⊢
⊢ ⌜φ⌝ ∧ ⌜φ⌝
-/
#guard_msgs (whitespace := lax) in
example (φ : Prop) (hφ : φ) : ⊢@{MonPred I PROP} ⌜φ⌝ ∧ ⌜φ⌝ := by
  iintro
  trace_state
  isplit <;> itrivial

/-
  Tests `asEmpValid_monPred_at_wand` with `asEmpValid_entails`,
  which turns `P ⊢ Q` into `P -∗ Q`.
-/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
𝓟 𝓠 : PROP
⊢
⊢ ∀ i, 𝓟 ∗ 𝓠 -∗ 𝓠 ∗ 𝓟
-/
#guard_msgs (whitespace := lax) in
example (𝓟 𝓠 : PROP) : ⎡𝓟⎤ ∗ ⎡𝓠⎤ ⊢@{MonPred I PROP} ⎡𝓠⎤ ∗ ⎡𝓟⎤ := by
  istart PROP
  trace_state
  iintro %i ⟨H1, H2⟩
  isplitl [H2]
  · iexact H2
  · iexact H1


/-
  Tests `asEmpValid_monPred_at_wand` with
  `makeMonPredAt_sep` on the left and `makeMonPredAt_embed` on the right.
-/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
𝓟 𝓠 : PROP
⊢
⊢ ∀ i, 𝓟 ∗ 𝓠 -∗ 𝓟 ∗ 𝓠
-/
#guard_msgs (whitespace := lax) in
example (𝓟 𝓠 : PROP) : ⎡𝓟⎤ ∗ ⎡𝓠⎤ ⊢@{MonPred I PROP} ⎡𝓟 ∗ 𝓠⎤ := by
  istart PROP
  trace_state
  iintro %i H
  iexact H

/- Tests `asEmpValid_monPred_at_wand` with `makeMonPredAt_forall` and `makeMonPredAt_exists`. -/
/-- trace:
I : BiIndex
PROP : Type u_2
bi : BI PROP
α : Type u_1
Φ : α → PROP
a : α
⊢
⊢ ∀ i, (∀ a, Φ a) -∗ ∃ a, Φ a
-/
#guard_msgs (whitespace := lax) in
example {α : Type _} (Φ : α → PROP) (a : α) :
    (∀ a, ⎡Φ a⎤) ⊢@{MonPred I PROP} ∃ a, ⎡Φ a⎤ := by
  istart PROP
  trace_state
  iintro %i H
  iexists a
  ispecialize H $$ %a
  iexact H

/- Tests `asEmpValid_monPred_at_wand` with `makeMonPredAt_in`. -/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
j : I.car
⊢
⊢ ∀ i, ⌜j ≤ i⌝ -∗ ⌜j ≤ i⌝
-/
#guard_msgs (whitespace := lax) in
example (j : I.car) :
    MonPred.monPred_in j ⊢@{MonPred I PROP} MonPred.monPred_in j := by
  istart PROP
  trace_state
  iintro %i H
  iexact H

/-
  Tests `asEmpValid_monPred_at_equiv` with `asEmpValid_bientails`, recursing
  under `□` and `∀`.
-/
/-- trace:
I : BiIndex
PROP : Type u_2
bi : BI PROP
α : Type u_1
Φ : α → PROP
⊢
⊢ ∀ i, (□ ∀ a, Φ a) ∗-∗ □ ∀ a, Φ a
-/
#guard_msgs (whitespace := lax) in
example {α : Type _} (Φ : α → PROP) :
    □ (∀ a, ⎡Φ a⎤) ⊣⊢@{MonPred I PROP} ⎡□ (∀ a, Φ a)⎤ := by
  istart PROP
  trace_state
  iintro %i
  isplit <;> iintro _ //

-- Expected: `AsEmpValid .from _ .in PROP bi .out iprop(∀ i, 𝓟 -∗ 𝓠)`,
-- i.e. `asEmpValid_monPred_at_wand` (not `asEmpValid_monPred_at`).



/- Tests `asEmpValid_monPred_at_wand`, which has higher priority than `asEmpValid_monPred_at`. -/
/-- info:
  solution: AsEmpValid AsEmpValid.Direction.from (⎡𝓟⎤ ⊢ ⎡𝓠⎤)
    InOut.in PROP bi InOut.out iprop(∀ i, 𝓟 -∗ 𝓠),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (𝓟 𝓠 : PROP) in
#ipm_synth AsEmpValid .from ((⎡𝓟⎤ : MonPred I PROP) ⊢ ⎡𝓠⎤) .in PROP bi .out _

/- Tests `asEmpValid_monPred_at_equiv`, which has higher priority than `asEmpValid_monPred_at`. -/
/-- info:
  solution: AsEmpValid AsEmpValid.Direction.from (⎡𝓟⎤ ⊣⊢ ⎡𝓠⎤)
    InOut.in PROP bi InOut.out iprop(∀ i, 𝓟 ∗-∗ 𝓠),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (𝓟 𝓠 : PROP) in
#ipm_synth AsEmpValid .from ((⎡𝓟⎤ : MonPred I PROP) ⊣⊢ ⎡𝓠⎤) .in PROP bi .out _

/-
  Tests `asEmpValid_monPred_at` after ``asEmpValid_monPred_at_wand` and
  `asEmpValid_monPred_at_equiv` fail to apply and cause backtracking.
-/
/-- info:
  solution: AsEmpValid AsEmpValid.Direction.from (⊢ ⌜φ⌝ ∧ ⌜φ⌝)
    InOut.in PROP bi InOut.out iprop(∀ i, ⌜φ⌝ ∧ ⌜φ⌝),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (φ : Prop) in
#ipm_synth AsEmpValid .from (⊢@{MonPred I PROP} ⌜φ⌝ ∧ ⌜φ⌝) .in PROP bi .out _

end AsEmpValid

section MakeMonPredAt

variable {I : BiIndex} {PROP : Type _} [bi : BI PROP]

/-- A monotone predicate for testing. -/
def testMonPred (𝓟 : PROP) : MonPred I PROP where
  monPred_at _ := 𝓟
  monPred_mono _ := .rfl

/- Tests `makeMonPredAt_default` as the fallback option of `MakeMonPredAt`. -/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
𝓟 𝓠 : PROP
⊢
⊢
∀ i,
  (testMonPred 𝓟).monPred_at i ∗ (testMonPred 𝓠).monPred_at i -∗
    (testMonPred 𝓠).monPred_at i ∗ (testMonPred 𝓟).monPred_at i
-/
#guard_msgs (whitespace := lax) in
example (𝓟 𝓠 : PROP) :
    testMonPred 𝓟 ∗ testMonPred 𝓠 ⊢@{MonPred I PROP} testMonPred 𝓠 ∗ testMonPred 𝓟 := by
  istart PROP
  trace_state
  iintro %i ⟨H1, H2⟩
  isplitl [H2]
  · iexact H2
  · iexact H1

set_option synthInstance.checkSynthOrder false in
instance makeMonPredAt_testMonPred (d : MakeMonPredAt.Kind) (i : I.car) (𝓟 : PROP) :
    MakeMonPredAt d i (testMonPred 𝓟) 𝓟 where
  make_monPred_at := .rfl

/- Tests `makeMonPredAt_testMonPred`, which has a higher priority than `makeMonPredAt_default`. -/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
𝓟 𝓠 : PROP
⊢
⊢ ∀ i, 𝓟 ∗ 𝓠 -∗ 𝓠 ∗ 𝓟
-/
#guard_msgs (whitespace := lax) in
example (𝓟 𝓠 : PROP) :
    testMonPred 𝓟 ∗ testMonPred 𝓠 ⊢@{MonPred I PROP} testMonPred 𝓠 ∗ testMonPred 𝓟 := by
  istart PROP
  trace_state
  iintro %i ⟨H1, H2⟩
  isplitl [H2]
  · iexact H2
  · iexact H1

end MakeMonPredAt

end IrisTest.MonPredAsEmpValid
