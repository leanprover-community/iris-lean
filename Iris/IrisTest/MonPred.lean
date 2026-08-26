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

/- Tests `asEmpValid_monPred_at_wand`, which has higher priority than `asEmpValid_monPred_at`. -/
/-- info:
  solution: AsEmpValid AsEmpValid.Direction.from (⎡𝓟⎤ ⊢ ⎡𝓠⎤)
    InOut.in PROP bi iprop(∀ i, 𝓟 -∗ 𝓠),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (𝓟 𝓠 : PROP) in
#ipm_synth AsEmpValid .from ((⎡𝓟⎤ : MonPred I PROP) ⊢ ⎡𝓠⎤) .in PROP bi _

/- Tests `asEmpValid_monPred_at_equiv`, which has higher priority than `asEmpValid_monPred_at`. -/
/-- info:
  solution: AsEmpValid AsEmpValid.Direction.from (⎡𝓟⎤ ⊣⊢ ⎡𝓠⎤)
    InOut.in PROP bi iprop(∀ i, 𝓟 ∗-∗ 𝓠),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (𝓟 𝓠 : PROP) in
#ipm_synth AsEmpValid .from ((⎡𝓟⎤ : MonPred I PROP) ⊣⊢ ⎡𝓠⎤) .in PROP bi _

/-
  Tests `asEmpValid_monPred_at` after ``asEmpValid_monPred_at_wand` and
  `asEmpValid_monPred_at_equiv` fail to apply and cause backtracking.
-/
/-- info:
  solution: AsEmpValid AsEmpValid.Direction.from (⊢ ⌜φ⌝ ∧ ⌜φ⌝)
    InOut.in PROP bi iprop(∀ i, ⌜φ⌝ ∧ ⌜φ⌝),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (φ : Prop) in
#ipm_synth AsEmpValid .from (⊢@{MonPred I PROP} ⌜φ⌝ ∧ ⌜φ⌝) .in PROP bi _

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

section ProofModeInstances

variable {I : BiIndex} {PROP : Type _} [bi : BI PROP]

/- Tests `intoExcept0_monPred_at_fwd`. -/
/-- info:
  solution: IntoExcept0 (iprop(◇ ⎡𝓟⎤).monPred_at i) 𝓟,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (𝓟 : PROP) (i : I.car) in
#ipm_synth IntoExcept0 ((iprop(◇ ⎡𝓟⎤) : MonPred I PROP).monPred_at i) _

/- Tests `intoWand_monPred_at_unknown_unknown`. -/
/-- info:
  solution: IntoWand false false (iprop(⎡𝓟⎤ -∗ ⎡𝓠⎤).monPred_at i) WandMode.unknown 𝓟 𝓠,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (i j : I.car) [IsBiIndexRel i j] (𝓟 𝓠 : PROP) in
#ipm_synth IntoWand false false ((iprop(⎡𝓟⎤ -∗ ⎡𝓠⎤) : MonPred I PROP).monPred_at i) .unknown _ _

/- Tests `intoWand_monPred_at_known_unknown_le`. -/
/-- info:
  solution: IntoWand false false (iprop(⎡𝓟⎤ -∗ Q).monPred_at i)
    (WandMode.matching WandMode.Side.argument) (⎡𝓟⎤.monPred_at j) (Q.monPred_at j),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (i j : I.car) [IsBiIndexRel i j] (𝓟 : PROP) (Q : MonPred I PROP) in
#ipm_synth IntoWand false false ((iprop(⎡𝓟⎤ -∗ Q) : MonPred I PROP).monPred_at i)
  (.matching .argument) ((iprop(⎡𝓟⎤) : MonPred I PROP).monPred_at j) _

/- Tests `intoWand_monPred_at_known_unknown_ge`. -/
/-- info:
  solution: IntoWand false false (iprop(⎡𝓟⎤ -∗ Q).monPred_at j)
    (WandMode.matching WandMode.Side.argument) (⎡𝓟⎤.monPred_at i) (Q.monPred_at j),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (i j : I.car) [IsBiIndexRel i j] (𝓟 : PROP) (Q : MonPred I PROP) in
#ipm_synth IntoWand false false ((iprop(⎡𝓟⎤ -∗ Q) : MonPred I PROP).monPred_at j)
  (.matching .argument) ((iprop(⎡𝓟⎤) : MonPred I PROP).monPred_at i) _

/- Tests that `fromModal_objectively` selects `modality_objectively`. -/
/-- info:
  solution: FromModal InOut.out modality_objectively True iprop(<obj> P) iprop(<obj> P) P,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (P : MonPred I PROP) in
#ipm_synth FromModal .out _ _ iprop(<obj> P) iprop(<obj> P) _

/- Introducing `<obj>` using `imodintro`. -/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
φ : Prop
hφ : φ
⊢
⊢ ⌜φ⌝
-/
#guard_msgs (whitespace := lax) in
example (φ : Prop) (hφ : φ) : ⊢@{MonPred I PROP} <obj> ⌜φ⌝ := by
  iintro
  imodintro (<obj> _)
  trace_state
  itrivial

example (𝓟 : PROP) : ⊢@{MonPred I PROP} ⎡𝓟⎤ -∗ <obj> ⎡𝓟⎤ := by
  istart (MonPred I PROP)
  iintro H
  imodintro (<obj> _)
  iexact H

/- Tests `ispecialize` using `intoForall_monPred_at` which has a higher priority than `intoForall_monPred_at_index`. -/
/-- trace:
I : BiIndex
PROP : Type u_2
bi : BI PROP
α : Sort u_1
Φ : α → PROP
a : α
i : I.car
⊢
∗H : Φ a
⊢ Φ a
-/
#guard_msgs (whitespace := lax) in
example {α} (Φ : α → PROP) (a : α) (i : I.car) :
    (iprop(∀ x, ⎡Φ x⎤) : MonPred I PROP).monPred_at i ⊢ Φ a := by
  iintro H
  ispecialize H $$ %a
  trace_state
  iexact H

/-
  Tests `ispecialize` using `intoForall_monPred_at_index` after
  `intoForall_monPred_at` fails to apply and results in backtracking.
-/
/-- trace:
I : BiIndex
PROP : Type u_1
bi : BI PROP
P : MonPred I PROP
i j : I.car
hij : i ≤ j
⊢
∗H : ⌜i ≤ j⌝ → P.monPred_at j
⊢ P.monPred_at j
-/
#guard_msgs (whitespace := lax) in
example (P : MonPred I PROP) (i j : I.car) (hij : I.rel.le i j) :
    P.monPred_at i ⊢ P.monPred_at j := by
  iintro H
  ispecialize H $$ %j
  trace_state
  ispecialize H $$ %hij
  iexact H

/- Tests `fromAssumption_make_monPred_at_l`. -/
/-- info:
  solution: ∀ (𝓟 : PROP) (j : I.car),
    FromAssumption true InOut.in (⎡𝓟⎤.monPred_at j) 𝓟,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth ∀ 𝓟 (j : I.car), FromAssumption true .in ((iprop(⎡𝓟⎤) : MonPred I PROP).monPred_at j) 𝓟

/- Tests `fromAssumption_make_monPred_at_r`. -/
/-- info:
  solution: ∀ (𝓟 : semiOutParamCore InOut.in PROP) (j : I.car),
    FromAssumption true InOut.in 𝓟 (⎡𝓟⎤.monPred_at j),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth ∀ 𝓟 (j : I.car), FromAssumption true .in 𝓟 ((iprop(⎡𝓟⎤) : MonPred I PROP).monPred_at j)

end ProofModeInstances

section FrameMonPredAt

variable {I : BiIndex} {PROP : Type _} [bi : BI PROP]
variable (i j : I.car) [instRel : IsBiIndexRel i j]

/- Tests `frameMonPredAt_here`, which has a higher priority than `frameMonPredAt_sep`. -/
/-- info:
  solution: FrameMonPredAt false i (iprop(P ∗ Q).monPred_at i) iprop(P ∗ Q) iprop(emp),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (P Q : MonPred I PROP) in
#ipm_synth FrameMonPredAt false i ((iprop(P ∗ Q) : MonPred I PROP).monPred_at i) iprop(P ∗ Q) _

/- Tests `frameMonPredAt_here`, which weakens the index using `IsBiIndexRel i j`. -/
/-- info:
  solution: FrameMonPredAt false j (P.monPred_at i) P iprop(emp),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (P : MonPred I PROP) in
#ipm_synth FrameMonPredAt false j (P.monPred_at i) P _

/- Tests `frameMonPredAt_sep`. -/
/-- info:
  solution: FrameMonPredAt false i (P.monPred_at i) iprop(P ∗ Q) (Q.monPred_at i),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (P Q : MonPred I PROP) in
#ipm_synth FrameMonPredAt false i (P.monPred_at i) iprop(P ∗ Q) _

/- Tests `frameMonPredAt_wand`. -/
/-- info:
  solution: FrameMonPredAt false i (R.monPred_at i) iprop(P -∗ R ∗ S)
    (iprop(P -∗ S).monPred_at i),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
variable (P R S : MonPred I PROP) in
#ipm_synth FrameMonPredAt false i (R.monPred_at i) iprop(P -∗ R ∗ S) _

/- Tests `iframe` with `FrameMonPredAt` instances. -/
example (P Q : MonPred I PROP) :
    (iprop(P ∗ Q) : MonPred I PROP).monPred_at i ⊢ (iprop(Q ∗ P) : MonPred I PROP).monPred_at j := by
  iintro ⟨H1, H2⟩
  iframe

end FrameMonPredAt

end IrisTest.MonPredAsEmpValid
