/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.ProofMode
public import Iris.Std.Telescopes
public import Iris.BI.Telescopes

@[expose] public section

namespace IrisTest
open Iris BI ProofMode Std

variable {PROP : Type} [inst : BI PROP] {TT : Tele.{0}}
  (Φ Ψ : TT.Arg → PROP) (φ : TT.Arg → Prop) (a : TT.Arg)

/- Delaboration of the telescope-aware lambda. -/
/-- info: λ.. x, Φ x : TT.Arg → PROP -/
#guard_msgs in #check (λ.. x, Φ x)

variable (TU : TT.Arg → Tele) (f : (x : TT.Arg) → (TU x).Arg → PROP) in
/-- info: λ.. x y, f x y : (xs : TT.Arg) → (TU xs).Arg → PROP -/
#guard_msgs in #check (λ.. x y, f x y)

/- Delaboration of `tforall`. -/
/-- info: tforall Φ : PROP -/
#guard_msgs in #check (tforall Φ : PROP)

/- Delaboration of `tforall` with partial application the predicate `P`. -/
variable (P : TT.Arg → TT.Arg → PROP) (x : TT.Arg) in
/-- info: tforall (P x) : PROP -/
#guard_msgs in #check (tforall (P x) : PROP)

/- No delaboration when `pp.notation` is set as `false`. -/
/-- info: tforall fun x => tforall fun y => tforall fun z => P x y z : PROP -/
#guard_msgs in
set_option pp.notation false in
variable (P : TT.Arg → TT.Arg → TT.Arg → PROP) in
#check (tforall fun x => tforall fun y => tforall fun z => P x y z : PROP)

/-
  Nested `texist` should collapse into one binder group.
-/
variable (f : TT.Arg → TT.Arg → TT.Arg → PROP) in
/-- info: iprop(∀.. x y z, f x y z) : PROP -/
#guard_msgs in
#check (tforall (fun x => tforall (fun y => tforall (fun z => f x y z))) : PROP)

/- Delaboration of `texist`. -/
/-- info: texist Φ : PROP -/
#guard_msgs in #check (texist Φ : PROP)

/- Delaboration of `texist` with partial application the predicate `P`. -/
variable (P : TT.Arg → TT.Arg → PROP) (x : TT.Arg) in
/-- info: texist (P x) : PROP -/
#guard_msgs in #check (texist (P x) : PROP)

/-
  Nested `texist` should collapse into one binder group.
-/
variable (f : TT.Arg → TT.Arg → TT.Arg → PROP) in
/-- info: iprop(∃.. x y z, f x y z) : PROP -/
#guard_msgs in
#check (texist (fun x => texist (fun y => texist (fun z => f x y z))) : PROP)

/- Tests `intoForall_tforall`. -/
/-- info: solution: IntoForall iprop(∀.. x, Φ x) fun x => Φ x, new goals: [] -/
#guard_msgs in
#ipm_synth @IntoForall PROP _ iprop(∀.. x, Φ x) (_ : Type) _

/- Tests `intoExists_texist`. -/
/-- info: solution: IntoExists iprop(∃.. x, Φ x) fun x => Φ x, new goals: [] -/
#guard_msgs in
#ipm_synth @IntoExists PROP _ iprop(∃.. x, Φ x) (_ : Type) _

/- Tests `fromForall_tforall_pure`. -/
/-- info:
  solution: FromForall iprop(⌜∀.. x, φ x⌝) fun x => iprop(⌜φ x⌝),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @FromForall PROP _ iprop(⌜∀.. x, φ x⌝) (_ : Type) _

/- Tests `fromForall_pure`. -/
/-- info:
  solution: FromForall iprop(⌜∀ (a : TT.Arg), φ a⌝) fun a => iprop(⌜φ a⌝),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @FromForall PROP _ iprop(⌜∀ x, φ x⌝) (_ : Type) _

/- Tests `fromPure_tforall`. -/
/-- info:
  solution: FromPure false iprop(∀.. x, ⌜φ x⌝) InOut.out (∀.. x, φ x),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @FromPure PROP _ _ iprop(∀.. x, ⌜φ x⌝) .out _

/- Tests `fromPure_tforall`. -/
/-- info:
  solution: FromPure false iprop(∀.. x, ⌜φ x⌝) InOut.in (∀.. x, φ x),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @FromPure PROP _ _ iprop(∀.. x, ⌜φ x⌝) .in (∀.. x, φ x)

/- Tests `intoPure_tforall`. -/
/-- info:
  solution: IntoPure iprop(∀.. x, ⌜φ x⌝) (∀.. x, φ x),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @IntoPure PROP _ iprop(∀.. x, ⌜φ x⌝) _

/- Tests `intoPure_texist`. -/
/-- info:
  solution: IntoPure iprop(∃.. x, ⌜φ x⌝) (∃.. x, φ x),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @IntoPure PROP _ iprop(∃.. x, ⌜φ x⌝) _

/-
  Tests `intoWand_tforall` with both the premise and the conclusion of the wand
  being unknown.
  The metavariable `?x` in `Φ ?x` and `Ψ ?x` becomes a new subgoal.
-/
/-- info:
  solution: IntoWand false false iprop(∀.. x, Φ x -∗ Ψ x) WandMode.unknown (Φ ?_) (Ψ ?_),
  new goals: [?_: TT.Arg]
-/
#guard_msgs (whitespace := lax) in
set_option pp.mvars false in
#ipm_synth @IntoWand PROP _ false false iprop(∀.. x, Φ x -∗ Ψ x) .unknown _ _

/-
  Tests `intoWand_tforall` with known wand conclusion.
  No subgoal involved as the `a` in `Φ a` is pinned.
-/
/-- info:
  solution: IntoWand false false iprop(∀.. x, Φ x -∗ Ψ x)
    (WandMode.matching WandMode.Side.result) (Φ a) (Ψ a),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @IntoWand PROP _ false false iprop(∀.. x, Φ x -∗ Ψ x)
  (.matching .result) _ (Ψ a)

example [BI PROP] {TT : Tele} (Φ Ψ : TT.Arg → PROP) :
    ⊢ (∀.. x, Φ x -∗ Ψ x) -∗ (∃.. x, Φ x) -∗ ∃.. x, Ψ x := by
  iintro Hwand ⟨%x, HΦ⟩
  iexists x
  iapply Hwand $$ HΦ

/- Tests `frame_tforall` and `frame_texist`. -/
/--
  □HR : R
  ∗HΦ : ∀.. x, Φ x
  ∗HΨ : ∃.. y, Ψ y
  ⊢ (∀.. x, Φ x) ∗ ∃.. x, Ψ x
-/
#guard_msgs (trace, substring := true) in
example [BI PROP] {TT : Tele} (R : PROP) (Φ Ψ : TT.Arg → PROP) :
    ⊢ iprop(□ R -∗ (∀.. x, Φ x) -∗ (∃.. y, Ψ y) -∗
            (∀.. x, R ∗ Φ x) ∗ (∃.. y, R ∗ Ψ y)) := by
  iintro #HR HΦ HΨ
  iframe HR
  trace_state
  isplitl [HΦ]
  · iexact HΦ
  · iexact HΨ
