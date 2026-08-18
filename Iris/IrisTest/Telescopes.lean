/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.ProofMode.Instances
public import Iris.Std.Telescopes
public import Iris.BI.Telescopes

@[expose] public section

namespace IrisTest
open Iris BI ProofMode Std

variable {PROP : Type} [BI PROP] {TT : Tele.{0}}
  (Φ Ψ : TT.Arg → PROP) (φ : TT.Arg → Prop) (a : TT.Arg)

/- Tests `intoForall_tforall`. -/
/-- info: solution: IntoForall (tforall Φ) Φ, new goals: [] -/
#guard_msgs in
#ipm_synth @IntoForall PROP _ (tforall Φ) (_ : Type) _

/- Tests `intoExists_texist`. -/
/-- info: solution: IntoExists (texist Φ) Φ, new goals: [] -/
#guard_msgs in
#ipm_synth @IntoExists PROP _ (texist Φ) (_ : Type) _

/- Tests `fromForall_tforall_pure`. -/
/-- info:
  solution: FromForall iprop(⌜Tele.tforall φ⌝) fun x => iprop(⌜φ x⌝),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @FromForall PROP _ iprop(⌜Tele.tforall φ⌝) (_ : Type) _

/- Tests `fromForall_pure`. -/
/-- info:
  solution: FromForall iprop(⌜∀ (a : TT.Arg), φ a⌝) fun a => iprop(⌜φ a⌝),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @FromForall PROP _ iprop(⌜∀ x, φ x⌝) (_ : Type) _

/- Tests `fromPure_tforall`. -/
/-- info:
  solution: FromPure false iprop(∀.. x, ⌜φ x⌝) InOut.out (Tele.tforall φ),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @FromPure PROP _ _ (tforall fun x => iprop(⌜φ x⌝)) .out _

/- Tests `fromPure_tforall`. -/
/-- info:
  solution: FromPure false iprop(∀.. x, ⌜φ x⌝) InOut.in (Tele.tforall φ),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @FromPure PROP _ _ (tforall fun x => iprop(⌜φ x⌝)) .in (Tele.tforall φ)

/- Tests `intoPure_tforall`. -/
/-- info:
  solution: IntoPure iprop(∀.. x, ⌜φ x⌝) (Tele.tforall φ),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @IntoPure PROP _ (tforall fun x => iprop(⌜φ x⌝)) _

/- Tests `intoPure_texist`. -/
/-- info:
  solution: IntoPure iprop(∃.. x, ⌜φ x⌝) (Tele.texist φ),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth @IntoPure PROP _ (texist fun x => iprop(⌜φ x⌝)) _

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
#ipm_synth @IntoWand PROP _ false false (tforall fun x => iprop(Φ x -∗ Ψ x)) .unknown _ _

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
#ipm_synth @IntoWand PROP _ false false (tforall fun x => iprop(Φ x -∗ Ψ x))
  (.matching .result) _ (Ψ a)

example [BI PROP] {TT : Tele} (Φ Ψ : TT.Arg → PROP) :
    ⊢ (∀.. x, Φ x -∗ Ψ x) -∗ (∃.. x, Φ x) -∗ ∃.. x, Ψ x := by
  iintro Hwand ⟨%x, HΦ⟩
  iexists x
  iapply Hwand $$ HΦ
