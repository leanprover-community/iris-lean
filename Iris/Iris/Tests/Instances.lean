/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.BI
public import Iris.ProofMode.SynthInstance
public import Iris.ProofMode.Instances

@[expose] public section

namespace Iris.Tests
open Lean Qq BI ProofMode

/- Test the backtracking of ipm_synth -/
section backtracking

variable [BI PROP] (P1 P2 Q : PROP) [FromAssumption p .in P1 Q] [FromAssumption p .in P2 Q]

/- Test backtracking with both options. IPM backtracking search will search for right conjuncts before
left conjuncts, because `fromAssumption_and_r` is declared after `fromAssumption_and_l`.
This is the same behavior as regular typeclass search. -/
/-- info: solution: FromAssumption p InOut.in iprop(P1 ∧ P2) Q, new goals: [] -/
#guard_msgs in #ipm_synth (FromAssumption p .in iprop(P1 ∧ P2) Q)

/- Test backtracking picking the left conjunct. -/
/-- info: solution: FromAssumption p InOut.in iprop(P1 ∧ P2) P1, new goals: [] -/
#guard_msgs in #ipm_synth (FromAssumption p .in iprop(P1 ∧ P2) P1)

/- Test backtracking picking the right conjunct. -/
/-- info: solution: FromAssumption p InOut.in iprop(P1 ∧ P2) P2, new goals: [] -/
#guard_msgs in #ipm_synth (FromAssumption p .in iprop(P1 ∧ P2) P2)

end backtracking

/- Test creation and instantiation of mvars using of ipm_synth -/
section mvars

variable [BI PROP] (P1 P2 : Nat → PROP)

/- Test creation of mvars -/
/-- info: solution: IntoWand false false iprop(∀ x, P1 x -∗ P2 x) InOut.out (P1 ?m.24) InOut.out
  (P2 ?m.24), new goals: [?m.24: Nat] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(∀ a, P1 a -∗ P2 a) .out _ .out _)

/- Test instantiation of forall quantifier -/
/-- info: solution: IntoWand false false iprop(∀ x, P1 x -∗ P2 x) InOut.in (P1 1) InOut.out (P2 1), new goals: [] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(∀ a, P1 a -∗ P2 a) .in (P1 1) .out _)

/- Test instantiation of mvar created outside ipm_synth -/
/-- info: solution: IntoWand false false iprop(P1 1 -∗ P2 1) InOut.in (P1 1) InOut.out (P2 1), new goals: [] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(P1 _ -∗ P2 1) .in (P1 1) .out _)

end mvars

section trace

variable [BI PROP] (P1 : PROP)

/--
info: solution: FromAssumption false InOut.out P1 P1, new goals: []
---
trace: [Meta.synthInstance] ✅️ IPM: FromAssumption false InOut.out P1 P1
  [Meta.synthInstance] ✅️ new goal FromAssumption false InOut.out ?_ P1 => FromAssumption false InOut.out P1 P1
    [Meta.synthInstance.tactics] []
    [Meta.synthInstance.instances] #[@fromAssumption_exact]
    [Meta.synthInstance] ✅️ apply @fromAssumption_exact to FromAssumption false InOut.out ?_ P1
      [Meta.synthInstance.tryResolve] ✅️ FromAssumption false InOut.out P1 P1 ≟ FromAssumption false InOut.out P1 P1
      [Meta.synthInstance] ✅️ switch to normal synthInstance
        [Meta.synthInstance] ✅️ BI PROP
          [Meta.synthInstance] ✅️ new goal BI PROP
            [Meta.synthInstance.instances] #[@Sbi.toBI, inst✝]
          [Meta.synthInstance.apply] ✅️ apply inst✝ to BI PROP
            [Meta.synthInstance.tryResolve] ✅️ BI PROP ≟ BI PROP
            [Meta.synthInstance.answer] ✅️ BI PROP
          [Meta.synthInstance] result inst✝
  [Meta.synthInstance] result fromAssumption_exact false InOut.out P1
---
trace: [Meta.synthInstance] ✅️ BI PROP
  [Meta.synthInstance] ✅️ new goal BI PROP
    [Meta.synthInstance.instances] #[@Sbi.toBI, inst✝]
  [Meta.synthInstance.apply] ✅️ apply inst✝ to BI PROP
    [Meta.synthInstance.tryResolve] ✅️ BI PROP ≟ BI PROP
    [Meta.synthInstance.answer] ✅️ BI PROP
  [Meta.synthInstance] result inst✝
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (FromAssumption false .out _ P1)

end trace

meta section tactics

@[ipm_class]
class TacticTest [BI PROP] (P : PROP) (Q : outParam PROP) where
  tactic_test : P ⊢ Q

@[ipm_tactic_instance:high TacticTest _ _]
def tac_continue : SynthTactic := λ e => do
  logInfo m!"tac_continue called wit {e}"
  return .continue

theorem tactic_test_emp [BI PROP] (P : PROP) : TacticTest iprop(emp ∗ P) P := ⟨sep_elim_r⟩

@[ipm_tactic_instance TacticTest iprop(emp ∗ _) _]
def tac_emp : SynthTactic := λ e => do
  let_expr TacticTest prop bi P _ := e | return .continue
  have u := e.getAppFn.constLevels![0]!
  have prop : Q(Type u) := prop
  have _bi : Q(BI $prop) := bi
  let_expr BI.sep _ _ E Q := P | return .continue
  let_expr BI.emp _ _ := E | return .continue
  have Q : Q($prop) := Q
  return .success q(tactic_test_emp $Q)

theorem tactic_test_sep [BI PROP] (P P' Q : PROP) :
  TacticTest P P' →
  TacticTest iprop(P ∗ Q) iprop(P' ∗ Q) := λ h => ⟨sep_mono h.1 .rfl⟩

@[ipm_tactic_instance TacticTest iprop(_ ∗ _) _]
def tac_sep : SynthTactic := λ e => do
  let_expr TacticTest prop bi S _ := e | return .continue
  have u := e.getAppFn.constLevels![0]!
  have prop : Q(Type u) := prop
  have _bi : Q(BI $prop) := bi
  let_expr BI.sep _ _ P Q := S | return .continue
  have P : Q($prop) := P
  have Q : Q($prop) := Q
  let P' : Q($prop) ← mkFreshExprMVarQ q($prop)
  let .some pf ← synthInstanceRecursiveQ q(TacticTest $P $P') | return .continue
  return .success q(tactic_test_sep $P $P' $Q $pf)

instance tactic_test_all {α} [BI PROP] (P P' : α → PROP)
  [h : ∀ a, TacticTest (P a) (P' a)] :
  TacticTest iprop(∀ a, P a) iprop(∀ a, P' a) :=
  ⟨forall_mono (λ a => (h a).1)⟩

-- Tests failing and multiple patterns
@[ipm_tactic_instance:low TacticTest iprop(False) _, TacticTest iprop(True) _]
def tac_fail : SynthTactic := λ _ => return .fail

variable {PROP} [BI PROP] (P : PROP)

/--
info: tac_continue called wit TacticTest iprop(emp ∗ P) ?_
---
info: solution: TacticTest iprop(emp ∗ P) P, new goals: []
---
trace: [Meta.synthInstance] ✅️ IPM: TacticTest iprop(emp ∗ P) P
  [Meta.synthInstance] ✅️ new goal TacticTest iprop(emp ∗ P) ?_ => TacticTest iprop(emp ∗ P) P
    [Meta.synthInstance.tactics] [Iris.Tests.tac_sep:1000, Iris.Tests.tac_emp:1000, Iris.Tests.tac_continue:10000]
    [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_continue to TacticTest iprop(emp ∗ P) ?_
    [Meta.synthInstance] Iris.Tests.tac_continue did not find an instance, continue to other instances
    [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_emp to TacticTest iprop(emp ∗ P) ?_
      [Meta.synthInstance] Iris.Tests.tac_emp success: tactic_test_emp P
  [Meta.synthInstance] result tactic_test_emp P
-/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (TacticTest iprop(emp ∗ P) _)

/--
info: tac_continue called wit TacticTest iprop((emp ∗ P) ∗ P) ?_
---
info: tac_continue called wit TacticTest iprop(emp ∗ P) ?_
---
info: solution: TacticTest iprop((emp ∗ P) ∗ P) iprop(P ∗ P), new goals: []
---
trace: [Meta.synthInstance] ✅️ IPM: TacticTest iprop((emp ∗ P) ∗ P) iprop(P ∗ P)
  [Meta.synthInstance] ✅️ new goal TacticTest iprop((emp ∗ P) ∗ P) ?_ => TacticTest iprop((emp ∗ P) ∗ P) iprop(P ∗ P)
    [Meta.synthInstance.tactics] [Iris.Tests.tac_sep:1000, Iris.Tests.tac_continue:10000]
    [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_continue to TacticTest iprop((emp ∗ P) ∗ P) ?_
    [Meta.synthInstance] Iris.Tests.tac_continue did not find an instance, continue to other instances
    [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_sep to TacticTest iprop((emp ∗ P) ∗ P) ?_
      [Meta.synthInstance] ✅️ new goal TacticTest iprop(emp ∗ P) ?_ => TacticTest iprop(emp ∗ P) P
        [Meta.synthInstance.tactics] [Iris.Tests.tac_sep:1000, Iris.Tests.tac_emp:1000, Iris.Tests.tac_continue:10000]
        [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_continue to TacticTest iprop(emp ∗ P) ?_
        [Meta.synthInstance] Iris.Tests.tac_continue did not find an instance, continue to other instances
        [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_emp to TacticTest iprop(emp ∗ P) ?_
          [Meta.synthInstance] Iris.Tests.tac_emp success: tactic_test_emp P
      [Meta.synthInstance] Iris.Tests.tac_sep success: tactic_test_sep iprop(emp ∗ P) P P (tactic_test_emp P)
  [Meta.synthInstance] result tactic_test_sep iprop(emp ∗ P) P P (tactic_test_emp P)
-/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (TacticTest iprop((emp ∗ P) ∗ P) _)

/--
info: tac_continue called wit TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) ?_
---
info: tac_continue called wit TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P) (?_ a)
---
info: tac_continue called wit TacticTest iprop(emp ∗ ⌜a = 5⌝) ?_
---
info: solution: TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) iprop(∀ a, ⌜a = 5⌝ ∗ P), new goals: []
---
trace: [Meta.synthInstance] ✅️ IPM: TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) iprop(∀ a, ⌜a = 5⌝ ∗ P)
  [Meta.synthInstance] ✅️ new goal TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P)
        ?_ => TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) iprop(∀ a, ⌜a = 5⌝ ∗ P)
    [Meta.synthInstance.tactics] [Iris.Tests.tac_continue:10000]
    [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_continue to TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) ?_
    [Meta.synthInstance] Iris.Tests.tac_continue did not find an instance, continue to other instances
    [Meta.synthInstance.instances] #[@tactic_test_all]
    [Meta.synthInstance] ✅️ apply @tactic_test_all to TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) ?_
      [Meta.synthInstance.tryResolve] ✅️ TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P)
            iprop(∀ a, ?_ a) ≟ TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) iprop(∀ a, ?_ a)
      [Meta.synthInstance] ✅️ switch to normal synthInstance
        [Meta.synthInstance] ✅️ BI PROP
          [Meta.synthInstance] ✅️ new goal BI PROP
            [Meta.synthInstance.instances] #[@Sbi.toBI, inst✝]
          [Meta.synthInstance.apply] ✅️ apply inst✝ to BI PROP
            [Meta.synthInstance.tryResolve] ✅️ BI PROP ≟ BI PROP
            [Meta.synthInstance.answer] ✅️ BI PROP
          [Meta.synthInstance] result inst✝
      [Meta.synthInstance] ✅️ new goal ∀ (a : Nat),
            TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P)
              (?_ a) => ∀ (a : Nat), TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P) iprop(⌜a = 5⌝ ∗ P)
        [Meta.synthInstance.tactics] [Iris.Tests.tac_sep:1000, Iris.Tests.tac_continue:10000]
        [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_continue to ∀ (a : Nat),
              TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P) (?_ a)
        [Meta.synthInstance] Iris.Tests.tac_continue did not find an instance, continue to other instances
        [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_sep to ∀ (a : Nat),
              TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P) (?_ a)
          [Meta.synthInstance] ✅️ new goal TacticTest iprop(emp ∗ ⌜a = 5⌝)
                ?_ => TacticTest iprop(emp ∗ ⌜a = 5⌝) iprop(⌜a = 5⌝)
            [Meta.synthInstance.tactics] [Iris.Tests.tac_sep:1000,
                 Iris.Tests.tac_emp:1000,
                 Iris.Tests.tac_continue:10000]
            [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_continue to TacticTest iprop(emp ∗ ⌜a = 5⌝) ?_
            [Meta.synthInstance] Iris.Tests.tac_continue did not find an instance, continue to other instances
            [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_emp to TacticTest iprop(emp ∗ ⌜a = 5⌝) ?_
              [Meta.synthInstance] Iris.Tests.tac_emp success: tactic_test_emp iprop(⌜a = 5⌝)
          [Meta.synthInstance] Iris.Tests.tac_sep success: tactic_test_sep iprop(emp ∗ ⌜a = 5⌝) iprop(⌜a = 5⌝) P
                (tactic_test_emp iprop(⌜a = 5⌝))
  [Meta.synthInstance] result tactic_test_all (fun a => iprop((emp ∗ ⌜a = 5⌝) ∗ P)) fun a => iprop(⌜a = 5⌝ ∗ P)
-/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) _)

/--
info: tac_continue called wit TacticTest iprop(True) ?_
---
info: None
---
trace: [Meta.synthInstance] ❌️ IPM: TacticTest iprop(True) ?_
  [Meta.synthInstance] ❌️ new goal TacticTest iprop(True) ?_ => TacticTest iprop(True) ?_
    [Meta.synthInstance.tactics] [Iris.Tests.tac_fail:100, Iris.Tests.tac_continue:10000]
    [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_continue to TacticTest iprop(True) ?_
    [Meta.synthInstance] Iris.Tests.tac_continue did not find an instance, continue to other instances
    [Meta.synthInstance] ✅️ apply tactic Iris.Tests.tac_fail to TacticTest iprop(True) ?_
    [Meta.synthInstance] Iris.Tests.tac_fail failed, no backtracking to other instances
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (TacticTest iprop(True) _)


end tactics
