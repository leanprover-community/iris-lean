/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.BI
public import Iris.Algebra.Frac
public import Iris.ProofMode.SynthInstance
public import Iris.ProofMode.Instances
public import Iris.ProofMode.InstancesMake
public import Iris.ProofMode.NatCancel

@[expose] public section

namespace IrisTest
open Lean Qq Iris BI ProofMode

/- Tests the mvar handling of synth and ipm_synth -/
section mvars
variable (PROP : Type u) [BI PROP]

set_option pp.mvars false

/-- info: None -/
#guard_msgs in
#ipm_synth QuickAbsorbing (PROP:=PROP) _

-- check that ipm_synth does not accidentally instantiate input mvars
/-- info: solution: MakeSep iprop(True) ?_ iprop(True ∗ ?_), new goals: [?_: PROP] -/
#guard_msgs in
#ipm_synth MakeSep (PROP:=PROP) iprop(True) _ _

/-- info: solution: MakeIntuitionistically ?_ iprop(□ ?_), new goals: [?_: PROP] -/
#guard_msgs in
#ipm_synth MakeIntuitionistically (PROP:=PROP) _ _

variable [BIAffine PROP]

/-- info: solution: QuickAbsorbing ?_, new goals: [?_: PROP] -/
#guard_msgs in
#ipm_synth QuickAbsorbing (PROP:=PROP) _

/-- info: solution: MakeSep iprop(True) ?_ ?_, new goals: [?_: PROP] -/
#guard_msgs in
#ipm_synth MakeSep (PROP:=PROP) iprop(True) _ _

end mvars

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
set_option pp.mvars false in
/-- info: solution: IntoWand false false iprop(∀ x, P1 x -∗ P2 x) WandMode.unknown (P1 ?_) (P2 ?_), new goals: [?_: Nat] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(∀ a, P1 a -∗ P2 a) .unknown _ _)

/- Test instantiation of forall quantifier -/
/-- info: solution: IntoWand false false iprop(∀ x, P1 x -∗ P2 x) (WandMode.matching WandMode.Side.argument) (P1 1)
  (P2 1), new goals: [] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(∀ a, P1 a -∗ P2 a) (.matching .argument) (P1 1) _)

/- Test instantiation of mvar created outside ipm_synth -/
/-- info: solution: IntoWand false false iprop(P1 1 -∗ P2 1) (WandMode.matching WandMode.Side.argument) (P1 1)
  (P2 1), new goals: [] -/
#guard_msgs in #ipm_synth (IntoWand false false iprop(P1 _ -∗ P2 1) (.matching .argument) (P1 1) _)

end mvars

section trace

variable [BI PROP] (P1 : PROP)

/--
info: solution: FromAssumption false InOut.out P1 P1, new goals: []
---
trace: [Meta.synthInstance] ✅️ IPM: FromAssumption false InOut.out P1 P1
  [Meta.synthInstance] ✅️ IPM: new goal FromAssumption false InOut.out ?_ P1 => FromAssumption false InOut.out P1 P1
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
  logInfo m!"tac_continue called with {e}"
  return .continue

theorem tactic_test_emp [BI PROP] (P : PROP) : TacticTest iprop(emp ∗ P) P := ⟨sep_elim_right⟩

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
info: tac_continue called with TacticTest iprop(emp ∗ P) ?_
---
info: solution: TacticTest iprop(emp ∗ P) P, new goals: []
---
trace: [Meta.synthInstance] ✅️ IPM: TacticTest iprop(emp ∗ P) P
  [Meta.synthInstance] ✅️ IPM: new goal TacticTest iprop(emp ∗ P) ?_ => TacticTest iprop(emp ∗ P) P
    [Meta.synthInstance.tactics] [IrisTest.tac_sep:1000, IrisTest.tac_emp:1000, IrisTest.tac_continue:10000]
    [Meta.synthInstance] ❌️ apply tactic IrisTest.tac_continue to TacticTest iprop(emp ∗ P) ?_
    [Meta.synthInstance] IrisTest.tac_continue did not find an instance, continue to other instances
    [Meta.synthInstance] ✅️ apply tactic IrisTest.tac_emp to TacticTest iprop(emp ∗ P) ?_
      [Meta.synthInstance] IrisTest.tac_emp success: tactic_test_emp P
  [Meta.synthInstance] result tactic_test_emp P
-/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (TacticTest iprop(emp ∗ P) _)

/--
info: tac_continue called with TacticTest iprop((emp ∗ P) ∗ P) ?_
---
info: tac_continue called with TacticTest iprop(emp ∗ P) ?_
---
info: solution: TacticTest iprop((emp ∗ P) ∗ P) iprop(P ∗ P), new goals: []
---
trace: [Meta.synthInstance] ✅️ IPM: TacticTest iprop((emp ∗ P) ∗ P) iprop(P ∗ P)
  [Meta.synthInstance] ✅️ IPM: new goal TacticTest iprop((emp ∗ P) ∗ P)
        ?_ => TacticTest iprop((emp ∗ P) ∗ P) iprop(P ∗ P)
    [Meta.synthInstance.tactics] [IrisTest.tac_sep:1000, IrisTest.tac_continue:10000]
    [Meta.synthInstance] ❌️ apply tactic IrisTest.tac_continue to TacticTest iprop((emp ∗ P) ∗ P) ?_
    [Meta.synthInstance] IrisTest.tac_continue did not find an instance, continue to other instances
    [Meta.synthInstance] ✅️ apply tactic IrisTest.tac_sep to TacticTest iprop((emp ∗ P) ∗ P) ?_
      [Meta.synthInstance] ✅️ IPM: new goal TacticTest iprop(emp ∗ P) ?_ => TacticTest iprop(emp ∗ P) P
        [Meta.synthInstance.tactics] [IrisTest.tac_sep:1000, IrisTest.tac_emp:1000, IrisTest.tac_continue:10000]
        [Meta.synthInstance] ❌️ apply tactic IrisTest.tac_continue to TacticTest iprop(emp ∗ P) ?_
        [Meta.synthInstance] IrisTest.tac_continue did not find an instance, continue to other instances
        [Meta.synthInstance] ✅️ apply tactic IrisTest.tac_emp to TacticTest iprop(emp ∗ P) ?_
          [Meta.synthInstance] IrisTest.tac_emp success: tactic_test_emp P
      [Meta.synthInstance] IrisTest.tac_sep success: tactic_test_sep iprop(emp ∗ P) P P (tactic_test_emp P)
  [Meta.synthInstance] result tactic_test_sep iprop(emp ∗ P) P P (tactic_test_emp P)
-/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (TacticTest iprop((emp ∗ P) ∗ P) _)

/--
info: tac_continue called with TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) ?_
---
info: tac_continue called with TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P) (?_ a)
---
info: tac_continue called with TacticTest iprop(emp ∗ ⌜a = 5⌝) ?_
---
info: solution: TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) iprop(∀ a, ⌜a = 5⌝ ∗ P), new goals: []
---
trace: [Meta.synthInstance] ✅️ IPM: TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) iprop(∀ a, ⌜a = 5⌝ ∗ P)
  [Meta.synthInstance] ✅️ IPM: new goal TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P)
        ?_ => TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) iprop(∀ a, ⌜a = 5⌝ ∗ P)
    [Meta.synthInstance.tactics] [IrisTest.tac_continue:10000]
    [Meta.synthInstance] ❌️ apply tactic IrisTest.tac_continue to TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) ?_
    [Meta.synthInstance] IrisTest.tac_continue did not find an instance, continue to other instances
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
      [Meta.synthInstance] ✅️ IPM: new goal ∀ (a : Nat),
            TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P)
              (?_ a) => ∀ (a : Nat), TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P) iprop(⌜a = 5⌝ ∗ P)
        [Meta.synthInstance.tactics] [IrisTest.tac_sep:1000, IrisTest.tac_continue:10000]
        [Meta.synthInstance] ❌️ apply tactic IrisTest.tac_continue to ∀ (a : Nat),
              TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P) (?_ a)
        [Meta.synthInstance] IrisTest.tac_continue did not find an instance, continue to other instances
        [Meta.synthInstance] ✅️ apply tactic IrisTest.tac_sep to ∀ (a : Nat),
              TacticTest iprop((emp ∗ ⌜a = 5⌝) ∗ P) (?_ a)
          [Meta.synthInstance] ✅️ IPM: new goal TacticTest iprop(emp ∗ ⌜a = 5⌝)
                ?_ => TacticTest iprop(emp ∗ ⌜a = 5⌝) iprop(⌜a = 5⌝)
            [Meta.synthInstance.tactics] [IrisTest.tac_sep:1000, IrisTest.tac_emp:1000, IrisTest.tac_continue:10000]
            [Meta.synthInstance] ❌️ apply tactic IrisTest.tac_continue to TacticTest iprop(emp ∗ ⌜a = 5⌝) ?_
            [Meta.synthInstance] IrisTest.tac_continue did not find an instance, continue to other instances
            [Meta.synthInstance] ✅️ apply tactic IrisTest.tac_emp to TacticTest iprop(emp ∗ ⌜a = 5⌝) ?_
              [Meta.synthInstance] IrisTest.tac_emp success: tactic_test_emp iprop(⌜a = 5⌝)
          [Meta.synthInstance] IrisTest.tac_sep success: tactic_test_sep iprop(emp ∗ ⌜a = 5⌝) iprop(⌜a = 5⌝) P
                (tactic_test_emp iprop(⌜a = 5⌝))
  [Meta.synthInstance] result tactic_test_all (fun a => iprop((emp ∗ ⌜a = 5⌝) ∗ P)) fun a => iprop(⌜a = 5⌝ ∗ P)
-/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (TacticTest iprop(∀ a, (emp ∗ ⌜a = 5⌝) ∗ P) _)

/--
info: tac_continue called with TacticTest iprop(True) ?_
---
info: None
---
trace: [Meta.synthInstance] ❌️ IPM: TacticTest iprop(True) ?_
  [Meta.synthInstance] ❌️ IPM: new goal TacticTest iprop(True) ?_ => TacticTest iprop(True) ?_
    [Meta.synthInstance.tactics] [IrisTest.tac_fail:100, IrisTest.tac_continue:10000]
    [Meta.synthInstance] ❌️ apply tactic IrisTest.tac_continue to TacticTest iprop(True) ?_
    [Meta.synthInstance] IrisTest.tac_continue did not find an instance, continue to other instances
    [Meta.synthInstance] ❌️ apply tactic IrisTest.tac_fail to TacticTest iprop(True) ?_
    [Meta.synthInstance] IrisTest.tac_fail failed, no backtracking to other instances
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
set_option pp.mvars false in
#ipm_synth (TacticTest (PROP:=PROP) iprop(True) _)


end tactics

section issue_456

-- test for https://github.com/leanprover-community/iris-lean/issues/456

@[ipm_class]
class C (io : InOut) (a : semiOutParamIPM io Nat) (b : semiOutParamIPM io.negate Nat) : Prop where

abbrev CMerge (a b : Nat) := C .out a b

abbrev CSplit (a b : Nat) := C .in a b

set_option synthInstance.checkSynthOrder false in
instance instMerge (b : Nat) : CMerge (b + 1) b := ⟨⟩

set_option synthInstance.checkSynthOrder false in
instance instSplit (k : Nat) : CSplit (k + 1) k := ⟨⟩

-- should not cause an index out of bounds exception
/-- info: solution: CMerge (?m.4 + 1) ?m.4, new goals: [?m.4: Nat] -/
#guard_msgs in
#ipm_synth CMerge _ _

-- should fail input check and thus result in None
/-- info: None -/
#guard_msgs in
#ipm_synth CSplit _ _

end issue_456

section semiOutParam

/-- error: invalid ipm_class, `semiOutParam` used directly in parameter #2. Use `semiOutParamIPM` instead -/
#guard_msgs in
@[ipm_class]
class C1 (io : InOut) (a : semiOutParam Nat) : Prop where

/-- Tests `semiOutParamIPM` where the `InOut` value depends on another argument by pattern matching. -/
@[ipm_class]
class C2 (a : Bool) (a : semiOutParamIPM (match a with | false => .in | true => .out) Nat) : Prop where

/-- Tests `semiOutParamIPM` where the `InOut` value depends on another argument by conditional branching. -/
@[ipm_class]
class C3 (a : Bool) (a : semiOutParamIPM (if a then .in else .out) Nat) : Prop where

/- The attribute `semiOutParam` is still relevant for regular type classes  -/
class C4 (io : InOut) (a : semiOutParam Nat) : Prop where

/-- error: invalid ipm_class, `semiOutParamCore` used directly in parameter #2. Use `semiOutParamIPM` instead -/
#guard_msgs in
@[ipm_class]
class C5 (io : InOut) (a : semiOutParamCore .in Nat) : Prop where

end semiOutParam

section NatCancel

variable (m n p q : Nat)

/- Cancellation of `1` on both sides, with the numeral in a rightmost position. -/
/-- info: solution: NatCancel (m + n + 1) 1 (m + n) 0 false, new goals: [] -/
#guard_msgs in
#ipm_synth (NatCancel (m + n + 1) 1 _ _ _)

/- Cancellation of `1` on both sides, with the numeral in a middle position. -/
/-- info: solution: NatCancel (m + 1 + n) 1 (m + n) 0 false, new goals: [] -/
#guard_msgs in
#ipm_synth (NatCancel (m + 1 + n) 1 _ _ _)

/- Cancellation of `1` on both sides, with the numeral in a leftmost position. -/
/-- info: solution: NatCancel 1 (m + n + 1) 0 (m + n) false, new goals: [] -/
#guard_msgs in
#ipm_synth (NatCancel 1 (m + n + 1) _ _ _)

/- Cancellation of a variable `n` on both sides. -/
/-- info: solution: NatCancel (m + n) n m 0 false, new goals: [] -/
#guard_msgs in
#ipm_synth (NatCancel (m + n) n _ _ _)

/- Cancellation of multiple variables on both sides. -/
/-- info: solution: NatCancel (m + (3 + (p + n))) (p + q + 2) (m + (1 + n)) q false, new goals: [] -/
#guard_msgs in
#ipm_synth (NatCancel (m + (3 + (p + n))) (p + q + 2) _ _ _)

/- Cancellation of zero, leaving both sides unchanged. -/
/-- info: solution: NatCancel (m + n) 0 (m + n) 0 true, new goals: [] -/
#guard_msgs in
#ipm_synth (NatCancel (m + n) 0 _ _ _)

/- Cancellation of `3` on both sides, with separated numerals on one side.  -/
/-- info: solution: NatCancel (1 + m + 2) 3 m 0 false, new goals: [] -/
#guard_msgs in
#ipm_synth (NatCancel (1 + m + 2) 3 _ _ _)

end NatCancel

section IsOp
open Iris CMRA ProofMode

variable (q q1 q2 : Qp)

/- Splitting a sum: `isOpFrac_split` is used instead of `isOpFrac_half`. -/
/-- info:
  solution: IsOp IsOp.Direction.split (q1 + q2) q1 q2,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IsOp .split (q1 + q2 : Qp) _ _

/- Splitting a CMRA operation: `isOpFrac_split` is used instead of `isOpFrac_half`. -/
/-- info:
  solution: IsOp IsOp.Direction.split (q1 • q2) q1 q2,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IsOp .split (q1 • q2) _ _

/- Splitting a `Qp` value, where `isOpFrac_split` is not applicable: use `isOpFrac_half`. -/
/-- info:
  solution: IsOp IsOp.Direction.split q q.half q.half,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IsOp .split q _ _

/- Merging two `Qp` values: `isOpFrac_half` is not applicable, use `isOpFrac_merge`. -/
/-- info:
  solution: IsOp IsOp.Direction.merge (q1 + q2) q1 q2,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IsOp .merge _ q1 q2

/- Merging two `Qp` values: `isOpFrac_half` is applicable and preferred for eliminating `.half`. -/
/-- info:
  solution: IsOp IsOp.Direction.merge q q.half q.half,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IsOp .merge _ q.half q.half

/-
  Splitting a pair:
  `isOp_pair`, `isOp_pair_core_id_l`, `isOp_pair_core_id_r` and `isOp_some` are used.
  Backtracking is involved after `isOp_pair_core_id_r` fails to split the second
  half of the pair.
-/
/-- info:
  solution: IsOp IsOp.Direction.split (some (q, q1 + q2)) (some (q.half, q1)) (some (q.half, q2)),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IsOp .split (some (q, q1 + q2)) _ _

/-
  Merging `Qp.quarter` and `Qp.threeQuarters`:
  `isOpFrac_quarters_left` and `isOpFrac_quarters_right` take precedence over `isOpFrac_merge`.
-/
/-- info:
  solution: IsOp IsOp.Direction.merge (One.one, One.one)
    (Qp.quarter, Qp.threeQuarters) (Qp.threeQuarters, Qp.quarter),
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IsOp .merge _ (Qp.quarter, Qp.threeQuarters) (Qp.threeQuarters, Qp.quarter)

/-
  Split `Qp.one`: `isOpFrac_half` takes precedence over
  `isOpFrac_quarters_left`/`isOpFrac_quarters_right`.
-/
/-- info:
  solution: IsOp IsOp.Direction.split One.one One.one.half One.one.half,
  new goals: []
-/
#guard_msgs (whitespace := lax) in
#ipm_synth IsOp .split instQpOne.one _ _

end IsOp
