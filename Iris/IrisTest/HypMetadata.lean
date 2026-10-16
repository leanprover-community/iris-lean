/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.ProofMode

/-!
# `rw` must not erase the name annotations of Iris hypotheses

Regression tests for https://github.com/leanprover-community/iris-lean/issues/469
(fixed by https://github.com/leanprover-community/iris-lean/pull/506).

The goals are printed with `pp.mdata` and with the proof mode display (`pp.iris.goal`) turned off, so the
annotations are visible.
-/

set_option pp.mdata true
set_option pp.iris.goal false

namespace IrisTest.HypMetadata
open Iris BI ProofMode

variable [BI PROP] (P Q R : PROP) (F : Nat → PROP)

/- `rw` whose left-hand side is a whole hypothesis. -/
/-- mdata name:H -/
#guard_msgs (substring := true) in
example (h : F 0 = Q) : F 0 ⊢ Q := by
  iintro H
  rw [h]
  trace_state
  iexact H

def ifZero (n : Nat) (P Q : PROP) : PROP :=
  match n with
  | 0 => P
  | _ + 1 => Q

/- `rw [_.eq_def]` then `simp only` reducing the `match` (the shape from #469 / `Quicksort.lean`). -/
/-- mdata name:H -/
#guard_msgs (substring := true) in
example : ifZero 0 P Q ⊢ P := by
  iintro H
  rw [ifZero.eq_def]
  simp only
  trace_state
  iexact H

end IrisTest.HypMetadata
