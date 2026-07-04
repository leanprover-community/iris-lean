/-
Copyright (c) 2026 Sebastian Graf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
-- Deliberately not a `module`: non-module importers ignore module-system
-- annotations such as `@[expose]`, so only `opaque` seals `fixpoint` for them.
-- This file checks the seal from such an importer. Since `module`s can only
-- import `module`s, it is not listed in `Iris.Tests`; the `IrisTest` glob
-- builds it.
-- module

import Iris.Algebra.OFE
import Iris.BI.SIProp

/-!
# Regression test: `fixpoint` is opaque to definitional equality

The `example` below attempts `exact k h`, which asks `isDefEq` to unify
`(fixpoint Phi.f P1).holds 24` with `(fixpoint Phi.f P2).holds 24`. Both sides share the
head `fixpoint Phi.f`, so unification compares the arguments; `P1` and `P2` differ, and
since `fixpoint` is a stuck constant the check fails right there, letting `first` fall
through to `trivial` well within the `maxHeartbeats 4000` cap. If `isDefEq` could instead
unfold `fixpoint` into `COFE.compl` of its approximation chain, it would retry the failed
argument comparison by reducing both sides: projecting out `.holds 24` forces 24
iterations of `Phi`, whose body applies the recursive call to two different arguments, so
the reduction tree doubles at every level with a distinct argument on each path. The
defeq cache never hits, and this single failed unification exceeds even the default
heartbeat budget. The low cap turns any reintroduction of that unfolding into a
deterministic failure of this test.

`Phi`'s proof fields are `sorry` (silenced): unification only ever touches the data.
-/

namespace Iris.Tests.FixpointTest

open Iris OFE

set_option warn.sorry false
set_option linter.unusedVariables false

instance : Inhabited SiProp := ⟨SiProp.pure True⟩

/-- A contraction on the hom space whose body applies the recursive call to two different
argument transformations: every path through its unfolding carries a distinct
argument. -/
def Phi : (SiProp -n> SiProp) -c> (SiProp -n> SiProp) where
  f g := ⟨fun P => .and (.later (g (.and P (.later P)))) (.later (g (.and (.later P) P))), sorry⟩
  contractive := sorry

def P1 : SiProp := .pure True
def P2 : SiProp := .pure (True ∧ True)

set_option maxHeartbeats 4000 in
example (k : ((fixpoint Phi.f) P1).holds 24 → True)
    (h : ((fixpoint Phi.f) P2).holds 24) : True := by
  first
  | exact k h -- fails fast: the two `fixpoint` applications differ in their argument
  | trivial

end Iris.Tests.FixpointTest
