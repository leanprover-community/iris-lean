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
# Tests for the Banach fixpoint

The first section exercises the `fixpoint` API on a constant contraction.

The second section guards the definitional-equality behavior of `fixpoint`. The final
`example` elaborates a failing-then-recovering unification between two applications of a
fixpoint on the hom space `SiProp -n> SiProp` to different arguments. With `fixpoint` a
stuck constant, the mismatch is detected at the arguments and the tactic falls through to
`trivial` well within the `maxHeartbeats 4000` cap. An `isDefEq` that descends into the
approximation chain has to reduce both applications all the way to their `True`-leaf
trees before it can compare them: the two recursive-call arguments of `Phi` give every
path through the unfolding a distinct argument, so caching cannot collapse the descent,
and at index 24 it exceeds even the default heartbeat budget. The cap turns any
reintroduction of chain descent into a deterministic timeout.

`Phi`'s proof fields are `sorry` (silenced): unification only ever touches the data.
-/

namespace Iris.Tests.FixpointTest

open Iris OFE

set_option warn.sorry false
set_option linter.unusedVariables false

/-! ## The `fixpoint` API -/

instance : Inhabited (LeibnizO Nat) := ⟨⟨0⟩⟩

/-- The simplest contraction on a discrete COFE: a constant map. -/
def K : LeibnizO Nat -c> LeibnizO Nat := Function.toContractiveHom fun _ => ⟨42⟩

example : K.fixpoint ≡ K K.fixpoint := fixpoint_unfold K

example : (⟨42⟩ : LeibnizO Nat) ≡ K.fixpoint := fixpoint_unique (f := K) .rfl

example {n} {f g : LeibnizO Nat -c> LeibnizO Nat} (h : f ≡{n}≡ g) :
    f.fixpoint ≡{n}≡ g.fixpoint :=
  OFE.ContractiveHom.fixpoint_ne.ne h

/-- The unbundled form, with the `Contractive` instance found by instance search. -/
example : fixpoint (fun _ => (⟨42⟩ : LeibnizO Nat)) ≡ ⟨42⟩ :=
  (fixpoint_unique (f := K) .rfl).symm

/-! ## Sealing of the approximation chain -/

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
example (g : ((fixpoint Phi.f) P1).holds 24 → True)
    (h : ((fixpoint Phi.f) P2).holds 24) : True := by
  first
  | exact g h -- stumbles: the two `fixpoint` applications differ in their argument
  | trivial

end Iris.Tests.FixpointTest
