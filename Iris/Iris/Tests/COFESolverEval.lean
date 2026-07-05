/-
Copyright (c) 2026 Sebastian Graf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
-- Deliberately not a `module`: since `module`s can only import `module`s, it
-- is not listed in `Iris.Tests`; the `IrisTest` glob builds it.
-- module

import Iris.Algebra.COFESolver

/-!
Regression guard for the runtime cost of the solver's section/retraction pair.

`Fix.Impl.up`/`Fix.Impl.down` are computed by a single recursion producing the
pair at every level, so evaluating either hom at level `k` makes `O(k)`
recursive calls; recomputing the two branches separately at every level makes
that `2^k`.

The `#eval` round-trips a value through level `k = 21` of the tower and reads
back a `Nat` threaded through the `constOF` component, so the hom construction
is demanded at runtime and cannot be erased as dead code. Compiled evaluation
is not subject to `maxHeartbeats`, so the check is a wall-clock budget,
calibrated against a pure baseline computation timed in the same interpreter
so that machine speed cancels out: the healthy path costs a few baseline
units, the exponential path several hundred. The exponential path still
terminates at this depth (in tens of seconds), so a regression fails with the
budget error rather than hanging the build.
-/

namespace Iris.Tests.COFESolverEval

open Iris Iris.COFE Iris.COFE.OFunctor Iris.COFE.OFunctor.Fix.Impl OFE

/-- A functor whose `map` captures both the covariant and the contravariant
hom (via `HomOF`), with a `LeibnizO Nat` payload to read back (via `constOF`).
The capture forces both components of the up/down pair at every level when the
homs are constructed at runtime. -/
abbrev F : ∀ (α β : Type), [COFE α] → [COFE β] → Type :=
  ProdOF (HomOF (LaterOF IdOF) (LaterOF IdOF)) (constOF (LeibnizO Nat))

instance : Inhabited (F (ULift Unit) (ULift Unit)) := ⟨Hom.id, ⟨42⟩⟩

/-- Round-trip the seed value up to level `1 + k` of the tower and back down to
level `1`, returning the `Nat` payload. `k` stays a runtime value, so no
elaboration-time reduction of `A F k` is involved: the cost measured is that of
running the compiled `up`/`down`. -/
def roundTrip (k : Nat) : Nat :=
  let x1 : A F 1 := up F 0 ⟨()⟩
  let xk : A F (1 + k) := upN F (k := 1) k x1
  let y1 : A F 1 := downN F (k := 1) k xk
  (y1 : (Later (ULift Unit) -n> Later (ULift Unit)) × LeibnizO Nat).2.car

#eval show IO Unit from do
  -- Reading these at runtime keeps the round-trip from being lifted out as a
  -- closed term and evaluated before the timestamps.
  let k := ((← IO.getEnv "COFESOLVER_EVAL_DEPTH").bind (·.toNat?)).getD 21
  let n := ((← IO.getEnv "COFESOLVER_EVAL_BASELINE").bind (·.toNat?)).getD 200000
  -- Baseline unit: a pure fold in the same interpreter.
  let b0 ← IO.monoNanosNow
  let base := (List.range n).foldl (· + ·) 0
  unless base == n * (n - 1) / 2 do
    throw <| IO.userError "COFESolverEval: baseline computed a wrong sum"
  let b1 ← IO.monoNanosNow
  -- The measured round-trip.
  let t0 ← IO.monoNanosNow
  let v := roundTrip k
  unless v == 42 do
    throw <| IO.userError s!"COFESolverEval: expected 42, got {v}"
  let t1 ← IO.monoNanosNow
  let baseline := max (b1 - b0) 1
  let ratio := (t1 - t0) / baseline
  if ratio > 20 then
    throw <| IO.userError s!"COFESolverEval: `down F {k}` cost {ratio} baseline \
      units (limit 20); the up/down pair is being recomputed exponentially"
  IO.println s!"COFESolverEval: ok ({ratio} baseline units)"

end Iris.Tests.COFESolverEval
