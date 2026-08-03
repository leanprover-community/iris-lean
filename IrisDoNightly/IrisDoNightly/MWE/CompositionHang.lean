module

public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

/-!
# MWE for `vcgen`: composing two `@[spec]` function calls hangs

**Context.** HeapLang-on-`Std.Internal.Do`. A function `incByte := λ n, n + 1` has a spec
`incByte_spec : True ⊑ wp⟦incByte (lit n)⟧ (fun v => v = lit (n+1))`, registered `@[spec]` at
priority above `spec_beta` (so `vcgen` applies the spec instead of unfolding the body).

**Works.** A SINGLE call closes with plain `vcgen` — it applies `incByte_spec` (postcondition matches
the goal's exactly, so no framing is needed):

    example : True ⊑ wp⟦incByte (lit n)⟧ (fun v => v = lit (n+1)) := by vcgen   -- ✓

**Hangs.** The NESTED composition does NOT terminate under `vcgen` (not even with a
`maxHeartbeats` bound — it is a loop `vcgen` does not heartbeat-check):

    example : True ⊑ wp⟦incByte (incByte (lit n))⟧ (fun v => v = lit (n+2)) := by vcgen   -- ⟳

Here the inner `incByte (lit n)` is in ARGUMENT position, so after `spec_appR` focuses it the goal is
`wp⟦incByte (lit n)⟧ (fun v => wp⟦incByte (ofVal v)⟧ Φ)` — the continuation differs from
`incByte_spec`'s fixed postcondition `fun v => v = lit (n+1)`, so applying the spec here requires
FRAMING it (via `wp_mono`/`SPred` entailment) rather than a direct match. That framing step is where
`vcgen` diverges.

**Why it matters.** This is the "just `vcgen`" case — composing already-specified functions with no
body to step (round-trips, wrappers, helper call sites). It should be `vcgen`'s sweet spot.

**Requested (targeted).** Make `vcgen` frame a `pre ⊑ wp prog Q` spec at a call site whose
continuation differs from `Q`, without diverging — i.e. the nested-composition case should behave
like the single-call case.

The hanging example is left commented so this file builds.

**RESOLVED (update).** Stating the spec in continuation-passing form — `Φ (lit (n+1)) ⊑ wp⟦incByte (lit
n)⟧ Φ` with `Φ` a *variable* (like `spec_val`/`spec_beta`) instead of the closed `True ⊑ wp e
(·=lit(n+1))` — makes the nested composition go through as PURE `vcgen` (+ a trivial arithmetic
`grind`), no framing, no hang: see `Codec/AutoTest.lean` (`incByte_cps`, and the round-trip
`dec1 (incByte n) = n`). So this is a "use CPS specs" answer, not a framework gap. The residual note
for Sebastian is only robustness: `vcgen` should not *diverge* on the closed-postcondition form.
-/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax.MWE

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

/-- `λ n, n + 1`. -/
def incByte : Val := hl_val% λ n, n + #1

/-- Spec keyed on the normalised value form `Val.lit (.int _)` (NOT `byteVal _`, which the stepper
normalises away), at priority above `spec_beta` (2000). -/
@[spec 2500] theorem incByte_spec (n : Int) :
    True ⊑ wp⟦Exp.app (Exp.ofVal incByte) (Exp.ofVal (Val.lit (.int n)))⟧
      (fun v => v = Val.lit (.int (n + 1))) := by
  simp only [incByte]
  hl_step
  first | rfl | (refine spec_binop_add ?_; rfl) | (refine wp_val ?_; rfl) | grind

/-- **Works.** Single call — plain `vcgen` applies `incByte_spec` and closes. -/
example (n : Int) :
    True ⊑ wp⟦Exp.app (Exp.ofVal incByte) (Exp.ofVal (Val.lit (.int n)))⟧
      (fun v => v = Val.lit (.int (n + 1))) := by
  vcgen

-- **Hangs.** Uncomment to reproduce the divergence:
-- set_option maxHeartbeats 400000 in
-- example (n : Int) :
--     True ⊑ wp⟦Exp.app (Exp.ofVal incByte) (Exp.app (Exp.ofVal incByte) (Exp.ofVal (Val.lit (.int n))))⟧
--       (fun v => v = Val.lit (.int (n + 2))) := by
--   vcgen

end Iris.HeapLang.Ax.MWE
