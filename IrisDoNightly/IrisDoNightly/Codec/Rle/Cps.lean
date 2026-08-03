module

public import IrisDoNightly.Codec.Rle
public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `rle` codec — a `vcgen'` CPS spec for the 3-argument helper `hlReplicateApp`

`rle`'s user-facing CPS specs (`hlRleEnc_cps`, `hlRleDec_cps`) already exist in `RleRoundtrip.lean`
via `derive_cps`. This file adds the one internal helper that fits the `vcgen'` shape, mainly as the
demonstration that `vcgen'` is arity-generic (its `Exp.app _ _` call pattern matches a 1-, 2- or
3-argument recursive call alike).

`hlReplicateApp` is 3-arg (`n c tail`) with `Nat` recursion and an `if k=0` guard. The guard's dead
branch is vacuous (contradictory hypothesis), so it is closed with `(try (exfalso; grind))` before
the real branch's discharger.

Not converted (kept as their closed proofs / `derive_cps`): `hlRleAux` (its recursion is nested inside
`injr((k, injr((c, go …))))`, which a vcgen sweep unrolls before `ih` can match — the same wall as
`Mtf.hlIndexOf`); `hlRleEnc`/`hlRleDec` (nested aux calls). Kept in a separate file from
`Correctness.lean` because importing `Auto` changes `vcgen`'s behaviour and breaks the closed proofs. -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

/-- CPS-native `hlReplicateApp`, proved with the arity-generic `vcgen'` (3-argument recursion). -/
theorem hlReplicateApp_cps (n : Nat) : ∀ (c : Int) (tail : List Int), ∀ Φ : Val → Prop,
    Φ (vList (replicateApp n c tail))
      ⊑ wp⟦hl(v(&hlReplicateApp) v(&(byteVal n)) v(&(byteVal c)) v(&(vList tail)))⟧ Φ := by
  induction n with
  | zero =>
    intro c tail Φ; simp only [hlReplicateApp]
    vcgen' [] <;> (try (exfalso; grind)) <;> (try simp_all [replicateApp, vList, byteVal])
  | succ n ih =>
    intro c tail Φ; simp only [hlReplicateApp]
    vcgen' [ih] <;> (try (exfalso; grind)) <;> (try simp_all [replicateApp, vList, byteVal])

end Iris.HeapLang.Ax
