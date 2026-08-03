module

public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

/-! # MWE: `vcgen` unrolls a recursive call instead of applying the in-scope `ih`/spec

This isolates the one framework gap behind our codec-verification use case, for @sgraf.

## The use case
We verify HeapLang codecs by `@[spec]`-registering each function's correctness lemma in
**continuation-passing form** `Φ (model …) ⊑ wp⟦prog⟧ Φ`. For a NON-recursive body the proof is
literally `simp only [prog]; vcgen`: `vcgen` symbolically executes the whole body and leaves the pure
side goals. We would like the SAME for a recursive body — `simp only [prog]; vcgen [ih]`, where `ih`
is the induction hypothesis (which is exactly the spec for the recursive call) — leaving the pure side
goals. See `Codec/Mtf/Correctness.lean` (`hlEraseIdx_cps`) and `Codec/Rle/Correctness.lean`
(`hlReplicateApp_cps`) for cases where `vcgen'` makes this work.

## The gap
It works ONLY when the recursive call sits at a spot where we can `until`-stop the sweep and
`apply ih` by hand before it unrolls. When the recursive call is buried inside a binop/constructor
(here `#1 + go xs`), `vcgen` reaches it and applies the structural step rule (`spec_app`→`spec_rec`)
— UNROLLING the call into a `match` on the abstract argument — instead of applying the in-scope `ih`.

## Root cause (traced in `Lean/Elab/Tactic/Do/Internal/VCGen/`)
`solve` (Solve.lean:554-576) decomposes `wp e Φ` and finally calls `applySpec`→`SpecDB.findSpecs`
(SpecDB.lean:120-132), which picks the HIGHEST-PRIORITY `@[spec]` whose discr-tree pattern matches `e`.
- PRIORITY is not the problem: the `vcgen [ih]` bracket registers `ih` at `explicitSpecPrio =
  eval_prio high + 3000 = 13000` (Attr.lean:357), far above the structural `spec_app` (~1000-2000).
- MATCHING is the problem: after the outer `rec` is stepped, the recursive call is the UNFOLDED
  `rec`-closure value `(Exp.val (Val.rec_ …)) …`, but `ih` is keyed on the FOLDED constant
  `Exp.val hlLen …`. The discrimination tree in `findSpecs`/`getMatch` therefore never OFFERS `ih` as
  a candidate → only `spec_app` matches → unroll.

## The ask
Make `findSpecs`/`getMatch` match a program against local/`[ih]` specs up to the reducibility that
folds the `rec`-closure back to the codec constant (or key such specs on the reduced form). Then the
`example`s below marked "IDEAL" would go through, and every codec spec — recursive or not — is
`simp only [prog]; vcgen [ih]` + pure side goals. -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax.MWE

open HeapLangAxioms
open scoped Iris.HeapLang.Ax.Auto

variable {wp} [HeapLangAxioms wp]

/-- Minimal recursive HeapLang function: list length, recursion buried in `#1 + go xs`. -/
def hlLen : Val := hl_val%
  rec go l :=
    match l with
    | injl(u) => #0
    | injr(p) => let xs := snd(p); #1 + go xs

/-- Pure model. -/
def lengthN : List Int → Int
  | [] => 0
  | _ :: xs => 1 + lengthN xs

theorem hlLen_cps (l : List Int) : ∀ Φ : Val → Prop,
    Φ (byteVal (lengthN l)) ⊑ wp⟦hl(v(&hlLen) v(&(vList l)))⟧ Φ := by
  induction l with
  | nil =>
    intro Φ
    simp only [hlLen]
    -- non-recursive: `vcgen'` (our sweep-to-fixpoint) alone finishes — exactly the shape we want.
    vcgen' []
    simp_all [lengthN, byteVal]
  | cons x xs ih =>
    intro Φ
    simp only [hlLen]
    -- `vcgen` symbolic execution across the `rec`/`match`/`let`, stopping AT the binop `#1 + go xs`.
    vcgen (errorOnMissingSpec := false) [BinOp.eval] until Exp.subst _ _ _
    try simp [Exp.subst, Exp.substStr, substStr_ofVal, vList, byteVal]
    vcgen (errorOnMissingSpec := false) [BinOp.eval] until Exp.subst _ _ _
    try simp [Exp.subst, Exp.substStr, substStr_ofVal, vList, byteVal]
    vcgen (errorOnMissingSpec := false) [BinOp.eval] until Exp.subst _ _ _
    try simp [Exp.subst, Exp.substStr, substStr_ofVal, vList, byteVal]
    -- ── THE GAP ─────────────────────────────────────────────────────────────────────────────
    -- Goal here is `wp⟦#1 + go xs⟧ Φ`, with `ih : ∀ Φ, Φ (byteVal (lengthN xs)) ⊑ wp⟦go xs⟧ Φ`
    -- IN SCOPE. What we WANT is for `vcgen [ih]` to APPLY `ih` at `go xs` and continue — leaving
    -- only pure side goals.
    --
    -- What actually happens if you run `vcgen (errorOnMissingSpec := false) [ih, BinOp.eval]` here:
    -- it steps into `go xs` and UNROLLS it (`spec_app`→`spec_rec`), leaving the stuck goal
    --   (∃ v, vList xs = injl v ∧ …) ∨ (∃ v, vList xs = injr v ∧ wp⟦match-body-of-hlLen⟧ …)
    -- i.e. a `match` on the ABSTRACT `vList xs` — never applying `ih`, even though `ih` is at
    -- priority 13000 (the `[ih]` bracket), because the discr-tree in `findSpecs` never offers it.
    --
    -- The two lines below are the manual stand-in for the one step the framework should do (match the
    -- recursive call against the in-scope `ih`/spec):
    refine spec_binop ?_        -- expose the operand `go xs` as `wp⟦go xs⟧ …`
    refine ih _ ?_              -- apply `ih` at the recursive call (CPS: no wp_mono/intro/subst)
    -- ── end gap ─────────────────────────────────────────────────────────────────────────────
    -- pure side goal: `wp⟦#1⟧ (fun v => ∃ v', BinOp.eval Add v (byteVal (lengthN xs)) = some v' ∧ Φ v')`
    vcgen' []
    simp_all [lengthN, byteVal]

end Iris.HeapLang.Ax.MWE
