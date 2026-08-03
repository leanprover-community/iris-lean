module

public import IrisDoNightly.Codec.Mtf.Correctness
public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `mtf` codec — CPS-form specs

Continuation-passing forms of the `mtf` helper specs. Kept in a SEPARATE file from `Correctness.lean`
because they need the extended `@[spec]` set from `Auto`, and importing `Auto` changes `vcgen`'s
behaviour enough to break the closed-form proofs there (which were written against base `vcgen`).

`hlEraseIdx`/`hlNth` are the two `mtf` functions whose recursion is in TAIL position with an `if`
guard, so `vcgen'` drives them end-to-end (all stepping, pure side goals). `hlIndexOf` recurses inside
a binop (`#1 + go xs c`), which `vcgen'` cannot yet drive — its CPS form is derived from the closed
proof. `hlMtfCompress`/`hlMtfDecompress` are not converted: their recursive call's table argument is a
constructed value `injr((c, e))` rather than a syntactic `vList _`, so `apply ih` fails to unify and
`vcgen'` diverges (a distinct wall from `hlIndexOf`'s). See the memory note for the full taxonomy. -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

/-- CPS-native, proved with `vcgen'`: the `if r=0` guard auto-splits and the tail recursion
`injr((x, go xs r'))` is discharged by `ih`, leaving two pure branch side goals that `simp_all`
closes against the split guard. -/
@[spec 2500] theorem hlEraseIdx_cps (t : List Int) : ∀ r : Int, ∀ Φ : Val → Prop,
    Φ (vList (eraseIdx' t r))
      ⊑ wp⟦hl(v(&hlEraseIdx) v(&(vList t)) v(&(byteVal r)))⟧ Φ := by
  induction t with
  | nil => intro r Φ; simp only [hlEraseIdx]; vcgen' []; assumption
  | cons x xs ih =>
    intro r Φ
    simp only [hlEraseIdx]
    vcgen' [ih] <;> simp_all [eraseIdx', vList, byteVal]

/-- CPS-native `hlNth` (same shape as `hlEraseIdx`). -/
@[spec 2500] theorem hlNth_cps (t : List Int) : ∀ r : Int, ∀ Φ : Val → Prop,
    Φ (byteVal (nthD t r))
      ⊑ wp⟦hl(v(&hlNth) v(&(vList t)) v(&(byteVal r)))⟧ Φ := by
  induction t with
  | nil => intro r Φ; simp only [hlNth]; vcgen' []; assumption
  | cons x xs ih =>
    intro r Φ
    simp only [hlNth]
    vcgen' [ih] <;> simp_all [nthD, vList, byteVal]

/-- CPS form of `hlIndexOf` — recursion inside a binop, so derived from the closed proof, not `vcgen'`. -/
@[spec 2500] theorem hlIndexOf_cps (t : List Int) (c : Int) (Φ : Val → Prop) :
    Φ (byteVal (idxOf t c)) ⊑ wp⟦hl(v(&hlIndexOf) v(&(vList t)) v(&(byteVal c)))⟧ Φ := by
  derive_cps (hlIndexOf_spec t c trivial)

end Iris.HeapLang.Ax
