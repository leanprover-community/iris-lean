module

public import IrisDoNightly.Codec.Rle
public import IrisDoNightly.Codec.DeltaRoundtrip   -- reuse the arity-agnostic `roundtrip_gen`
import Std.Tactic.Do
import Std.Internal.Do

/-!
# `rle` round-trip via the SAME `roundtrip_gen` — proving it is arity-agnostic

`rle`'s compressor/decompressor are 1-argument (no `prev`), yet the identical generic theorem
`roundtrip_gen` (proved once in `DeltaRoundtrip.lean`) closes the round-trip — `runComp`/`Kdecomp`
absorb the arity difference.
-/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

/-- CPS form of `hlRleEnc_spec`. -/
@[spec 2500] public theorem hlRleEnc_cps (l : List Int) (Φ : Val → Prop) :
    Φ (vList (rleEnc l)) ⊑ wp⟦hl(v(&hlRleEnc) v(&(vList l)))⟧ Φ := by
  derive_cps (hlRleEnc_spec l trivial)

/-- CPS form of `hlRleDec_spec` (its `GoodCounts` premise stays a hypothesis). -/
@[spec 2500] public theorem hlRleDec_cps (l : List Int) (hl : GoodCounts l) (Φ : Val → Prop) :
    Φ (vList (rleDec l)) ⊑ wp⟦hl(v(&hlRleDec) v(&(vList l)))⟧ Φ := by
  derive_cps (hlRleDec_spec l hl trivial)

/-- `rle` round-trip as an instance of the arity-agnostic `roundtrip_gen` (1-arg codec, `P := True`). -/
theorem rle_roundtrip_gen (l : List Int) :
    True ⊑ wp⟦(ECtxItem.appR hl(v(&hlRleDec))).fill
                hl(v(&hlRleEnc) v(&(vList l)))⟧
      (fun v => v = vList l) :=
  roundtrip_gen
    (runComp := fun l => hl(v(&hlRleEnc) v(&(vList l))))
    (Kdecomp := ECtxItem.appR hl(v(&hlRleDec)))
    (mc := rleEnc) (md := rleDec) (P := fun _ => True) (Q := GoodCounts)
    (fun l _ => hlRleEnc_cps l) (fun l hl => hlRleDec_cps l hl)
    (fun l _ => GoodCounts_rleEnc l) (fun l _ => rleDec_rleEnc l) l trivial

end Iris.HeapLang.Ax
