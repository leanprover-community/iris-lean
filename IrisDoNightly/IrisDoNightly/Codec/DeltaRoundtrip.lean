module

public import IrisDoNightly.Codec.Delta
public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

/-!
# `delta` round-trip via CPS specs + `vcgen` — vs. the manual `spec_bind` version in `Delta.lean`

`Delta.lean`'s `delta_roundtrip` is ~9 lines of manual `spec_bind` + `wp_mono` plumbing. Here the two
compressor/decompressor specs are re-exposed in continuation-passing form (one line each, derived
from the closed specs) and `@[spec]`-registered; the round-trip is then `vcgen` + closing the VCs.
-/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

/-! The CPS forms `deltaCPure_cps` / `deltaDPure_cps` are now the *primary* codec specs, proved
directly in `Delta/Correctness.lean` (the closed `deltaCPure_spec` / `deltaDPure_spec` are the
corollaries). So the `derive_cps` wrappers that used to live here are gone — nothing to derive. -/

/-- `delta` round-trip, PURE `vcgen`: it composes the two CPS specs at the two call sites; the four
side-condition VCs and the pure round-trip `deltaDec 0 (deltaEnc 0 cs) = cs` close by name/`omega`.
(A bare `vcgen <;> grind` does NOT work here — `grind`'s triggers don't fire reliably on these VC
shapes even with tuned `@[grind]` facts; a declarative discharge list is the practical form.) -/
theorem delta_roundtrip_vcgen (cs : List Int) (hcs : ∀ x ∈ cs, 0 ≤ x ∧ x < 256) :
    True ⊑ wp⟦hl(v(&deltaDPure) v(&(byteVal 0)) (v(&deltaCPure) v(&(byteVal 0)) v(&(vList cs))))⟧
      (fun v => v = vList cs) := by
  vcgen <;>
    first
      | exact congrArg vList (deltaDec_deltaEnc cs hcs 0)
      | exact hcs _ (by assumption)
      | exact deltaEnc_mem_range 0 cs _ (by assumption)
      | omega

/-! ## Upgrade #4 (architectural): a GENERIC round-trip theorem, proved once

For any prev-parameterised codec pair whose specs are CPS-form, with an input precondition `P`, a
compressor-output precondition `Q`, and a pure model round-trip — the HeapLang round-trip follows.
Each concrete codec of this shape then gets its round-trip as a single application. -/

theorem roundtrip_of_cps
    {compV c0 decompV d0 : Val} {mc md : List Int → List Int} {P Q : List Int → Prop}
    (comp_cps : ∀ l, P l → ∀ Φ : Val → Prop,
      Φ (vList (mc l)) ⊑ wp⟦hl(v(&compV) v(&c0) v(&(vList l)))⟧ Φ)
    (decomp_cps : ∀ l, Q l → ∀ Φ : Val → Prop,
      Φ (vList (md l)) ⊑ wp⟦hl(v(&decompV) v(&d0) v(&(vList l)))⟧ Φ)
    (hQ : ∀ l, P l → Q (mc l)) (rt : ∀ l, P l → md (mc l) = l)
    (l : List Int) (hl : P l) :
    True ⊑ wp⟦hl(v(&decompV) v(&d0) (v(&compV) v(&c0) v(&(vList l))))⟧
      (fun v => v = vList l) := by
  refine PartialOrder.rel_trans ?_
    (spec_bind (ECtxItem.appR hl(v(&decompV) v(&d0))))
  refine PartialOrder.rel_trans ?_ (comp_cps l hl _)
  refine PartialOrder.rel_trans ?_ (decomp_cps (mc l) (hQ l hl) _)
  intro _
  exact congrArg vList (rt l hl)

/-- `delta` round-trip as a ONE-LINE instantiation of the generic theorem. -/
theorem delta_roundtrip_generic (cs : List Int) (hcs : ∀ x ∈ cs, 0 ≤ x ∧ x < 256) :
    True ⊑ wp⟦hl(v(&deltaDPure) v(&(byteVal 0)) (v(&deltaCPure) v(&(byteVal 0)) v(&(vList cs))))⟧
      (fun v => v = vList cs) :=
  roundtrip_of_cps (P := fun l => ∀ x ∈ l, 0 ≤ x ∧ x < 256) (Q := fun l => ∀ x ∈ l, 0 ≤ x ∧ x < 256)
    (fun l hl => deltaCPure_cps l hl 0 (by omega))
    (fun l hl => deltaDPure_cps l hl 0 (by omega))
    (fun l _ => deltaEnc_mem_range 0 l) (fun l hl => deltaDec_deltaEnc l hl 0) cs hcs

/-! ## Upgrade #4, full form: arity-agnostic round-trip

`roundtrip_of_cps` above hard-codes the 2-argument (prev) call shape, so it fits `delta` but not the
1-argument `rle`. Abstracting the compressor as `runComp : List Int → Exp` and the decompressor as an
evaluation context `Kdecomp : ECtxItem` (its argument slot) covers EVERY arity — proved once. -/

public theorem roundtrip_gen {runComp : List Int → Exp} {Kdecomp : ECtxItem}
    {mc md : List Int → List Int} {P Q : List Int → Prop}
    (comp_cps : ∀ l, P l → ∀ Φ : Val → Prop, Φ (vList (mc l)) ⊑ wp⟦runComp l⟧ Φ)
    (decomp_cps : ∀ l, Q l → ∀ Φ : Val → Prop,
      Φ (vList (md l)) ⊑ wp⟦Kdecomp.fill hl(v(&(vList l)))⟧ Φ)
    (hQ : ∀ l, P l → Q (mc l)) (rt : ∀ l, P l → md (mc l) = l)
    (l : List Int) (hl : P l) :
    True ⊑ wp⟦Kdecomp.fill (runComp l)⟧ (fun v => v = vList l) := by
  refine PartialOrder.rel_trans ?_ (spec_bind Kdecomp)
  refine PartialOrder.rel_trans ?_ (comp_cps l hl _)
  refine PartialOrder.rel_trans ?_ (decomp_cps (mc l) (hQ l hl) _)
  intro _; exact congrArg vList (rt l hl)

/-- `delta` round-trip via the arity-agnostic theorem (delta's decompressor is `appR (deltaDPure 0)`). -/
theorem delta_roundtrip_gen (cs : List Int) (hcs : ∀ x ∈ cs, 0 ≤ x ∧ x < 256) :
    True ⊑ wp⟦(ECtxItem.appR hl(v(&deltaDPure) v(&(byteVal 0)))).fill
                hl(v(&deltaCPure) v(&(byteVal 0)) v(&(vList cs)))⟧
      (fun v => v = vList cs) :=
  roundtrip_gen
    (runComp := fun l => hl(v(&deltaCPure) v(&(byteVal 0)) v(&(vList l))))
    (Kdecomp := ECtxItem.appR hl(v(&deltaDPure) v(&(byteVal 0))))
    (mc := deltaEnc 0) (md := deltaDec 0)
    (P := fun l => ∀ x ∈ l, 0 ≤ x ∧ x < 256) (Q := fun l => ∀ x ∈ l, 0 ≤ x ∧ x < 256)
    (fun l hl => deltaCPure_cps l hl 0 (by omega))
    (fun l hl => deltaDPure_cps l hl 0 (by omega))
    (fun l _ => deltaEnc_mem_range 0 l) (fun l hl => deltaDec_deltaEnc l hl 0) cs hcs

end Iris.HeapLang.Ax
