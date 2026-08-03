module

public import IrisDoNightly.Codec.DeltaRoundtrip
public import IrisDoNightly.Codec.RleRoundtrip
import Std.Tactic.Do
import Std.Internal.Do

/-!
# Two-codec pipeline round-trips, proved once (`pipeline_gen`)

`roundtrip_gen` (in `DeltaRoundtrip.lean`) closes the round-trip of a *single* codec. A real pipeline
stacks codecs: `encode = encᵢ ∘ encₒ`, `decode = decₒ ∘ decᵢ`. Its HeapLang program nests the
decoder two frames deep — `Kdₒ.fill (Kdᵢ.fill (Kcᵢ.fill (Kcₒ.fill v)))` — so `roundtrip_gen`'s
single-frame `spec_bind` no longer reaches the compressed value.

`pipeline_gen` proves the stacked round-trip once, by peeling the four evaluation frames one at a time
with `spec_bind` (assemble direction only — a two-frame *decode* bind law is NOT derivable from the
one-directional `spec_bind`, so we never form it; we peel instead). Each concrete pipeline is then a
single application. `delta_rle_pipeline` instantiates it on `delta ∘ rle` — its whole proof is the
component specs already proved for the two codecs in isolation, composed with no new `wp` reasoning.

Only the model-level facts (`hQ_*`, `rt_*`, `chainP`) and the four component CPS specs are supplied;
the operational glue is entirely inside `pipeline_gen`.
-/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms
open scoped Iris.HeapLang.Ax.Auto

variable {wp} [HeapLangAxioms wp]

/-- Round-trip of a two-codec pipeline. `o` = outer codec (runs first on encode, last on decode),
`i` = inner codec. `Kc*`/`Kd*` are each codec's compressor / decompressor as a one-argument evaluation
frame (fill the list slot); `mc*`/`md*` their pure models; `P*`/`Q*` their input / compressed-output
preconditions. `chainP` threads the outer compressor's output into the inner codec's precondition. -/
public theorem pipeline_gen
    {Kc_o Kd_o Kc_i Kd_i : ECtxItem}
    {mc_o md_o mc_i md_i : List Int → List Int}
    {P_o Q_o P_i Q_i : List Int → Prop}
    (comp_o : ∀ l, P_o l → ∀ Φ : Val → Prop,
      Φ (vList (mc_o l)) ⊑ wp⟦Kc_o.fill hl(v(&(vList l)))⟧ Φ)
    (decomp_o : ∀ l, Q_o l → ∀ Φ : Val → Prop,
      Φ (vList (md_o l)) ⊑ wp⟦Kd_o.fill hl(v(&(vList l)))⟧ Φ)
    (comp_i : ∀ l, P_i l → ∀ Φ : Val → Prop,
      Φ (vList (mc_i l)) ⊑ wp⟦Kc_i.fill hl(v(&(vList l)))⟧ Φ)
    (decomp_i : ∀ l, Q_i l → ∀ Φ : Val → Prop,
      Φ (vList (md_i l)) ⊑ wp⟦Kd_i.fill hl(v(&(vList l)))⟧ Φ)
    (hQ_o : ∀ l, P_o l → Q_o (mc_o l)) (rt_o : ∀ l, P_o l → md_o (mc_o l) = l)
    (hQ_i : ∀ l, P_i l → Q_i (mc_i l)) (rt_i : ∀ l, P_i l → md_i (mc_i l) = l)
    (chainP : ∀ l, P_o l → P_i (mc_o l))
    (l : List Int) (hl : P_o l) :
    True ⊑ wp⟦Kd_o.fill (Kd_i.fill (Kc_i.fill (Kc_o.fill hl(v(&(vList l))))))⟧
      (fun v => v = vList l) := by
  -- peel the four frames outermost-first with `spec_bind`, then hit each exposed value with its
  -- component CPS spec; the last goal is the pure four-fold model round-trip.
  refine PartialOrder.rel_trans ?_ (spec_bind Kd_o)
  refine PartialOrder.rel_trans ?_ (spec_bind Kd_i)
  refine PartialOrder.rel_trans ?_ (spec_bind Kc_i)
  refine PartialOrder.rel_trans ?_ (comp_o l hl _)
  refine PartialOrder.rel_trans ?_ (comp_i (mc_o l) (chainP l hl) _)
  refine PartialOrder.rel_trans ?_ (decomp_i (mc_i (mc_o l)) (hQ_i (mc_o l) (chainP l hl)) _)
  have hq : Q_o (md_i (mc_i (mc_o l))) := by
    rw [rt_i (mc_o l) (chainP l hl)]; exact hQ_o l hl
  refine PartialOrder.rel_trans ?_ (decomp_o (md_i (mc_i (mc_o l))) hq _)
  intro _
  refine congrArg vList ?_
  rw [rt_i (mc_o l) (chainP l hl)]; exact rt_o l hl

/-- `delta ∘ rle` pipeline (compress with `delta` then `rle`; decompress `rle` then `delta`), a single
application of `pipeline_gen` fed the two codecs' already-proven component specs. -/
public theorem delta_rle_pipeline (l : List Int) (hl : ∀ x ∈ l, 0 ≤ x ∧ x < 256) :
    True ⊑ wp⟦(ECtxItem.appR hl(v(&deltaDPure) v(&(byteVal 0)))).fill
                ((ECtxItem.appR hl(v(&hlRleDec))).fill
                  ((ECtxItem.appR hl(v(&hlRleEnc))).fill
                    ((ECtxItem.appR hl(v(&deltaCPure) v(&(byteVal 0)))).fill
                      hl(v(&(vList l))))))⟧
      (fun v => v = vList l) :=
  pipeline_gen
    (Kc_o := ECtxItem.appR hl(v(&deltaCPure) v(&(byteVal 0))))
    (Kd_o := ECtxItem.appR hl(v(&deltaDPure) v(&(byteVal 0))))
    (Kc_i := ECtxItem.appR hl(v(&hlRleEnc))) (Kd_i := ECtxItem.appR hl(v(&hlRleDec)))
    (mc_o := deltaEnc 0) (md_o := deltaDec 0) (mc_i := rleEnc) (md_i := rleDec)
    (P_o := fun l => ∀ x ∈ l, 0 ≤ x ∧ x < 256) (Q_o := fun l => ∀ x ∈ l, 0 ≤ x ∧ x < 256)
    (P_i := fun _ => True) (Q_i := GoodCounts)
    (fun l hl => deltaCPure_cps l hl 0 (by omega))
    (fun l hl => deltaDPure_cps l hl 0 (by omega))
    (fun l _ => hlRleEnc_cps l) (fun l hl => hlRleDec_cps l hl)
    (fun l _ => deltaEnc_mem_range 0 l) (fun l hl => deltaDec_deltaEnc l hl 0)
    (fun l _ => GoodCounts_rleEnc l) (fun l _ => rleDec_rleEnc l)
    (fun _ _ => trivial) l hl

end Iris.HeapLang.Ax
