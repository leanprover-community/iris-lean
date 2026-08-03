module

public import IrisDoNightly.Codec.Delta.Code
public import IrisDoNightly.Codec.Delta.Model
public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `delta` codec — correctness proofs -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

@[spec 2500] public theorem deltaCPure_cps (cs : List Int) :
    (∀ x ∈ cs, 0 ≤ x ∧ x < 256) → ∀ prev : Int, prev < 256 → ∀ Φ : Val → Prop,
    Φ (vList (deltaEnc prev cs))
      ⊑ wp⟦hl(v(&deltaCPure) v(&(byteVal prev)) v(&(vList cs)))⟧ Φ := by
  induction cs with
  | nil =>
    intro _ prev _ Φ
    simp only [deltaCPure]
    vcgen' []
    assumption
  | cons c cs ih =>
    intro hcs prev hprev Φ
    obtain ⟨hc0, hc256⟩ := hcs c (by simp)
    simp only [deltaCPure]
    -- ALL weakest-precondition stepping — the recursive call is discharged by `ih` — then the pure
    -- side goals: `ih`'s two hypotheses and the head reconciliation (object `tmod` vs model `emod`).
    vcgen' [ih]
    · exact fun x hx => hcs x (List.mem_cons_of_mem c hx)
    · exact hc256
    · have harg : (c - prev + 256).tmod 256 = (c - prev + 256) % 256 := by grind
      rw [harg]; assumption

/-- Closed compressor spec — one-line corollary of the CPS-native `deltaCPure_cps`. -/
public theorem deltaCPure_spec (cs : List Int) :
    (∀ x ∈ cs, 0 ≤ x ∧ x < 256) → ∀ prev : Int, prev < 256 →
    True ⊑ wp⟦hl(v(&deltaCPure) v(&(byteVal prev)) v(&(vList cs)))⟧
      (fun v => v = vList (deltaEnc prev cs)) :=
  fun hcs prev hprev _ => deltaCPure_cps cs hcs prev hprev _ rfl

@[spec 2500] public theorem deltaDPure_cps (ds : List Int) :
    (∀ x ∈ ds, 0 ≤ x ∧ x < 256) → ∀ prev : Int, 0 ≤ prev → ∀ Φ : Val → Prop,
    Φ (vList (deltaDec prev ds))
      ⊑ wp⟦hl(v(&deltaDPure) v(&(byteVal prev)) v(&(vList ds)))⟧ Φ := by
  induction ds with
  | nil =>
    intro _ prev _ Φ
    simp only [deltaDPure]
    vcgen' []
    assumption
  | cons d ds ih =>
    intro hds prev hprev Φ
    obtain ⟨hd0, hd256⟩ := hds d (by simp)
    simp only [deltaDPure]
    -- the decoder's recursive `prev` is `(prev+d) tmod 256`; `ih` unifies against it directly, so the
    -- side goals carry `tmod` — one `harg` rewrite reconciles it with the model's `emod`.
    have harg : (prev + d).tmod 256 = (prev + d) % 256 := by grind
    vcgen' [ih]
    · exact fun x hx => hds x (List.mem_cons_of_mem d hx)
    · rw [harg]; omega
    · rw [harg]; assumption

/-- Closed decompressor spec — one-line corollary of the CPS-native `deltaDPure_cps`. -/
public theorem deltaDPure_spec (ds : List Int) :
    (∀ x ∈ ds, 0 ≤ x ∧ x < 256) → ∀ prev : Int, 0 ≤ prev →
    True ⊑ wp⟦hl(v(&deltaDPure) v(&(byteVal prev)) v(&(vList ds)))⟧
      (fun v => v = vList (deltaDec prev ds)) :=
  fun hds prev hprev _ => deltaDPure_cps ds hds prev hprev _ rfl

public theorem deltaDec_deltaEnc (cs : List Int) (h : ∀ x ∈ cs, 0 ≤ x ∧ x < 256) :
    ∀ prev, deltaDec prev (deltaEnc prev cs) = cs := by
  induction cs with
  | nil => intro prev; rfl
  | cons c cs ih =>
    intro prev
    have hc := h c (by simp)
    have key : (prev + (c - prev + 256) % 256) % 256 = c := by grind
    simp only [deltaEnc, deltaDec, key]
    exact congrArg (c :: ·) (ih (fun x hx => h x (by simp [hx])) c)

public theorem deltaEnc_mem_range (prev : Int) (l : List Int) :
    ∀ x ∈ deltaEnc prev l, 0 ≤ x ∧ x < 256 := by
  induction l generalizing prev <;> grind [deltaEnc]

theorem delta_roundtrip (cs : List Int) (hcs : ∀ x ∈ cs, 0 ≤ x ∧ x < 256) :
    True ⊑ wp⟦hl(v(&deltaDPure) v(&(byteVal 0)) (v(&deltaCPure) v(&(byteVal 0)) v(&(vList cs))))⟧
      (fun v => v = vList cs) := by
  refine PartialOrder.rel_trans ?_
    (spec_bind (ECtxItem.appR hl(v(&deltaDPure) v(&(byteVal 0)))))
  refine PartialOrder.rel_trans (deltaCPure_spec cs hcs 0 (by omega)) (wp_mono ?_)
  intro v hv
  subst hv
  refine wp_mono ?_ (deltaDPure_spec (deltaEnc 0 cs) (deltaEnc_mem_range 0 cs) 0 (by omega) trivial)
  intro v hv
  exact hv.trans (congrArg vList (deltaDec_deltaEnc cs hcs 0))

end Iris.HeapLang.Ax
