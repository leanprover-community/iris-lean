module

public import IrisDoNightly.Codec.Mtf.Code
public import IrisDoNightly.Codec.Mtf.Model
public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `mtf` (move-to-front) codec — correctness proofs

Proof shape is **(vcgen-ish) then (grind-ish)** throughout.  The tail-recursive helper `hlEraseIdx`
is driven end-to-end by `vcgen'` (in an `open scoped …Auto` section); the buried-recursion `hlIndexOf`
and the constructed-arg-recursion `hlMtfCompress`/`hlMtfDecompress` keep base-`vcgen` stepping (the
framework gap-2 wall) followed by a `grind` discharge — the `Auto` spec set is *scoped*, so those base
proofs are unaffected by the import. -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

public theorem hlIndexOf_spec (t : List Int) : ∀ c : Int,
    True ⊑ wp⟦hl(v(&hlIndexOf) v(&(vList t)) v(&(byteVal c)))⟧
      (fun v => v = byteVal (idxOf t c)) := by
  induction t with
  | nil =>
    intro c
    simp only [hlIndexOf]
    hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    grind [idxOf, byteVal]
  | cons x xs ih =>
    intro c
    simp only [hlIndexOf]
    hl_beta; hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let x := fst p`
    hl_projlet                             -- `let xs := snd p`
    -- evaluate the guard `x = c` to a boolean, then case on whether the bytes are equal
    vcgen
    simp only [byteVal, BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed,
      Bool.or_true, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨_, rfl, ?_⟩
    by_cases hxc : x = c
    · -- match at this position: index 0
      subst hxc
      simp only [beq_self_eq_true, ite_true]
      vcgen
      grind [idxOf]
    · -- mismatch: `1 +` the index in the tail, the recursion discharged by the IH
      have hb : (hl_val(#x) == hl_val(#c)) = false := by simp [hxc]
      rw [hb]
      simp only [Bool.false_eq_true, ite_false]
      refine spec_binop ?_
      refine wp_mono ?_ (ih c trivial)
      intro v hv
      subst hv
      refine spec_val ?_
      grind [byteVal, BinOp.eval, idxOf]

-- === clean CPS helpers (vcgen'-driven, `Auto` spec set opened for this section) ===
section
open scoped Iris.HeapLang.Ax.Auto

/-- Tail-recursive `hlEraseIdx`: `vcgen'` does all stepping (the `if r=0` guard auto-splits), then
`simp_all` discharges both pure branches — (vcgen-ish) then (grind-ish). -/
public theorem hlEraseIdx_cps (t : List Int) : ∀ r : Int, ∀ Φ : Val → Prop,
    Φ (vList (eraseIdx' t r)) ⊑ wp⟦hl(v(&hlEraseIdx) v(&(vList t)) v(&(byteVal r)))⟧ Φ := by
  induction t with
  | nil => intro r Φ; simp only [hlEraseIdx]; vcgen' []; assumption
  | cons x xs ih =>
    intro r Φ; simp only [hlEraseIdx]; vcgen' [ih] <;> simp_all [eraseIdx', vList, byteVal]

/-- CPS form of `hlIndexOf` — recursion is buried in `#1 + go …` (framework gap-2), so the closed
`hlIndexOf_spec` above stays base-`vcgen` and the CPS wrapper is derived from it. -/
public theorem hlIndexOf_cps (t : List Int) (c : Int) (Φ : Val → Prop) :
    Φ (byteVal (idxOf t c)) ⊑ wp⟦hl(v(&hlIndexOf) v(&(vList t)) v(&(byteVal c)))⟧ Φ := by
  derive_cps (hlIndexOf_spec t c trivial)

end

/-- Closed `hlEraseIdx` spec — 1-line corollary of the CPS form. -/
public theorem hlEraseIdx_spec (t : List Int) : ∀ r : Int,
    True ⊑ wp⟦hl(v(&hlEraseIdx) v(&(vList t)) v(&(byteVal r)))⟧
      (fun v => v = vList (eraseIdx' t r)) :=
  fun r _ => hlEraseIdx_cps t r _ rfl

theorem hlMtfCompress_spec (l : List Int) : ∀ tbl : List Int,
    True ⊑ wp⟦hl(v(&hlMtfCompress) v(&(vList tbl)) v(&(vList l)))⟧
      (fun v => v = vList (mtfEnc tbl l)) := by
  induction l with
  | nil =>
    intro tbl
    simp only [hlMtfCompress]
    hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    grind [mtfEnc, vList]
  | cons c cs ih =>
    intro tbl
    simp only [hlMtfCompress]
    hl_beta; hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let c := fst p`
    hl_projlet                             -- `let cs := snd p`
    hl_call (hlIndexOf_spec tbl c)         -- `let r := hlIndexOf tbl c`
    hl_call (hlEraseIdx_spec tbl (idxOf tbl c))  -- `let e := hlEraseIdx tbl r`
    -- build the new table value `tbl' = c :: eraseIdx tbl r`, then β-bind it
    refine spec_app ?_
    refine spec_injR ?_
    refine spec_pair ?_
    refine spec_val ?_
    refine spec_val ?_
    hl_beta
    -- emit the index `r` and recurse on the new table via the IH
    refine spec_injR ?_
    refine spec_pair ?_
    refine wp_mono ?_ (ih (c :: eraseIdx' tbl (idxOf tbl c)) trivial)
    intro v hv
    subst hv
    refine spec_val ?_
    grind [mtfEnc, vList, byteVal]

theorem hlMtfDecompress_spec (l : List Int) : ∀ tbl : List Int,
    True ⊑ wp⟦hl(v(&hlMtfDecompress) v(&(vList tbl)) v(&(vList l)))⟧
      (fun v => v = vList (mtfDec tbl l)) := by
  induction l with
  | nil =>
    intro tbl
    simp only [hlMtfDecompress]
    hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    grind [mtfDec, vList]
  | cons r rs ih =>
    intro tbl
    simp only [hlMtfDecompress]
    hl_beta; hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let r := fst p`
    hl_projlet                             -- `let rs := snd p`
    hl_call (hlNth_spec tbl r)             -- `let c := hlNth tbl r`
    hl_call (hlEraseIdx_spec tbl r)        -- `let e := hlEraseIdx tbl r`
    -- build the new table value `c :: eraseIdx tbl r`, β-bind, emit `c`, recurse via the IH
    refine spec_app ?_
    refine spec_injR ?_
    refine spec_pair ?_
    refine spec_val ?_
    refine spec_val ?_
    hl_beta
    refine spec_injR ?_
    refine spec_pair ?_
    refine wp_mono ?_ (ih (nthD tbl r :: eraseIdx' tbl r) trivial)
    intro v hv
    subst hv
    refine spec_val ?_
    grind [mtfDec, vList, byteVal]

private theorem idxOf_nonneg (tbl : List Int) (c : Int) : 0 ≤ idxOf tbl c := by
  induction tbl <;> grind [idxOf]

private theorem nthD_idxOf (tbl : List Int) (c : Int) (h : c ∈ tbl) :
    nthD tbl (idxOf tbl c) = c := by
  induction tbl with
  | nil => simp at h
  | cons x xs ih => have := idxOf_nonneg xs c; grind [idxOf, nthD]

private theorem eraseIdx'_idxOf (tbl : List Int) (c : Int) :
    eraseIdx' tbl (idxOf tbl c) = tbl.erase c := by
  induction tbl with
  | nil => simp [eraseIdx']
  | cons x xs ih => have := idxOf_nonneg xs c; grind [idxOf, eraseIdx']

private theorem mtfDec_mtfEnc (l : List Int) : ∀ tbl : List Int, tbl.Nodup →
    (∀ x ∈ l, x ∈ tbl) → mtfDec tbl (mtfEnc tbl l) = l := by
  induction l with
  | nil => intro tbl _ _; simp [mtfEnc, mtfDec]
  | cons c cs ih =>
    intro tbl hnd hmem
    have hc : c ∈ tbl := hmem c (by simp)
    have hperm : tbl.Perm (c :: tbl.erase c) := List.perm_cons_erase hc
    simp only [mtfEnc, mtfDec, nthD_idxOf tbl c hc, eraseIdx'_idxOf tbl c]
    congr 1
    apply ih (c :: tbl.erase c) (hperm.nodup_iff.mp hnd)
    intro x hx
    have hxt : x ∈ tbl := hmem x (by simp [hx])
    exact hperm.mem_iff.mp hxt

/-- **End-to-end `mtf` round-trip.**  Decompressing the compression of `l` against a duplicate-free
table that already contains every byte of `l` returns `l` unchanged — the `mtf` analogue of
`delta_roundtrip` / `rle_roundtrip`, assembling the compressor/decompressor specs with the model
round-trip `mtfDec_mtfEnc`. -/
theorem mtf_roundtrip (tbl l : List Int) (hnd : tbl.Nodup) (hmem : ∀ x ∈ l, x ∈ tbl) :
    True ⊑ wp⟦hl(v(&hlMtfDecompress) v(&(vList tbl))
      (v(&hlMtfCompress) v(&(vList tbl)) v(&(vList l))))⟧
      (fun v => v = vList l) := by
  refine PartialOrder.rel_trans ?_
    (spec_bind (ECtxItem.appR hl(v(&hlMtfDecompress) v(&(vList tbl)))))
  refine PartialOrder.rel_trans (hlMtfCompress_spec l tbl) (wp_mono ?_)
  intro v hv
  subst hv
  refine wp_mono ?_ (hlMtfDecompress_spec (mtfEnc tbl l) tbl trivial)
  intro v hv
  subst hv
  rw [mtfDec_mtfEnc l tbl hnd hmem]

end Iris.HeapLang.Ax
