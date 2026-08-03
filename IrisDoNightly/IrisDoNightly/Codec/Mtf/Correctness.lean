module

public import IrisDoNightly.Codec.Mtf.Code
public import IrisDoNightly.Codec.Mtf.Model
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `mtf` (move-to-front) codec — correctness proofs -/

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
    simp [idxOf, byteVal]
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
      simp [idxOf]
    · -- mismatch: `1 +` the index in the tail, the recursion discharged by the IH
      have hb : (hl_val(#x) == hl_val(#c)) = false := by simp [hxc]
      rw [hb]
      simp only [Bool.false_eq_true, ite_false]
      refine spec_binop ?_
      refine wp_mono ?_ (ih c trivial)
      intro v hv
      subst hv
      refine spec_val ?_
      simp only [byteVal, BinOp.eval, Option.some.injEq, exists_eq_left', Val.lit.injEq,
        BaseLit.int.injEq, idxOf, ite_eq_right hxc]
      omega

theorem hlEraseIdx_spec (t : List Int) : ∀ r : Int,
    True ⊑ wp⟦hl(v(&hlEraseIdx) v(&(vList t)) v(&(byteVal r)))⟧
      (fun v => v = vList (eraseIdx' t r)) := by
  induction t with
  | nil =>
    intro r
    simp only [hlEraseIdx]
    hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    simp [eraseIdx', vList]
  | cons x xs ih =>
    intro r
    simp only [hlEraseIdx]
    hl_beta; hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let x := fst p`
    hl_projlet                             -- `let xs := snd p`
    vcgen
    simp only [byteVal, BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed,
      Bool.or_true, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨_, rfl, ?_⟩
    by_cases hr : r = 0
    · -- drop here: return the tail
      subst hr
      simp only [beq_self_eq_true, ite_true]
      vcgen
      simp [eraseIdx']
    · -- keep `x`, recurse into the tail
      have hb : (hl_val(#r) == hl_val(#(0:Int))) = false := by simp [hr]
      rw [hb]
      simp only [Bool.false_eq_true, ite_false]
      hl_binop                             -- `let r' := r - 1`
      refine spec_injR ?_
      refine spec_pair ?_
      refine wp_mono ?_ (ih (r - 1) trivial)
      intro v hv
      subst hv
      refine spec_val ?_
      simp [eraseIdx', ite_eq_right hr, vList, byteVal]

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
    simp [mtfEnc, vList]
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
    simp [mtfEnc, vList, byteVal]

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
    simp [mtfDec, vList]
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
    simp [mtfDec, vList, byteVal]

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

end Iris.HeapLang.Ax
