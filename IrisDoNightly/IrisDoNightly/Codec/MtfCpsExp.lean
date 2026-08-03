module

public import IrisDoNightly.Codec.Mtf
public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

/-! # DIAGNOSE the compress hang: bounded loop, inspect where vcgen' gets stuck. -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

@[spec 2500] theorem hlEraseIdx_cps (t : List Int) : ∀ r : Int, ∀ Φ : Val → Prop,
    Φ (vList (eraseIdx' t r)) ⊑ wp⟦hl(v(&hlEraseIdx) v(&(vList t)) v(&(byteVal r)))⟧ Φ := by
  induction t with
  | nil => intro r Φ; simp only [hlEraseIdx]; vcgen' []; assumption
  | cons x xs ih => intro r Φ; simp only [hlEraseIdx]; vcgen' [ih] <;> simp_all [eraseIdx', vList, byteVal]

@[spec 2500] theorem hlIndexOf_cps (t : List Int) (c : Int) (Φ : Val → Prop) :
    Φ (byteVal (idxOf t c)) ⊑ wp⟦hl(v(&hlIndexOf) v(&(vList t)) v(&(byteVal c)))⟧ Φ := by
  derive_cps (hlIndexOf_spec t c)

/-- BOUNDED loop (iterate, can't hang) to inspect the compress cons goal. -/
scoped macro "vcgenN" " [" specs:term,* "] " : tactic =>
  `(tactic| iterate 14 any_goals first
      | (vcgen (errorOnMissingSpec := false) [BinOp.eval] until Exp.app (Exp.app _ _) _
         first $[| apply $specs]* | fail)
      | simp [Exp.subst, Exp.substStr, substStr_ofVal, vList, byteVal]
      | vcgen (errorOnMissingSpec := false) [BinOp.eval] until Exp.subst _ _ _
      | vcgen (errorOnMissingSpec := false) [BinOp.eval])

theorem hlMtfCompress_cps (l : List Int) : ∀ tbl : List Int, ∀ Φ : Val → Prop,
    Φ (vList (mtfEnc tbl l)) ⊑ wp⟦hl(v(&hlMtfCompress) v(&(vList tbl)) v(&(vList l)))⟧ Φ := by
  induction l with
  | nil => intro tbl Φ; simp only [hlMtfCompress]; vcgenN []
  | cons c cs ih =>
    intro tbl Φ
    simp only [hlMtfCompress]
    vcgenN [ih]

end Iris.HeapLang.Ax
