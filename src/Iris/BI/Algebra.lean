/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProofMode
/-! ## Algebra wrappers for BI

This file provides introduction rules (BI entailments) for (some) CMRA operations and properties.
-/

@[expose] public section

-- TODO: Need sbi_unfold to make these proofs less horrific
namespace Iris
section heap_view

open HeapView BI Std PartialMap LawfulPartialMap BIBase.BiEntails

variable {F K V : Type _} {H : Type _ → Type _}
variable [UFraction F]
variable [LawfulPartialMap H K]
variable [CMRA V]

@[rocq_alias gmap_view_both_dfrac_validI]
theorem auth_op_frag_validI [Sbi PROP] (dp : DFrac F) (m : H V) k dq v :
  internalCmraValid (Auth dp m • Frag k dq v) ⊣⊢@{PROP}
    ∃ v' dq', ⌜✓ dp⌝ ∧ ⌜get? m k = .some v'⌝ ∧ internalCmraValid (dq', v') ∧
      internalCmraIncluded (Option.some (dq, v)) (Option.some (dq', v')) := by
  unfold internalCmraValid internalCmraIncluded
  refine symm ((symm
      (siPure_exist.trans (exists_congr
        (fun v' => siPure_exist.trans (exists_congr
        (fun dq' => siPure_and.trans (and_congr siPure_pure
          (siPure_and.trans (and_congr siPure_pure siPure_and))))))))).trans ?_ )
  constructor
  · apply siPure_mono
    iintro ⟨%v', ⟨%dq', %Hdp', %Hlookup, H⟩⟩
    refine siPure_and.mpr.trans (siPure_mono (and_exists_l.mp.trans (exists_elim (fun c => ?_))))
    intro n ⟨h1, h2⟩; simp only at h1 h2 ⊢
    apply auth_op_frag_validN_iff.mpr
    exists v', dq'; simp [Hdp', Hlookup, h1]; exists c
  · apply siPure_mono
    intro n; simp [SiProp.cmraValid]
    rw [auth_op_frag_validN_iff]
    intro ⟨v', dq', Hdp, Hlookup, Hvalid, ⟨z, Hincl⟩⟩
    apply SiProp.instBI.sExists_intro; exists v'; simp only
    apply SiProp.instBI.sExists_intro; exists dq'; simp only
    refine ⟨Hdp, Hlookup, Hvalid, ?_⟩
    apply SiProp.instBI.sExists_intro
    exists z; simp only; exact Hincl

@[rocq_alias gmap_view_both_validI]
theorem auth_op_frag_one_validI [Sbi PROP] (dp : DFrac F) (m : H V) k v :
  internalCmraValid (Auth dp m • Frag k (.own One.one) v) ⊣⊢@{PROP}
    ⌜✓ dp⌝ ∧ internalCmraValid v ∧ internalEq (get? m k) (.some v) := by
  unfold internalCmraValid internalEq
  refine symm ((and_congr_r siPure_and).symm.trans
    ((and_congr_l siPure_pure).symm.trans (siPure_and.symm.trans ?_)))
  constructor
  <;> (apply siPure_mono; intro n; simp only [SiProp.cmraValid]; rw [auth_op_frag_one_validN_iff]; exact id)

@[rocq_alias gmap_view_both_validI_total]
theorem auth_op_frag_validI_total [Sbi PROP] [CMRA.IsTotal V] (dp : DFrac F) (m : H V) k dq v :
  internalCmraValid (Auth dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      internalCmraValid v' ∧ internalCmraIncluded v v' := by
  unfold internalCmraValid internalCmraIncluded
  refine trans ?_
    (siPure_exist.trans (exists_congr (fun v => siPure_and.trans (and_congr siPure_pure
      (siPure_and.trans (and_congr siPure_pure (siPure_and.trans (and_congr siPure_pure siPure_and)))))))).mp
  apply siPure_mono
  intro n; simp [SiProp.cmraValid]; intro hvalid
  have ⟨v', Hdp, Hdq, Hlookup, Hv', ⟨z, Hincl⟩⟩ := auth_op_frag_validN_total_iff hvalid
  apply SiProp.instBI.sExists_intro; exists v'; simp only
  refine ⟨Hdp, Hdq, Hlookup, Hv', ?_⟩
  apply SiProp.instBI.sExists_intro; exists z; simp only; exact Hincl

@[rocq_alias gmap_view_frag_op_validI]
theorem frag_op_frag_validI [Sbi PROP] k dq1 dq2 v1 v2 :
  internalCmraValid (Frag (F := F) (H := H) (V := V) k dq1 v1 • Frag k dq2 v2) ⊣⊢@{PROP}
    ⌜✓ (dq1 • dq2)⌝ ∧ internalCmraValid (v1 • v2) := by
  unfold internalCmraValid
  refine (symm ((and_congr_l siPure_pure.symm).trans (siPure_and.symm.trans ?_)))
  constructor
  <;> (apply siPure_mono; intro n; simp only [SiProp.cmraValid]; rw [frag_op_validN_iff]; exact id)

end heap_view

section agree_inclusion

open Iris BI Agree OFE

variable [Sbi PROP] [OFE A]

@[rocq_alias agree_equivI]
theorem agree_equivI (a b : A) :
    internalEq (toAgree a) (toAgree b) ⊣⊢@{PROP} internalEq a b := by
  unfold internalEq
  constructor <;> apply siPure_mono <;> intro n
  · exact Agree.toAgree_injN
  · apply NonExpansive.ne

@[rocq_alias agree_op_invI]
theorem agree_op_invI (x y : Agree A) :
    internalCmraValid (x • y) ⊢@{PROP} internalEq x y := by
  unfold internalCmraValid internalEq
  exact siPure_mono (fun n => op_invN)

@[rocq_alias to_agree_validI]
theorem toAgree_validI (a : A) :
    ⊢@{PROP} internalCmraValid (toAgree a) := by
  unfold internalCmraValid
  apply internalCmraValid_intro
  intro n; simp [validN, toAgree]

@[rocq_alias to_agree_op_validI]
theorem toAgree_op_validI (a b : A) :
    internalCmraValid (toAgree a • toAgree b) ⊣⊢@{PROP} internalEq a b := by
  unfold internalCmraValid internalEq
  constructor <;> apply siPure_mono
  · intro n; exact toAgree_op_validN_iff_dist.mp
  · intro n; exact toAgree_op_validN_iff_dist.mpr

@[rocq_alias to_agree_uninjI]
theorem toAgree_uninjI (x : Agree A) :
    internalCmraValid x ⊢@{PROP} ∃ a, internalEq (toAgree a) x := by
  unfold internalCmraValid internalEq
  refine trans (siPure_mono ?_) siPure_exist.mp
  intro n hvalid
  have ⟨a, heq⟩ := toAgree_uninjN hvalid
  apply SiProp.instBI.sExists_intro; exists a
  exact heq

@[rocq_alias agree_op_equiv_to_agreeI]
theorem agree_op_equiv_toAgreeI (x y : Agree A) (a : A) :
    internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq x y ∧ internalEq y (toAgree a) := by
  have hxy : internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq x y := by
    refine internalEq.rewrite' (fun o => internalCmraValid o) internalEq.symm ?_ |>.trans (agree_op_invI x y)
    refine (absorbingly_internalEq (x • y) (toAgree a)).mpr.trans ?_
    have valid_a : internalEq (x • y) (toAgree a) ⊢@{PROP} internalCmraValid (toAgree a) :=
      emp_sep.2.trans (sep_mono_l (toAgree_validI a)) |>.trans sep_elim_l
    refine (absorbingly_mono valid_a).trans absorbing
  apply and_intro hxy
  have hxa : internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq x (toAgree a) := by
    letI : NonExpansive (x • ·) := CMRA.op_ne
    have hxx_a : internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq (x • x) (toAgree a) :=
      (and_intro (hxy.trans (internalEq.of_internalEquiv_ne (x • ·))) .rfl).trans internalEq.trans
    have hxx_x : internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq (x • x) x :=
      emp_sep.2.trans (sep_mono_l (internalEq.of_equiv Agree.idemp)) |>.trans sep_elim_l
    refine (and_intro (hxx_x.trans internalEq.symm) hxx_a).trans internalEq.trans
  refine (and_intro (hxy.trans internalEq.symm) hxa).trans internalEq.trans

@[rocq_alias agree_includedI]
theorem agree_includedI (x y : Agree A) :
    internalCmraIncluded x y ⊣⊢@{PROP} internalEq y (x • y) := by
  unfold internalCmraIncluded internalEq
  constructor
  · refine siPure_mono (exists_elim (fun c => ?_))
    exact (fun n Heq => (includedN.mp ⟨c, Heq⟩).trans op_commN)
  · refine siPure_mono (exists_intro' y ?_)
    exact entails_preorder.refl

@[rocq_alias to_agree_includedI]
theorem toAgree_includedI (a b : A) :
    internalCmraIncluded (toAgree a) (toAgree b) ⊣⊢@{PROP} internalEq a b := by
  unfold internalCmraIncluded internalEq
  constructor
  · refine siPure_mono (exists_elim (fun c => ?_))
    exact (fun n Heq => toAgree_includedN.mp ⟨c, Heq⟩)
  · refine siPure_mono ?_
    show SiProp.internalEq a b ⊢ (∃ c, SiProp.internalEq (toAgree b) (toAgree a • c))
    refine exists_intro' (toAgree a) ?_
    exact internalEq_entails.mpr (fun n heq => Dist.trans (NonExpansive.ne heq.symm) (idemp.symm n))

end agree_inclusion
end Iris
