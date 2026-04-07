/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

### agree:
- [x] agree_includedI
- [x] to_agree_includedI
- [] agree_equivI
- [] agree_op_invI
- [] to_agree_validI
- [] to_agree_op_validI
- [] to_agree_uninjI
- [] agree_op_equiv_to_agreeI

### other sections:
- general algebra (ucmra_unit_validI, cmra_validI_op_r/l, cmra_later_opI, etc.)
- gmap_ofe (gmap_equivI, gmap_union_equiv_eqI)
- gmap_cmra (gmap_validI, singleton_validI)
- list_ofe (list_equivI)
- excl (excl_equivI, excl_validI, excl_includedI)
- csum_ofe/csum_cmra (csum_equivI, csum_validI, csum_includedI)
- view (view_both_dfrac_validI, view_both_validI, view_auth_validI, view_frag_validI)
- auth (auth_auth_validI, auth_frag_validI, auth_both_validI, etc.)
- excl_auth (excl_auth_agreeI)
- dfrac_agree (dfrac_agree_validI, frac_agree_validI)
-/
module

public import Iris.ProofMode

@[expose] public section

-- TODO: Need sbi_unfold to make these proofs less horrific
section heap_view

open Iris HeapView BI Std PartialMap LawfulPartialMap

variable {F K V : Type _} {H : Type _ → Type _}
variable [UFraction F]
variable [LawfulPartialMap H K]
variable [CMRA V]

@[rocq_alias gmap_view_both_dfrac_validI]
theorem auth_op_frag_validI [Sbi PROP] (dp : DFrac F) (m : H V) k dq v :
  internalCmraValid (HeapView.Auth dp m • HeapView.Frag k dq v) ⊣⊢@{PROP}
    ∃ v' dq', ⌜✓ dp⌝ ∧ ⌜get? m k = .some v'⌝ ∧ internalCmraValid (dq', v') ∧
      internalCmraIncluded (Option.some (dq, v)) (Option.some (dq', v')) := by
  unfold internalCmraValid internalCmraIncluded
  refine BIBase.BiEntails.symm ((BIBase.BiEntails.symm
      (siPure_exist.trans (BI.exists_congr
        (fun v' => siPure_exist.trans (BI.exists_congr
        (fun dq' => siPure_and.trans (BI.and_congr siPure_pure
          (siPure_and.trans (BI.and_congr siPure_pure siPure_and))))))))).trans ?_ )
  constructor
  · apply siPure_mono
    iintro ⟨%v', ⟨%dq', %Hdp', %Hlookup, H⟩⟩
    refine siPure_and.mpr.trans (siPure_mono (BI.and_exists_l.mp.trans (BI.exists_elim (fun c => ?_))))
    intro n ⟨h1, h2⟩
    simp only at h1 h2 ⊢
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
  internalCmraValid (HeapView.Auth dp m • HeapView.Frag k (.own One.one) v) ⊣⊢@{PROP}
    ⌜✓ dp⌝ ∧ internalCmraValid v ∧ internalEq (get? m k) (.some v) := by
  unfold internalCmraValid internalEq
  refine BIBase.BiEntails.symm
    ((BI.and_congr_r siPure_and).symm.trans ((BI.and_congr_l siPure_pure).symm.trans (siPure_and.symm.trans ?_)))
  constructor
  <;> (apply siPure_mono; intro n; simp only [SiProp.cmraValid]; rw [auth_op_frag_one_validN_iff]; exact id)

@[rocq_alias gmap_view_both_validI_total]
theorem auth_op_frag_validI_total [Sbi PROP] [CMRA.IsTotal V] (dp : DFrac F) (m : H V) k dq v :
  internalCmraValid (HeapView.Auth dp m • HeapView.Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      internalCmraValid v' ∧ internalCmraIncluded v v' := by
  unfold internalCmraValid internalCmraIncluded
  refine Entails.trans ?_
    (siPure_exist.trans (BI.exists_congr (fun v => siPure_and.trans (BI.and_congr siPure_pure
      (siPure_and.trans (BI.and_congr siPure_pure (siPure_and.trans (BI.and_congr siPure_pure siPure_and)))))))).mp
  apply siPure_mono
  intro n; simp [SiProp.cmraValid]; intro hvalid
  have ⟨v', Hdp, Hdq, Hlookup, Hv', ⟨z, Hincl⟩⟩ := auth_op_frag_validN_total_iff hvalid
  apply SiProp.instBI.sExists_intro; exists v'; simp only
  refine ⟨Hdp, Hdq, Hlookup, Hv', ?_⟩
  apply SiProp.instBI.sExists_intro; exists z; simp only; exact Hincl

@[rocq_alias gmap_view_frag_op_validI]
theorem frag_op_frag_validI [Sbi PROP] k dq1 dq2 v1 v2 :
  internalCmraValid (HeapView.Frag (F := F) (H := H) (V := V) k dq1 v1 • HeapView.Frag k dq2 v2) ⊣⊢@{PROP}
    ⌜✓ (dq1 • dq2)⌝ ∧ internalCmraValid (v1 • v2) := by
  unfold internalCmraValid
  refine (BIBase.BiEntails.symm ((BI.and_congr_l siPure_pure.symm).trans (siPure_and.symm.trans ?_)))
  constructor
  <;> (apply siPure_mono; intro n; simp only [SiProp.cmraValid]; rw [frag_op_validN_iff]; exact id)

end heap_view

section agree_inclusion

open Iris BI Agree

variable [Sbi PROP] [OFE A]

@[rocq_alias agree_includedI]
theorem agree_includedI (x y : Agree A) :
    internalCmraIncluded x y ⊣⊢@{PROP} internalEq y (x • y) := by
  unfold internalCmraIncluded internalEq
  constructor
  · refine siPure_mono (BI.exists_elim (fun c => ?_))
    intro n Heq
    exact (Agree.includedN.mp ⟨c, Heq⟩).trans op_commN
  · refine siPure_mono (BI.exists_intro' y ?_)
    exact entails_preorder.refl

@[rocq_alias to_agree_includedI]
theorem toAgree_includedI (a b : A) :
    internalCmraIncluded (toAgree a) (toAgree b) ⊣⊢@{PROP} internalEq a b := by
  unfold internalCmraIncluded internalEq
  constructor
  · refine siPure_mono (BI.exists_elim (fun c => ?_))
    intro n Heq
    exact Agree.toAgree_includedN.mp ⟨c, Heq⟩
  · refine siPure_mono ?_
    show SiProp.internalEq a b ⊢ (∃ c, SiProp.internalEq (toAgree b) (toAgree a • c))
    refine BI.exists_intro' (toAgree a) ?_
    exact internalEq_entails.mpr (fun n heq => OFE.instTransDist.trans (OFE.NonExpansive.ne heq.symm) (Agree.idemp.symm n))

end agree_inclusion
