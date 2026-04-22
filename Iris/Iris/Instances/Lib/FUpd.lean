/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Instances.IProp
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.BI.Plainly

@[expose] public section

namespace Iris

open Iris OFE COFE BI Auth

section InvG

@[rocq_alias has_lc]
abbrev hasLc := Bool

@[rocq_alias invGpreS]
class InvGpreS (GF : BundledGFunctors) where
  toWsatGpreS : WsatGpreS GF
  toLcGpreS : LcGpreS GF

attribute [reducible, instance] InvGpreS.toWsatGpreS
attribute [reducible, instance] InvGpreS.toLcGpreS

@[rocq_alias invGS_gen]
class InvGS_gen (hlc : outParam hasLc) (GF : BundledGFunctors) extends InvGpreS GF where
  toWsatGS : WsatGS GF
  toLcGS : LcGS GF

attribute [reducible, instance] InvGS_gen.toWsatGS
attribute [reducible, instance] InvGS_gen.toLcGS

abbrev InvGS := InvGS_gen true

#rocq_ignore «invΣ» "Not needed"
#rocq_ignore «subG_invΣ» "Not needed"

end InvG

section FUpd

variable {GF : BundledGFunctors} {hlc : Bool} [InvGS_gen hlc GF]

#rocq_ignore uPred_fupd_def "Not needed"
#rocq_ignore uPred_fupd_aux "Not needed"
#rocq_ignore uPred_fupd_unseal "Not needed"

@[rocq_alias uPred_fupd]
def uPred_fupd (E1 E2 : CoPset) (P : IProp GF) : IProp GF :=
  iprop(wsat ∗ ownE E1 -∗ le_upd_if hlc iprop(◇ (wsat ∗ ownE E2 ∗ P)))

instance {E1 E2 : CoPset} : NonExpansive (uPred_fupd (GF := GF) (hlc := hlc) E1 E2) where
  ne {_ _ _} h := by
    simp only [uPred_fupd]
    refine wand_ne.ne .rfl ?_
    refine le_upd_if_ne.ne ?_
    refine except0_ne.ne ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl h

instance uPred_fupd_instance : FUpd (IProp GF) where
  fupd := uPred_fupd

end FUpd

section Instances

open Std.LawfulSet

#rocq_ignore uPred_fupd_mixin "Not needed"

@[rocq_alias uPred_bi_fupd]
instance uPred_bi_fupd {GF : BundledGFunctors} [InvGS_gen hlc GF] : BIFUpdate (IProp GF) where
  fupd := uPred_fupd
  subset Hsub := by
    simp only [uPred_fupd]
    iintro ⟨Hwsat, HE⟩
    rw [diff_subset_decomp Hsub]
    ihave ⟨HE1, HE2⟩ := (ownE_op (disjoint_symm disjoint_diff_right)).mp $$ HE
    imodintro; imodintro
    isplitl [Hwsat]; iassumption
    isplitl [HE2]; iassumption
    iintro ⟨Hwsat, HE⟩
    imodintro; imodintro
    isplitl [Hwsat]; iassumption
    ihave HE := (ownE_op (disjoint_symm disjoint_diff_right)).mpr $$ [HE1 HE]
    · isplitl [HE1] <;> iassumption
    isplitl [HE]; iassumption
    simp
  except0 {E1 E2 P} := by
    simp only [uPred_fupd]
    iintro >H; iexact H
  mono H := by
    simp only [uPred_fupd]
    iintro H ⟨Hwsat, HE⟩
    ihave H := H $$ [Hwsat HE]; isplitl [Hwsat] <;> iassumption
    iapply le_upd_if_mono $$ H
    iintro >⟨H1, H2, H3⟩; imodintro
    isplitl [H1]; iassumption
    isplitl [H2]; iassumption
    iapply H $$ H3
  trans {_ _ _ _} := by
    simp only [uPred_fupd]
    iintro H ⟨Hwsat, HE⟩
    iapply le_upd_if_trans
    ihave H := H $$ [Hwsat HE]; isplitl [Hwsat] <;> iassumption
    iapply le_upd_if_mono $$ H
    iintro >⟨H1, H2, H3⟩
    iapply H3 $$ [H1 H2]; isplitl [H1] <;> iassumption
  mask_frame_r' {_ _ _ _} Hdisj := by
    simp only [uPred_fupd]
    iintro H ⟨Hwsat, HE⟩
    ihave ⟨HE1, HE2⟩ := ownE_op Hdisj $$ HE
    ihave >H := H $$ [Hwsat HE1]; isplitl [Hwsat] <;> iassumption
    imodintro
    imod H with ⟨H1, H2, H3⟩; imodintro
    ihave ⟨%Hdisj, HE⟩ := ownE_op_iff.mpr $$ [H2 HE2]
    · isplitl [H2] <;> iassumption
    isplitl [H1]; iassumption
    isplitl [HE]; iassumption
    iapply H3
    ipure_intro; assumption
  frame_r {_ _ _ _} := by
    simp only [uPred_fupd]
    iintro ⟨H, Hx⟩ ⟨Hwsat, HE⟩
    ispecialize H $$ [Hwsat HE]; isplitl [Hwsat] <;> iassumption
    ihave H := le_upd_if_frame_r $$ [H Hx]
    · isplitl [H]
      · iexact H
      · iexact Hx
    imod H with ⟨>⟨H1, H2, H3⟩, H4⟩; imodintro
    imodintro
    isplitl [H1]; iassumption
    isplitl [H2]; iassumption
    isplitl [H3]; iassumption
    iassumption

@[rocq_alias uPred_bi_bupd_fupd]
instance {GF : BundledGFunctors} [InvGS_gen hlc GF] : BIUpdateFUpdate (IProp GF) where
  fupd_of_bupd {_ _} := by
    iintro H
    simp only [fupd, uPred_fupd]
    iintro ⟨Hwsat, HE⟩
    imod H; imodintro; imodintro
    isplitl [Hwsat]; iassumption
    isplitl [HE]; iassumption
    iassumption

@[rocq_alias uPred_bi_fupd_sbi_no_lc]
instance uPred_bi_fupd_plainly_no_lc {GF : BundledGFunctors} [INV : InvGS_gen false GF] :
    BIFUpdatePlainly (IProp GF) where
  fupd_plainly_keep_l E E' P Q := by
    simp only [fupd, uPred_fupd, le_upd_if, Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H, Hx⟩ ⟨Hwsat, HE⟩
    ihave #>HP : ◇ ■ P $$ [H Hx Hwsat HE]
    · imod H $$ Hx [Hwsat HE] with ⟨_, _, H⟩
      · isplitl [Hwsat] <;> iassumption
      iexact H
    imodintro
    isplitl [Hwsat]; iassumption
    isplitl [HE]; iassumption
    isplitl [HP] <;> iassumption
  fupd_plainly_later _ P := by
    simp only [fupd, uPred_fupd, le_upd_if, Bool.false_eq_true, ↓reduceIte]
    iintro H ⟨Hwsat, HE⟩
    ihave #HP : ▷ ◇ ■ P $$ [H Hwsat HE]
    · inext
      imod H $$ [Hwsat HE] with ⟨_, _, H⟩
      · isplitl [Hwsat] <;> iassumption
      iexact H
    imodintro
    isplitl [Hwsat]; iassumption
    isplitl [HE]; iassumption
    imodintro; inext; imod HP; imodintro; iassumption
  fupd_plainly_sForall_2 E P := by
    simp only [fupd, uPred_fupd, le_upd_if, Bool.false_eq_true, ↓reduceIte]
    iintro H ⟨Hwsat, HE⟩
    ihave #HP : ◇ ■ sForall P $$ [H Hwsat HE]
    · imod H $$ [Hwsat HE] with ⟨_, _, H⟩
      · isplitl [Hwsat] <;> iassumption
      iexact H
    imodintro; imod HP; imodintro
    isplitl [Hwsat]; iassumption
    isplitl [HE]; iassumption
    iclear H
    iexact HP

end Instances

section LaterCreditLemmas

variable {GF : BundledGFunctors} [InvGS GF]

@[rocq_alias lc_fupd_elim_later]
theorem lc_fupd_elim_later {E : CoPset} {P : IProp GF} : ⊢ £ 1 -∗ (▷ P) -∗ |={E}=> P := by
  iintro Hcr HP
  simp only [fupd, uPred_fupd]
  iintro ⟨Hwsat, HE⟩
  simp only [le_upd_if, ↓reduceIte]
  iapply le_upd_later $$ Hcr
  inext; imodintro
  isplitl [Hwsat]; iassumption
  isplitl [HE]; iassumption
  iassumption

@[rocq_alias lc_fupd_add_later]
theorem lc_fupd_add_later {E : CoPset} {P : IProp GF} : ⊢ £ 1 -∗ (|={E}=> ▷ P) -∗ |={E}=> P := by
  iintro Hcr HP
  simp only [fupd, uPred_fupd]
  iintro ⟨Hwsat, HE⟩
  simp only [le_upd_if, ↓reduceIte]
  -- FIXME: Is it possible to make >> work instead of adding the spaces between them?
  ihave > > ⟨H1, H2, H3⟩ := HP $$ [Hwsat HE]
  · isplitl [Hwsat] <;> iassumption
  imod le_upd_later $$ Hcr H3 with H3
  imodintro; imodintro
  isplitl [H1]; iassumption
  isplitl [H2]; iassumption
  iassumption

@[rocq_alias lc_fupd_add_laterN]
theorem lc_fupd_add_laterN (n : Nat) {E : CoPset} {P : IProp GF} :
    ⊢ £ n -∗ (|={E}=> ▷^[n] P) -∗ |={E}=> P := by
  induction n generalizing P with
  | zero =>
    iintro _ >H
    ihave H := laterN_0.mp (PROP := IProp GF) $$ H
    imodintro; iexact H
  | succ n IH =>
    iintro ⟨Hcr, Hcrs⟩ >HP
    ihave HP := (laterN_later n).mp $$ HP
    iapply lc_fupd_add_later $$ Hcr
    iapply IH $$ Hcrs [HP]
    imodintro; iexact HP

end LaterCreditLemmas

section Soundness

open Std.LawfulSet

variable {GF : BundledGFunctors}

@[rocq_alias fupd_soundness_lc]
theorem fupd_soundness_lc [InvGpreS GF] {E1 E2 : CoPset} {P : IProp GF} [Plain P]
     (H : ∀ (_ : InvGS GF), ⊢ £ m -∗ |={E1,E2}=> P) : ⊢ P := by
  iapply lc_soundness m.succ
  iintro %Hc ⟨Hcr, Hcrs⟩
  simp only [fupd, uPred_fupd, le_upd_if, ↓reduceIte] at H
  imod wsat_alloc with ⟨%W, Hwsat, HE⟩
  let LC : InvGS GF := { toWsatGS := W, toLcGS := Hc }
  specialize H LC
  rw [diff_subset_decomp (s₂ := ⊤) ((fun _ _ => CoPset.mem_full) : E1 ⊆ ⊤)]
  ihave ⟨HE1, HE2⟩ := (ownE_op (disjoint_symm disjoint_diff_right)).mp $$ HE
  imod H $$ Hcrs [Hwsat HE2] with ⟨_, _, H⟩
  · isplitl [Hwsat] <;> iassumption
  iapply le_upd_later $$ Hcr [H]
  iapply except0_into_later $$ H

#rocq_ignore fupd_soundness_no_lc_unfold "Proof inlined in fupd_soundness_no_lc"

@[rocq_alias fupd_soundness_no_lc]
theorem fupd_soundness_no_lc [InvGpreS GF] {E1 E2 : CoPset} {P : IProp GF} [Plain P]
    (H : ∀ (_ : InvGS_gen false GF), ⊢ £ m -∗ |={E1,E2}=> P) : ⊢ P := by
  iapply lc_soundness m.succ
  iintro %Hc ⟨Hcr, Hcrs⟩
  simp only [fupd, uPred_fupd, le_upd_if, Bool.false_eq_true, ↓reduceIte] at H
  imod wsat_alloc with ⟨%W, Hwsat, HE⟩
  let LC : InvGS_gen false GF := { toWsatGS := W, toLcGS := Hc }
  specialize H LC
  rw [diff_subset_decomp (s₂ := ⊤) ((fun _ _ => CoPset.mem_full) : E1 ⊆ ⊤)]
  ihave ⟨HE1, HE2⟩ := (ownE_op (disjoint_symm disjoint_diff_right)).mp $$ HE
  imod H $$ Hcrs [Hwsat HE2] with ⟨_, _, H⟩
  · isplitl [Hwsat] <;> iassumption
  iapply le_upd_later $$ Hcr [H]
  iapply except0_into_later $$ H

@[rocq_alias fupd_soundness_gen]
theorem fupd_soundness_gen (hlc : Bool) [InvGpreS GF] (m : Nat) {E1 E2 : CoPset} {P : IProp GF} [Plain P] :
  (∀ (_ : InvGS_gen hlc GF), ⊢ £ m -∗ |={E1,E2}=> P) → ⊢ P := by
  cases hlc
  · apply fupd_soundness_no_lc
  · apply fupd_soundness_lc

end Soundness

section StepIndexed

open Iris Std LawfulSet BIFUpdatePlainly

variable {GF : BundledGFunctors}

@[rocq_alias step_fupdN_soundness_no_lc]
theorem step_fupdN_soundness_no_lc [InvGpreS GF] (n m : Nat) {P : IProp GF} [Plain P]
    (H : ∀ (_ : InvGS_gen false GF), ⊢ £ m -∗ |={⊤,∅}=> |={∅}▷=>^[n] P) : ⊢ P := by
  apply laterN_soundness (n := n.succ)
  letI _ : Persistent iprop(P) := plain_persistent
  apply fupd_soundness_no_lc (E1 := ⊤) (E2 := ⊤) (m := m)
  intro LC
  specialize H LC
  iintro Hcrds
  iapply fupd_plainly_mask (E' := ∅)
  imod H $$ Hcrds with H
  imod step_fupdN_plain $$ H with H
  imodintro
  iapply plainly_mono (laterN_later _).mpr
  iapply laterN_plainly
  inext
  iapply later_plainly.mp
  imod H with #H
  inext
  imodintro; iassumption

@[rocq_alias step_fupdN_soundness_lc]
theorem step_fupdN_soundness_lc [InvGpreS GF] (n m : Nat) {P : IProp GF} [Plain P]
    (H : ∀ (_ : InvGS GF), ⊢ £ m -∗ |={⊤,∅}=> |={∅}▷=>^[n] P) : ⊢ P := by
  apply fupd_soundness_lc (E1 := ⊤) (E2 := ∅) (m := m + n)
  intro LC
  specialize H LC
  iintro Hcrds
  icases lc_split $$ Hcrds with ⟨Hcr1, Hcr2⟩
  imod H $$ Hcr1 with H
  clear H
  istop
  induction n with
  | zero =>
    simp only [Nat.repeat]
    iintro ⟨_, HP⟩
    imodintro
    iassumption
  | succ n IH =>
    simp only [Nat.repeat]
    iintro ⟨⟨Hcr, Hcrs⟩, >H⟩
    imod lc_fupd_elim_later $$ Hcr H with >H
    -- FIXME: direct iapply doesn't work
    ihave IH : £ n ∗ (|={∅}▷=>^[n] P) -∗ |={∅}=> P $$ []
    · refine wand_intro ?_
      refine sep_elim_r.trans ?_
      exact IH
    iapply IH $$ [Hcrs H]
    isplitl [Hcrs]; iassumption
    iassumption

@[rocq_alias step_fupdN_soundness_gen]
theorem step_fupdN_soundness_gen [InvGpreS GF] (n m : Nat) {P : IProp GF} [Plain P] hlc :
    (∀ (_ : InvGS_gen hlc GF), ⊢ £ m -∗ |={⊤,∅}=> |={∅}▷=>^[n] P) → ⊢ P := by
  cases hlc
  · apply step_fupdN_soundness_no_lc
  · apply step_fupdN_soundness_lc

@[rocq_alias step_fupdN_soundness_no_lc']
theorem step_fupdN_soundness_no_lc' [InvGpreS GF] (n m : Nat) {P : IProp GF} [Plain P]
    (H : ∀ (_ : InvGS_gen false GF), ⊢ £ m -∗ |={⊤}[∅]▷=>^[n] P) : ⊢ P := by
  apply step_fupdN_soundness_no_lc n m
  intro LC
  specialize H LC
  iintro Hcr
  cases n with
  | zero =>
    simp only [Nat.repeat] at H ⊢
    iapply fupd_mask_intro_discard empty_subset
    iapply H $$ Hcr
  | succ n =>
    simp only [Nat.repeat] at H ⊢
    imod H $$ Hcr with H
    imodintro; imodintro; inext
    clear H
    imod H
    istop
    induction n with
    | zero =>
      simp only [Nat.repeat]
      iintro HP
      iapply fupd_mask_intro_discard empty_subset
      iassumption
    | succ n IH =>
      simp only [Nat.repeat]
      iintro >H
      imodintro; imodintro; inext
      imod H
      apply IH

@[rocq_alias step_fupdN_soundness_lc']
theorem step_fupdN_soundness_lc' [InvGpreS GF] (n m : Nat) {P : IProp GF} [Plain P]
    (H : ∀ (_ : InvGS GF), ⊢ £ m -∗ |={⊤}[∅]▷=>^[n] P) : ⊢ P := by
  apply fupd_soundness_lc (E1 := ⊤) (E2 := ⊤) (m := m + n)
  intro LC
  specialize H LC
  iintro Hcrds
  icases lc_split $$ Hcrds with ⟨Hcr1, Hcr2⟩
  icases H $$ Hcr1 with H
  clear H
  istop
  induction n with
  | zero =>
    simp only [Nat.repeat]
    iintro ⟨_, HP⟩
    imodintro
    iassumption
  | succ n IH =>
    simp only [Nat.repeat]
    iintro ⟨⟨Hcr, Hcrs⟩, >H⟩
    imod lc_fupd_elim_later $$ Hcr H with >H
    -- FIXME: direct iapply doesn't work
    ihave IH : £ n ∗ (|={⊤}[∅]▷=>^[n] P) -∗ |={⊤}=> P $$ []
    · refine wand_intro ?_
      refine sep_elim_r.trans ?_
      exact IH
    iapply IH $$ [Hcrs H]
    isplitl [Hcrs]; iassumption
    iassumption

end StepIndexed

end Iris

end
