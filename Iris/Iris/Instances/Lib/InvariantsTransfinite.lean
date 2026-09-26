/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko, Iris-Lean Contributors
-/
module

public import Iris.Algebra
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Std.Namespaces
public import Iris.Instances.IProp
public import Iris.Instances.Lib.FUpdTransfinite
public import Iris.Std.CoPset
import Iris.Instances.Lib.WSat

/-! # Invariants over arbitrary step-indices (Transfinite Iris)

This file ports `theories/base_logic/lib/invariants.v` of Transfinite Iris: invariants for the
credit-free fancy update of `Iris.Instances.Lib.FUpdTransfinite`, over any type of step-indices.
The proofs follow `Iris.Instances.Lib.Invariants`.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris OFE COFE BI

section InvariantDefinition

variable {GF : BundledGFunctors} [W : WsatGS GF]


def inv (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(□ ∀ E, ⌜↑N ⊆ E⌝ → |={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True))

def own_inv (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(∃ i, ⌜i ∈ (↑N : CoPset)⌝ ∧ ownI i P)

end InvariantDefinition

section Instances

open ProofMode

variable {GF : BundledGFunctors} [W : WsatGS GF]

instance inv_contractive (N : Namespace) : Contractive (inv (GF := GF) N) where
  distLater_dist {n x y} H := by
    simp only [inv]
    refine intuitionistically_ne.ne ?_
    refine forall_ne (fun i => ?_)
    refine imp_ne.ne .rfl ?_
    refine BIFUpdate.ne.ne ?_
    refine sep_ne.ne ?_ ?_
    · exact Contractive.distLater_dist H
    · refine wand_ne.ne ?_ .rfl
      exact Contractive.distLater_dist H

instance inv_ne (N : Namespace) : NonExpansive (inv (GF := GF) N) := ne_of_contractive _


instance inv_persistent (N : Namespace) (P : IProp GF) : Persistent (inv N P) := by
  simp only [inv]
  infer_instance

instance own_inv_persistent (N : Namespace) (P : IProp GF) : Persistent (own_inv N P) := by
  simp only [own_inv]
  infer_instance

theorem except_0_inv (N : Namespace) (P : IProp GF) : ⊢ ◇ inv N P -∗ inv N P := by
  simp only [inv]
  iintro #H
  imodintro
  iintro %E %Hsub
  imod H
  iapply H
  itrivial

instance is_except_0_inv (N : Namespace) (P : IProp GF) : IsExcept0 (inv N P) where
  is_except0 := by iintro H; iapply except_0_inv $$ H

instance intoInv_inv (N : Namespace) (P : IProp GF) : IntoInv (inv N P) N := {}

set_option synthInstance.checkSynthOrder false in
instance intoAcc_inv (N : Namespace) (P : IProp GF) E :
    IntoAcc (X := Unit) (inv N P) (↑N ⊆ E) iprop(True) (fupd E (E \ ↑N)) (fupd (E \ ↑N) E)
      (fun _ => iprop(▷ P)) (fun _ => iprop(▷ P)) (fun _ => none) where
  into_acc := by
    dsimp only [inv, accessor, Option.getD]
    iintro %x #Hinv -
    imod Hinv $$ %E [] with ⟨HP, Hclose⟩
    · itrivial
    · iexists ()
      imodintro
      isplitl [HP]
      · iassumption
      · iintro HP
        iapply (BIFUpdate.mono true_emp.mp)
        iapply Hclose $$ HP

end Instances

section BasicLemmas

open Iris Iris.Std LawfulSet

variable {GF : BundledGFunctors} [W : WsatGS GF]

-- FIXME: Use iframe

theorem own_inv_acc (E : CoPset) (N : Namespace) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢ own_inv N P ={E, E \ ↑N}=∗ ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  simp only [own_inv, FUpd.fupd, uPred_fupd]
  iintro ⟨%i, %Hin, #Hown⟩ ⟨Hwsat, HE⟩
  have Hsub' : ({i} : CoPset) ⊆ ↑N := by
    intro x; simp only [mem_singleton]
    rintro ⟨⟩
    apply Hin
  have HEEQ : ↑N ∪ (E \ ↑N) = E := by
    rw [union_comm, ←diff_subset_decomp Hsub]
  have HNEQ : {i} ∪ (nclose N \ {i}) = ↑N := by
    rw [union_comm, ←diff_subset_decomp Hsub']
  ihave HE : ownE (↑N ∪ (E \ ↑N)) $$ [HE]
  · rw [HEEQ]; iexact HE
  icases ownE_op disjoint_diff_right $$ HE with ⟨HE1, HE2⟩
  ihave HE1 : ownE ({i} ∪ (nclose N \ {i})) $$ [HE1]
  · rw [HNEQ]; iexact HE1
  icases ownE_op disjoint_diff_right $$ HE1 with ⟨HE1, HE3⟩
  imodintro
  imodintro
  icases ownI_open $$ [$Hwsat $HE1 $Hown] with ⟨$, $, HD⟩
  iframe
  iintro HP ⟨Hwsat, HE⟩
  imodintro
  imodintro
  icases ownI_close $$ [$HP $Hwsat $HD $Hown] with ⟨$, HE1⟩
  icases ownE_op disjoint_diff_right $$ [$HE1 $HE3] with HE1
  rw [HNEQ]
  icases ownE_op disjoint_diff_right $$ [$HE1 $HE] with HE
  rw [HEEQ]
  iframe

theorem own_inv_alloc (N : Namespace) (E : CoPset) (P : IProp GF) :
  ⊢ ▷ P ={E}=∗ own_inv N P := by
  simp only [own_inv, FUpd.fupd, uPred_fupd]
  iintro HP ⟨Hw, HE⟩
  imod ownI_alloc (· ∈ (↑N : CoPset)) P $$ [HP Hw] with ⟨%i, %Hin, Hw, HI⟩
  · intro E; apply fresh_name
  · isplitl [Hw] <;> iassumption
  · imodintro; imodintro; iframe
    itrivial

theorem own_inv_alloc_open (N : Namespace) (E : CoPset) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢ |={E, E \ ↑N}=> own_inv N P ∗ (▷P ={E \ ↑N, E}=∗ True) := by
  simp only [own_inv, FUpd.fupd, uPred_fupd]
  iintro ⟨Hw, HE⟩
  imod ownI_alloc_open $$ Hw with ⟨%i, %Hin, Hcont, #HI, HD⟩
  · intro _; apply fresh_name
  have Hsub' : ({i} : CoPset) ⊆ ↑N := by
    intro x; simp only [mem_singleton]
    rintro ⟨⟩
    apply Hin
  have HEEQ : ↑N ∪ (E \ ↑N) = E := by
    rw [union_comm, ←diff_subset_decomp Hsub]
  have HNEQ : {i} ∪ (nclose N \ {i}) = ↑N := by
    rw [union_comm, ←diff_subset_decomp Hsub']
  ihave HE : ownE (↑N ∪ (E \ ↑N)) $$ [HE]
  · rw [HEEQ]; iexact HE
  icases ownE_op disjoint_diff_right $$ HE with ⟨HE1, HEN⟩
  ihave HE1 : ownE ({i} ∪ (nclose N \ {i})) $$ [HE1]
  · rw [HNEQ]; iexact HE1
  icases ownE_op disjoint_diff_right $$ HE1 with ⟨HEi, HENi⟩
  imodintro
  imodintro
  ispecialize Hcont $$ HEi
  isplitl [Hcont]; iassumption
  isplitl [HEN]; iassumption
  isplitl [HI]
  · iexists i; isplit
    · ipureintro; assumption
    · iexact HI
  iintro HP ⟨Hw, HE⟩
  icases ownI_close $$ [HP Hw HD] with ⟨Hwsat, HE1⟩
  · isplitl [Hw]; iassumption
    isplitl [HI]; iassumption
    isplitl [HP]; iassumption
    iassumption
  imodintro
  imodintro
  isplitl [Hwsat]; iassumption
  icases ownE_op disjoint_diff_right $$ [HENi HE1] with HE1
  · isplitl [HE1]; iassumption
    iassumption
  rw [HNEQ]
  icases ownE_op disjoint_diff_right $$ [HE1 HE] with HE
  · isplitl [HE1]; iassumption
    iassumption
  rw [HEEQ]
  isplitl [HE]; iassumption
  apply true_intro

theorem own_inv_to_inv (M : Namespace) (P : IProp GF) :
    ⊢ own_inv M P -∗ inv M P := by
  simp only [inv]
  iintro #I
  imodintro
  iintro %E %Hsub
  iapply own_inv_acc _ _ _ Hsub $$ I

end BasicLemmas

section Allocation

variable {GF : BundledGFunctors} [W : WsatGS GF]

theorem inv_alloc (N : Namespace) (E : CoPset) (P : IProp GF) :
    ⊢ ▷ P ={E}=∗ inv N P := by
  iintro HP
  imod own_inv_alloc N $$ HP with H
  imodintro
  iapply own_inv_to_inv $$ H

theorem inv_alloc_open (N : Namespace) (E : CoPset) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢ |={E, E \ ↑N}=> inv N P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  imod own_inv_alloc_open _ _ P Hsub with ⟨Hown, Hcl⟩
  imodintro
  isplitr [Hcl]
  · iapply own_inv_to_inv $$ Hown
  · iexact Hcl

end Allocation

section Access

open Iris Iris.Std LawfulSet

variable {GF : BundledGFunctors} [W : WsatGS GF]

theorem inv_acc {E : CoPset} {N : Namespace} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ inv N P ={E, E \ ↑N}=∗ ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  simp only [inv]
  iintro #HI
  iapply HI $$ %E []
  ipureintro; assumption

theorem inv_acc_strong {E : CoPset} {N : Namespace} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ inv N P ={E, E \ ↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E', ↑N ∪ E'}=∗ True := by
  iintro Hinv
  icases inv_acc subset_refl $$ Hinv with H
  rw [diff_all]
  icases fupd_mask_frame_right disjoint_diff_right (Ef := (E \ ↑N)) $$ H with H
  rw [union_empty_left, ←union_comm, ←diff_subset_decomp Hsub]
  imod H with ⟨HP, H⟩
  imodintro
  isplitl [HP]; iassumption
  iintro %E' HP
  ispecialize H $$ HP
  icases fupd_mask_frame_right disjoint_empty_left (Ef := E') $$ H with H
  rw [union_empty_left]
  imod H; imodintro; itrivial

theorem inv_acc_timeless {E : CoPset} {N : Namespace} {P : IProp GF} [Timeless P] (Hsub : ↑N ⊆ E) :
    ⊢ inv N P ={E, E \ ↑N}=∗ P ∗ (P ={E \ ↑N, E}=∗ True) := by
  iintro HI
  imod inv_acc Hsub $$ HI with ⟨>HP, H⟩
  imodintro
  isplitl [HP]; iassumption
  iintro HP
  iapply H
  inext; iassumption

theorem inv_open_fupd {E : CoPset} {N : Namespace} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ inv N P -∗ (▷ P ∗ Q ={E \ N}=∗ P ∗ R) -∗ Q ={E}=∗ R := by
  iintro #Hinv H HQ
  imod inv_acc Hsub $$ Hinv with ⟨HP, Hclose⟩
  imod H $$ [$] with ⟨HP, HR⟩; iframe
  imod Hclose $$ [$HP] with -
  itrivial

end Access

section Modification

variable {GF : BundledGFunctors} [W : WsatGS GF]

/-! `inv_alter` and `inv_combine` of standard Iris are not sound for transfinite step-indices,
since `▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q` fails. Transfinite Iris replaces them by versions for timeless
propositions. -/

theorem inv_iff (N : Namespace) (P Q : IProp GF) :
    ⊢ inv N P -∗ ▷ □ (P ↔ Q) -∗ inv N Q := by
  simp only [inv]
  iintro #HI #HPQ
  imodintro
  iintro %E Hsub
  imod HI $$ %E Hsub with ⟨HP, H⟩
  imodintro
  isplitl [HP]
  · inext
    icases HPQ with ⟨H1, -⟩
    iapply H1 $$ HP
  · iintro HQ
    iapply H
    inext
    icases HPQ with ⟨-, H2⟩
    iapply H2 $$ HQ

theorem inv_alter_timeless (N : Namespace) (P Q : IProp GF) [Timeless P] :
    ⊢ inv N P -∗ □ (P -∗ Q ∗ ▷ (Q -∗ P)) -∗ inv N Q := by
  simp only [inv]
  iintro #HI #HPQ
  imodintro
  iintro %E Hsub
  imod HI $$ %E Hsub with ⟨>HP, H⟩
  imodintro
  icases HPQ $$ HP with ⟨HQ, HQP⟩
  isplitl [HQ]
  · inext
    iexact HQ
  · iintro HQ
    iapply H
    inext
    iapply HQP $$ HQ

end Modification

section Splitting

variable {GF : BundledGFunctors} [W : WsatGS GF]

theorem inv_split_l_timeless (N : Namespace) (P Q : IProp GF) [Timeless P] [Timeless Q] :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N P := by
  iintro #H
  iapply inv_alter_timeless $$ H
  imodintro
  iintro ⟨HP, HQ⟩
  isplitl [HP]
  · iexact HP
  · inext
    iintro HP
    isplitl [HP] <;> iassumption

theorem inv_split_r_timeless (N : Namespace) (P Q : IProp GF) [Timeless P] [Timeless Q] :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N Q := by
  iintro #H
  iapply inv_alter_timeless $$ H
  imodintro
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · inext
    iintro HQ
    isplitl [HP] <;> iassumption

theorem inv_split (N : Namespace) (P Q : IProp GF) [Timeless P] [Timeless Q] :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N P ∗ inv N Q := by
  iintro #H
  ihave H1 := inv_split_l_timeless $$ H
  ihave H2 := inv_split_r_timeless $$ H
  isplit <;> iassumption

end Splitting

end Iris.Transfinite

