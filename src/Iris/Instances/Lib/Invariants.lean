/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Std.Namespaces
public import Iris.Instances.IProp
public import Iris.Instances.Lib.FUpd
public import Iris.Std.CoPset
import Iris.Instances.Lib.WSat

@[expose] public section

/-! ## Invariants
TODO: into_inv_inv, into_acc_inv
-/

namespace Iris

open Iris OFE COFE BI FUpd

section InvariantDefinition

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

def inv (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(□ ∀ E, ⌜↑N ⊆ E⌝ → |={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True))

def own_inv (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(∃ i, ⌜i ∈ (↑N : CoPset)⌝ ∧ ownI i P)

end InvariantDefinition

section Instances

open ProofMode

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

@[rocq_alias inv_contractive]
instance inv_contractive (N : Namespace) : Contractive (inv (GF := GF) N) where
  distLater_dist {n x y} H := by
    simp only [inv]
    refine intuitionistically_ne.ne ?_
    refine forall_ne (fun i => ?_)
    refine imp_ne.ne .rfl ?_
    refine wand_ne.ne .rfl ?_
    refine le_upd_if_ne.ne ?_
    refine except0_ne.ne ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne ?_ ?_
    · exact Contractive.distLater_dist H
    · refine wand_ne.ne ?_ .rfl
      exact Contractive.distLater_dist H

@[rocq_alias inv_ne]
instance inv_ne (N : Namespace) : NonExpansive (inv (GF := GF) N) := ne_of_contractive _

@[rocq_alias inv_persistent]
instance inv_persistent (N : Namespace) (P : IProp GF) : Persistent (inv N P) := by
  simp only [inv]
  infer_instance

instance own_inv_persistent (N : Namespace) (P : IProp GF) : Persistent (own_inv N P) := by
  simp only [own_inv]
  infer_instance

@[rocq_alias except_0_inv]
theorem except_0_inv (N : Namespace) (P : IProp GF) :
  ⊢ ◇ inv N P -∗ inv N P := by
  simp only [inv]
  iintro #H
  imodintro
  iintro %E %Hsub
  imod H
  iapply H
  ipure_intro; assumption

@[rocq_alias is_except_0_inv]
instance is_except_0_inv (N : Namespace) (P : IProp GF) : IsExcept0 (inv N P) where
  is_except0 := by iintro H; iapply except_0_inv $$ H

end Instances

section BasicLemmas

open Iris Std LawfulSet

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

@[rocq_alias own_inv_acc]
theorem own_inv_acc (E : CoPset) (N : Namespace) (P : IProp GF) (Hsub : ↑N ⊆ E) :
  ⊢ own_inv N P ={E, E \ ↑N}=∗ ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  simp only [own_inv, fupd, uPred_fupd]
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
  icases ownE_op (GF := GF) disjoint_diff_right $$ HE with ⟨HE1, HE2⟩
  ihave HE1 : ownE ({i} ∪ (nclose N \ {i})) $$ [HE1]
  · rw [HNEQ]; iexact HE1
  icases ownE_op (GF := GF) disjoint_diff_right $$ HE1 with ⟨HE1, HE3⟩
  imodintro; imodintro
  icases ownI_open (P := P) (GF := GF) $$ [Hwsat HE1 Hown] with ⟨Hwsat, HP, HD⟩
  · isplitl [Hwsat]; iassumption
    isplitl [Hown]; iassumption
    iassumption
  isplitl [Hwsat]; iassumption
  isplitl [HE2]; iassumption
  isplitl [HP]; iassumption
  iintro HP ⟨Hwsat, HE⟩
  imodintro; imodintro
  icases ownI_close (GF := GF) $$ [HP Hwsat HD Hown] with ⟨Hwsat, HE1⟩
  · isplitl [Hwsat]; iassumption
    isplitl [Hown]; iassumption
    isplitl [HP]; iassumption
    iassumption
  isplitl [Hwsat]; iassumption
  icases ownE_op (GF := GF) disjoint_diff_right $$ [HE3 HE1] with HE1
  · isplitl [HE1]; iassumption
    iassumption
  rw [HNEQ]
  icases ownE_op (GF := GF) disjoint_diff_right $$ [HE1 HE] with HE
  · isplitl [HE1]; iassumption
    iassumption
  rw [HEEQ]
  isplitl [HE]; iassumption
  apply true_intro

@[rocq_alias own_inv_alloc]
theorem own_inv_alloc (N : Namespace) (E : CoPset) (P : IProp GF) :
  ⊢ ▷ P ={E}=∗ own_inv N P := by
  simp only [own_inv, fupd, uPred_fupd]
  iintro HP ⟨Hw, HE⟩
  imod ownI_alloc (.∈ (↑N : CoPset)) P $$ [HP Hw] with ⟨%i, %Hin, Hw, HI⟩
  · intro E; apply fresh_name
  · isplitl [Hw] <;> iassumption
  · imodintro; imodintro
    isplitl [Hw]; iassumption
    isplitl [HE]; iassumption
    iexists i
    isplit
    · ipure_intro; assumption
    · iassumption

@[rocq_alias own_inv_alloc_open]
theorem own_inv_alloc_open (N : Namespace) (E : CoPset) (P : IProp GF) (Hsub : ↑N ⊆ E) :
  ⊢ |={E, E \ ↑N}=> own_inv N P ∗ (▷P ={E \ ↑N, E}=∗ True) := by
  simp only [own_inv, fupd, uPred_fupd]
  iintro ⟨Hw, HE⟩
  imod ownI_alloc_open (φ := fun x => x ∈ (↑N : CoPset)) (P := P) (GF := GF) $$ Hw with ⟨%i, %Hin, Hcont, #HI, HD⟩
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
  icases ownE_op (GF := GF) disjoint_diff_right $$ HE with ⟨HE1, HEN⟩
  ihave HE1 : ownE ({i} ∪ (nclose N \ {i})) $$ [HE1]
  · rw [HNEQ]; iexact HE1
  icases ownE_op (GF := GF) disjoint_diff_right $$ HE1 with ⟨HEi, HENi⟩
  imodintro; imodintro
  ispecialize Hcont $$ HEi
  isplitl [Hcont]; iassumption
  isplitl [HEN]; iassumption
  isplitl [HI]
  · iexists i; isplit
    · ipure_intro; assumption
    · iexact HI
  iintro HP ⟨Hw, HE⟩
  icases ownI_close (GF := GF) $$ [HP Hw HD] with ⟨Hwsat, HE1⟩
  · isplitl [Hw]; iassumption
    isplitl [HI]; iassumption
    isplitl [HP]; iassumption
    iassumption
  imodintro; imodintro
  isplitl [Hwsat]; iassumption
  icases ownE_op (GF := GF) disjoint_diff_right $$ [HENi HE1] with HE1
  · isplitl [HE1]; iassumption
    iassumption
  rw [HNEQ]
  icases ownE_op (GF := GF) disjoint_diff_right $$ [HE1 HE] with HE
  · isplitl [HE1]; iassumption
    iassumption
  rw [HEEQ]
  isplitl [HE]; iassumption
  apply true_intro

@[rocq_alias own_inv_to_inv]
theorem own_inv_to_inv (M : Namespace) (P : IProp GF) :
  ⊢ own_inv M P -∗ inv M P := by
  simp only [inv]
  iintro #I
  imodintro
  iintro %E %Hsub
  iapply own_inv_acc _ _ _ Hsub (GF := GF) $$ I

end BasicLemmas

section Allocation

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

@[rocq_alias inv_alloc]
theorem inv_alloc (N : Namespace) (E : CoPset) (P : IProp GF) :
  ⊢ ▷ P ={E}=∗ inv N P := by
  iintro HP
  imod own_inv_alloc N (GF := GF) $$ HP with H
  imodintro
  iapply own_inv_to_inv $$ H

@[rocq_alias inv_alloc_open]
theorem inv_alloc_open (N : Namespace) (E : CoPset) (P : IProp GF) (Hsub : ↑N ⊆ E) :
  ⊢ |={E, E \ ↑N}=> inv N P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  imod own_inv_alloc_open _ _ P Hsub (GF := GF) with ⟨Hown, Hcl⟩
  imodintro
  isplitr [Hcl]
  · iapply own_inv_to_inv $$ Hown
  · iexact Hcl

end Allocation

section Access

open Iris Std LawfulSet

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

@[rocq_alias inv_acc]
theorem inv_acc (E : CoPset) (N : Namespace) (P : IProp GF) (Hsub : ↑N ⊆ E) :
  ⊢ inv N P ={E, E \ ↑N}=∗ ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  simp only [inv]
  iintro #HI
  iapply HI $$ %E []
  ipure_intro; assumption

@[rocq_alias inv_acc_strong]
theorem inv_acc_strong (E : CoPset) (N : Namespace) (P : IProp GF) (Hsub : ↑N ⊆ E) :
  ⊢ inv N P ={E, E \ ↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E', ↑N ∪ E'}=∗ True := by
  iintro Hinv
  icases inv_acc ↑N N _ subset_refl (GF := GF) $$ Hinv with H
  rw [diff_all]
  icases fupd_mask_frame_r disjoint_diff_right (Ef := (E \ ↑N)) (PROP := IProp GF) $$ H with H
  rw [union_empty_left, ←union_comm (s₁ := E \ nclose N), ←diff_subset_decomp Hsub]
  imod H with ⟨HP, H⟩
  imodintro
  isplitl [HP]; iassumption
  iintro %E' HP
  ispecialize H $$ HP
  icases fupd_mask_frame_r disjoint_empty_left (Ef := E') (PROP := IProp GF) $$ H with H
  rw [union_empty_left]
  imod H; imodintro
  iexact H

@[rocq_alias inv_acc_timeless]
theorem inv_acc_timeless (E : CoPset) (N : Namespace) (P : IProp GF) [Timeless P] (Hsub : ↑N ⊆ E) :
  ⊢ inv N P ={E, E \ ↑N}=∗ P ∗ (P ={E \ ↑N, E}=∗ True) := by
  iintro HI
  imod inv_acc _ _ _ Hsub (GF := GF) $$ HI with ⟨>HP, H⟩
  imodintro
  isplitl [HP]; iassumption
  iintro HP
  iapply H
  inext; iassumption

end Access

section Modification

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

@[rocq_alias inv_alter]
theorem inv_alter (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N P -∗ ▷ □ (P -∗ Q ∗ (Q -∗ P)) -∗ inv N Q := by
  simp only [inv]
  iintro #HI #HPQ
  imodintro
  iintro %E Hsub
  imod HI $$ %E Hsub with ⟨HP, H⟩
  imodintro
  icases HPQ $$ HP with ⟨HQ, HQP⟩
  isplitl [HQ]
  · iexact HQ
  · iintro HQ
    iapply H
    iapply HQP $$ HQ

@[rocq_alias inv_iff]
theorem inv_iff (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N P -∗ ▷ □ (P ↔ Q) -∗ inv N Q := by
  iintro #HI #HPQ
  iapply inv_alter $$ HI
  inext; imodintro; iintro HP
  isplitl [HP]
  · simp only [iff]
    iapply HPQ $$ HP
  · iintro HQ
    simp only [iff]
    iapply HPQ $$ HQ

end Modification

section Combination

open Iris Std LawfulSet

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

@[rocq_alias inv_combine]
theorem inv_combine (N1 N2 N : Namespace) (P Q : IProp GF) (Hdisj : N1 ## N2) (Hsub : ↑N1 ∪ ↑N2 ⊆ (↑N : CoPset)) :
  ⊢ inv N1 P -∗ inv N2 Q -∗ inv N iprop(P ∗ Q) := by
  simp only [inv]
  iintro #HI1 #HI2
  imodintro
  iintro %E %Hsub'
  imod HI1 $$ %E [] with ⟨HP, H1⟩
  · ipure_intro
    exact subset_trans (subset_trans union_subset_left Hsub) Hsub'
  imod HI2 $$ %(E \ ↑N1) [] with ⟨HQ, H2⟩
  · ipure_intro
    intro x; simp only [mem_diff]
    specialize Hsub x; simp only [mem_union] at Hsub
    specialize Hsub' x
    specialize Hdisj x
    grind
  iapply fupd_mask_intro
  · intro x; simp only [mem_diff, mem_diff]
    specialize Hsub x; simp only [mem_union] at Hsub
    specialize Hsub' x
    specialize Hdisj x
    grind
  iintro Hcl
  isplitl [HP HQ]; inext; isplitl [HP] <;> iassumption
  iintro ⟨HP, HQ⟩
  imod Hcl
  imod H2 $$ HQ with _
  imod H1 $$ HP with _
  imodintro
  iassumption

@[rocq_alias inv_combine_dup_l]
theorem inv_combine_dup_l (N : Namespace) (P Q : IProp GF) :
  ⊢ □ (P -∗ (P ∗ P)) -∗ inv N P -∗ inv N Q -∗ inv N iprop(P ∗ Q) := by
  simp only [inv]
  iintro #HPP #HI1 #HI2
  imodintro; iintro %E #Hsub
  imod HI1 $$ %E Hsub with ⟨HP, HI1⟩
  ihave ⟨HP1, HP2⟩ : ▷ P ∗ ▷ P $$ [HP]
  · iapply later_sep; inext; iapply HPP $$ HP
  imod HI1 $$ HP2 with _
  imod HI2 $$ %E Hsub with ⟨HQ, HI2⟩
  imodintro
  isplitl [HP1 HQ]
  · inext; isplitl [HP1] <;> iassumption
  iintro ⟨_, HQ⟩
  imod HI2 $$ HQ with _
  imodintro; iassumption

end Combination

section Splitting

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

@[rocq_alias inv_split_l]
theorem inv_split_l (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N iprop(P ∗ Q) -∗ inv N P := by
  iintro H
  iapply inv_alter $$ H
  inext; imodintro
  iintro ⟨HP, HQ⟩
  isplitl [HP]; iassumption
  iintro HP
  isplitl [HP] <;> iassumption

@[rocq_alias inv_split_r]
theorem inv_split_r (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N iprop(P ∗ Q) -∗ inv N Q := by
  iintro H
  iapply inv_alter $$ H
  inext; imodintro
  iintro ⟨HP, HQ⟩
  isplitl [HQ]; iassumption
  iintro HQ
  isplitl [HP] <;> iassumption

@[rocq_alias inv_split]
theorem inv_split (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N iprop(P ∗ Q) -∗ inv N P ∗ inv N Q := by
  iintro #H
  ihave H1 := inv_split_l (GF := GF) $$ H
  ihave H2 := inv_split_r (GF := GF) $$ H
  isplit <;> iassumption

end Splitting

end Iris

end
