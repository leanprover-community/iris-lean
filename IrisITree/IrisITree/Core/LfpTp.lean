/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import Iris.BI.BigOp.BigSepMSet
public import Iris.BI.Lib.Fixpoint
public import Iris.Std.GenMultiSetsInstances
public import IrisITree.Core.BIMono

public section

local stepindex Nat

namespace IrisITree

open Iris BI Std OFE

noncomputable scoped instance threadPoolMultiset {α PROP : Type _} :
    LawfulFiniteMultiSet (ListPerm ((α → PROP) → PROP)) ((α → PROP) → PROP) := by
  classical
  exact ListPerm.instLawfulFiniteMultiSet

/-- One-step rule for a whole thread pool. -/
@[expose]
noncomputable def lfp_tpF {PROP : Type _} [BI PROP] {α : Type _}
    (F : (α → PROP) → (α → PROP))
    (rec_tp : ListPerm ((α → PROP) → PROP) → PROP) :
    ListPerm ((α → PROP) → PROP) → PROP :=
  fun Ms => iprop%
    ∀ M Mrest, <affine> ⌜Ms = {M} ⊎ Mrest⌝ -∗
      bi_mono0 M fun x => iprop%
        ∃ G, F G x ∗ ∀ Ms', ([∗mset] M' ∈ Ms', M' G) -∗ rec_tp (Ms' ⊎ Mrest)

section lfp_tpF

variable {PROP : Type _} [BI PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))
local bi PROP

instance lfp_tpF_ne : NonExpansive (lfp_tpF F) where
  ne {_ _ _} Hfg := by
    intro Ms; unfold lfp_tpF
    refine forall_ne fun _ => forall_ne fun _ => ?_
    refine wand_ne.ne .rfl ?_
    refine bi_mono0_ne .rfl fun x => ?_
    refine exists_ne fun _ => ?_
    refine sep_ne.ne .rfl <| forall_ne fun _ => ?_
    exact wand_ne.ne .rfl <| Hfg _

theorem lfp_tpF_mono (tp1 tp2 : ListPerm ((α → PROP) → PROP) → PROP) :
    □ (∀ Ms, tp1 Ms -∗ tp2 Ms) -∗
    ∀ Ms, lfp_tpF F tp1 Ms -∗ lfp_tpF F tp2 Ms := by
  iintro #Hwand %Ms Htp; unfold lfp_tpF
  iintro %M %Mrest %Heq; ispecialize Htp $$ %M %Mrest %Heq
  iapply bi_mono0_mono $$ Htp
  iintro %x ⟨%G, HF, HMS⟩
  iframe HF
  iintro %Ms HM'
  iapply Hwand
  iapply HMS $$ HM'

theorem lfp_tpF_mono' tp (F G : (α → PROP) → α → PROP) :
    □ (∀ Φ x, F Φ x -∗ G Φ x) -∗
    ∀ Ms, lfp_tpF F tp Ms -∗ lfp_tpF G tp Ms := by
  iintro #Hwand %Ms Htp; unfold lfp_tpF
  iintro %M %Mrest %Heq
  ispecialize Htp $$ %M %Mrest %Heq
  iapply bi_mono0_mono $$ Htp
  iintro %x ⟨%Φ, HF, $⟩
  iapply Hwand $$ HF

/-- Only this abbreviation is built on top of `Discrete0`. -/
private noncomputable abbrev lfp_tpF_discrete (F : (α → PROP) → (α → PROP))
    (rec_tp : DiscreteO (ListPerm ((α → PROP) → PROP)) → PROP) :
    DiscreteO (ListPerm ((α → PROP) → PROP)) → PROP :=
  fun Ms => lfp_tpF F (fun l => rec_tp ⟨l⟩) Ms.car

private instance : BIMonoPred (lfp_tpF_discrete F) where
  mono_pred := by
    iintro %Φ %Ψ %HneΦ %HneΨ #Hwand %Ms HΦ
    iapply lfp_tpF_mono F _ _ $$ [] HΦ
    iintro !> %Ms; iapply Hwand
  mono_pred_ne := ne_of_discrete _

end lfp_tpF

/-- Every thread in the pool `Ms` can keep stepping safely according to `F`, however the threads are scheduled. -/
noncomputable def lfp_tp {PROP : Type _} [BI PROP] {α : Type _} (F : (α → PROP) → (α → PROP))
    (Ms : ListPerm ((α → PROP) → PROP)) : PROP :=
  bi_least_fixpoint (lfp_tpF_discrete F) ⟨Ms⟩

section lfp_tp_lemmas

variable {PROP : Type _} [BI PROP] {α : Type _} (F : (α → PROP) → (α → PROP))

theorem lfp_tp_unfold (Ms : ListPerm ((α → PROP) → PROP)) :
    lfp_tp F Ms ⊣⊢ lfp_tpF F (fun Ms => lfp_tp F Ms) Ms :=
  equiv_iff.mp <| least_fixpoint_unfold (lfp_tpF_discrete F)

theorem lfp_tp_empty : ⊢ lfp_tp F ∅ := by
  iapply (lfp_tp_unfold F ∅).mpr
  unfold lfp_tpF
  iintro %M %Mrest %Heq
  exfalso
  exact (not_mem_empty (a := M) (by rw [Heq]; grind))

/-- Induction theorem on `lfp_tp`. -/
theorem lfp_tp_ind (Φ : ListPerm ((α → PROP) → PROP) → PROP) :
    □ (∀ Ms, lfp_tpF F (fun Ms => iprop(Φ Ms ∧ lfp_tp F Ms)) Ms -∗ Φ Ms) -∗
    ∀ Ms, lfp_tp F Ms -∗ Φ Ms := by
  unfold lfp_tp
  iintro #Hwand %Ms Hlfp
  iapply least_fixpoint_ind (lfp_tpF_discrete F) (fun Ms => Φ Ms.car) $$ [] %⟨Ms⟩ Hlfp
  iintro !> %Ms Hpre
  iapply Hwand $$ Hpre

theorem lfp_tp_disjUnion (Ms1 Ms2 : ListPerm ((α → PROP) → PROP)) :
    lfp_tp F Ms1 -∗ lfp_tp F Ms2 -∗ lfp_tp F (Ms1 ⊎ Ms2) := by
  iintro Hx1 Hx2
  irevert %Ms2 Hx2; irevert Hx1; irevert %Ms1
  iapply lfp_tp_ind F
  iintro !> %Ms1 Hx1 %Ms2 Hx2
  irevert %Ms1 Hx1; irevert Hx2; irevert %Ms2
  iapply lfp_tp_ind F
  iintro !> %Ms2 Hx2 %Ms1 Hx1
  iapply lfp_tp_unfold
  iunfold lfp_tpF
  iintro %M %Mrest %Heq
  cases mem_disjUnion_iff (x := M) (X := Ms1) (Y := Ms2).mp (by grind) with
  | inl hx =>
    obtain rfl : Mrest = (Ms1 \ {M}) ⊎ Ms2 := by grind [disjUnion_singleton_difference]
    iunfold lfp_tpF at Hx1
    ispecialize Hx1 $$ %M %(Ms1 \ {M}) %(by grind)
    iapply bi_mono0_mono $$ Hx1
    iintro %x ⟨%G, HF, Hcont⟩
    iframe HF
    iintro %new Hnew
    icases Hcont $$ %new Hnew with ⟨Hunion, -⟩
    rw [← disjUnion_assoc]
    iapply Hunion
    iapply lfp_tp_unfold
    iapply lfp_tpF_mono F _ _ $$ [] %Ms2 Hx2
    iintro !> %Ms ⟨-, $⟩
  | inr hy =>
    obtain rfl : Mrest = (Ms2 \ {M}) ⊎ Ms1 := by grind [disjUnion_singleton_difference]
    iunfold lfp_tpF at Hx2
    ispecialize Hx2 $$ %M %(Ms2 \ {M}) %(by grind)
    iapply bi_mono0_mono $$ Hx2
    iintro %x ⟨%G, HF, Hcont⟩
    iframe HF
    iintro %new Hnew
    icases Hcont $$ %new Hnew with ⟨Hunion, -⟩
    rw [← disjUnion_assoc, disjUnion_comm (Y := Ms1)]
    iunfold lfp_tpF at Hx1
    iapply Hunion $$ %Ms1 Hx1

theorem lfp_tp_singleton (M : (α → PROP) → PROP) :
    M (fun x => lfp_tp F {fun P => P x}) -∗ lfp_tp F {M} := by
  iintro Hx; iapply lfp_tp_unfold; simp only [lfp_tpF]
  iintro %M' %Mrest %Heq
  obtain ⟨rfl, rfl⟩ : M' = M ∧ Mrest = ∅ := by
    grind [disjUnion_subset_left, singleton_subset_iff,
      disjUnion_empty_right (X := ({M} : ListPerm _))]
  iapply bi_mono0_intro $$ Hx
  iintro %x Hlfp
  rw [(lfp_tp_unfold F {fun P => P x}).to_eq, lfp_tpF]
  ispecialize Hlfp $$ %_ %∅ %disjUnion_empty_right.symm
  iapply bi_mono0_elim $$ Hlfp
  iintro %Q %Q' Hwand HQ'
  iapply Hwand $$ HQ'

variable {α : Type _} [OFE α] [OFE.Discrete α]

theorem lfp_tp_intro (G : (α → PROP) → (α → PROP)) (x : α) :
    bi_least_fixpoint G x -∗ lfp_tp G {fun P => P x} := by
  letI := ne_of_discrete fun (x : α) => lfp_tp G {fun P => P x}
  iintro Hlfp
  irevert %x Hlfp
  iapply least_fixpoint_iter
  iintro !> %x HF; iapply lfp_tp_unfold
  rw [lfp_tpF]
  iintro %M %Mrest %Heq
  obtain ⟨rfl, rfl⟩ : M = (fun P => P x) ∧ Mrest = ∅ := by
    grind [disjUnion_subset_left, singleton_subset_iff,
      disjUnion_empty_right (X := ({fun (P : α → PROP) => P x} : ListPerm _))]
  iapply bi_mono0_intro0
  iexists (fun x => _)
  iframe HF
  iintro %Ms
  rw [disjUnion_empty_right]
  -- FIXME(#758): iinduction does not work
  induction Ms using multiset_ind with
  | empty => iintro _; iapply lfp_tp_empty
  | disjUnion_singleton M Ms IHM =>
    iintro HMs
    icases BigSepMS.bigSepMS_insert $$ HMs with ⟨HM, HMs⟩
    iapply lfp_tp_disjUnion G $$ [HM]
    · iapply lfp_tp_singleton G M $$ HM
    irevert HMs
    exact IHM

end lfp_tp_lemmas

end IrisITree
