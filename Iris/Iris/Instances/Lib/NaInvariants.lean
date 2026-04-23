/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.ProofMode
public import Iris.Instances.IProp.Instance
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.Invariants
public import Iris.Algebra.LeibnizSet
public import Iris.Std.Namespaces
public import Iris.Std.CoPset

@[expose] public section

namespace Iris

open BI CMRA OFE Iris Std LawfulSet DisjointLeibnizSet COFE

abbrev NaInvF : OFunctorPre :=
  ProdOF (constOF (DisjointLeibnizSet CoPset)) (constOF (DisjointLeibnizSet PosSet))

@[rocq_alias na_invG]
class NaInvG (GF : BundledGFunctors) where
  inv : ElemG GF NaInvF

attribute [reducible, instance] NaInvG.inv

@[rocq_alias na_inv_pool_name]
abbrev NaInvPoolName := GName

instance instNaInvF_discreteE {α β : Type _} (x : DisjointLeibnizSet α) (y : DisjointLeibnizSet β) :
    DiscreteE (x, y) :=
  prod.is_discrete (inst_disjointLeibnizSet_DiscreteE _) (inst_disjointLeibnizSet_DiscreteE _)

instance coreId_valid_empty_empty : CoreId ((valid (∅ : CoPset), valid (∅ : PosSet))) where
  core_id := by rfl

instance isUnit_valid_empty_empty : IsUnit ((valid (∅ : CoPset), valid (∅ : PosSet))) where
  unit_valid := ⟨trivial, trivial⟩
  unit_left_id := ⟨unit_left_id, unit_left_id⟩
  pcore_unit := coreId_valid_empty_empty.core_id

namespace NonAtomicInvariant

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [W : NaInvG GF]

@[rocq_alias na_own]
def own (p : NaInvPoolName) (E : CoPset) : IProp GF :=
  iOwn (E := W.inv) p (.valid E, .valid ∅)

@[rocq_alias na_inv]
nonrec def inv (p : NaInvPoolName) (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(∃ i, ⌜i ∈ (↑N : CoPset)⌝ ∧
    inv N iprop(P ∗ iOwn (E := W.inv) p (.valid ∅, .valid {i}) ∨ own p {i}))

@[rocq_alias na_own_timeless]
instance instTimeless_own (p : NaInvPoolName) (E : CoPset) : Timeless (own (GF := GF) p E) := by
  unfold own; infer_instance

@[rocq_alias na_inv_contractive]
instance instContractive_inv (p : NaInvPoolName) (N : Namespace) :
    Contractive (inv (GF := GF) p N) where
  distLater_dist {n x y} H := by
    refine exists_ne fun i => and_ne.ne .rfl ?_
    refine Contractive.distLater_dist fun m hm => ?_
    exact or_ne.ne (sep_ne.ne (H _ hm) .rfl) .rfl

@[rocq_alias na_inv_ne]
instance instNonExpansive_inv (p : NaInvPoolName) (N : Namespace) : NonExpansive (inv (GF := GF) p N) :=
  ne_of_contractive _

@[rocq_alias na_inv_persistent]
instance instPersistentInv (p : NaInvPoolName) (N : Namespace) (P : IProp GF) :
    Persistent (inv p N P) := by
  unfold inv; infer_instance

@[rocq_alias na_own_empty_persistent]
instance instPersistent_own (p : NaInvPoolName) : Persistent (own (GF := GF) p ∅) := by
  unfold own; infer_instance

@[rocq_alias na_inv_iff]
nonrec theorem inv_iff {p : NaInvPoolName} {N : Namespace} {P Q : IProp GF} :
    ⊢ inv p N P -∗ ▷ □ (P ↔ Q) -∗ inv p N Q := by
  unfold inv
  iintro ⟨%i, %Hin, HI⟩ #HPQ
  iexists i
  isplit; (· ipure_intro; assumption)
  iapply inv_iff $$ HI
  inext; imodintro
  unfold BI.iff
  isplit
  · iintro (⟨HP, Ho⟩ | Htok)
    · ileft
      isplitr [Ho]
      · icases HPQ with ⟨HPQm, _⟩
        iapply HPQm $$ HP
      · iassumption
    · iright; iassumption
  · iintro (⟨HQ, Ho⟩ | Htok)
    · ileft
      isplitr [Ho]
      · icases HPQ with ⟨_, HQPm⟩
        iapply HQPm $$ HQ
      · iassumption
    · iright; iassumption

@[rocq_alias na_alloc]
theorem alloc : ⊢@{IProp GF} |==> ∃ p : NaInvPoolName, own p ⊤ :=
  iOwn_alloc (E := W.inv) (.valid (⊤ : CoPset), .valid (∅ : PosSet)) ⟨trivial, trivial⟩

@[rocq_alias na_own_disjoint]
theorem own_disjoint {p : NaInvPoolName} {E1 E2 : CoPset} :
    ⊢ own (GF := GF) p E1 -∗ own p E2 -∗ ⌜E1 ## E2⌝ := by
  unfold own
  iintro H1 H2
  ihave H := iOwn_op $$ [H1 H2]
  · isplitl [H1] <;> iassumption
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete $$ H with %H
  ipure_intro
  exact valid_op_iff_disj.mp H.1

@[rocq_alias na_own_union]
theorem own_union {p : NaInvPoolName} {E1 E2 : CoPset} (Hdisj : E1 ## E2) :
    own (GF := GF) p (E1 ∪ E2) ⊣⊢ own p E1 ∗ own p E2 := by
  refine .trans ?_ iOwn_op
  refine BI.equiv_iff.mp (NonExpansive.eqv (f := iOwn (E := W.inv) p) ?_)
  refine .symm <| equiv_prod_ext (disj_op_union Hdisj) ?_
  refine .trans (disj_op_union disjoint_empty_left) ?_
  exact .of_eq (by simp)

@[rocq_alias na_own_acc]
theorem own_acc {E2 E1 : CoPset} {tid : NaInvPoolName} (Hsub : E2 ⊆ E1) :
    ⊢ own (GF := GF) tid E1 -∗ own tid E2 ∗ (own tid E2 -∗ own tid E1) := by
  rw [← subset_union_diff Hsub]
  iintro H
  icases (own_union disjoint_diff_right).mp $$ H with ⟨H1, H2⟩
  isplitl [H1]; iassumption
  iintro H1
  iapply (own_union disjoint_diff_right).mpr
  isplitl [H1] <;> iassumption

@[rocq_alias na_own_empty]
theorem own_empty (p : NaInvPoolName) : ⊢@{IProp GF} |==> own p ∅ := iOwn_unit (E := W.inv)

@[rocq_alias na_inv_alloc]
nonrec theorem inv_alloc {p : NaInvPoolName} {E : CoPset} {N : Namespace} {P : IProp GF} :
    ⊢ ▷ P ={E}=∗ inv p N P := by
  iintro HP
  imod (iOwn_unit (E := W.inv) (γ := p) (ε := (.valid ∅, .valid ∅))) with Hempty
  have Hupd : (.valid (∅ : CoPset), .valid (∅ : PosSet)) ~~>:
      fun y : NaInvF.ap (IProp GF) => ∃ i, y = (.valid ∅, .valid {i}) ∧ i ∈ (↑N : CoPset) :=
    .prod (P := (· = .valid ∅)) (.id rfl) (alloc_empty_updateP_strong' (fresh_name · N))
      (fun a b ha ⟨i, hb, hi⟩ => ⟨i, Prod.ext ha hb, hi⟩)
  imod iOwn_updateP Hupd $$ Hempty with ⟨%y, %Hy, Hown⟩
  obtain ⟨i, rfl, Hi⟩ := Hy
  unfold inv
  imod inv_alloc N E iprop( P ∗ iOwn (E := W.inv) p (.valid ∅, .valid {i}) ∨ own p {i}) $$ [HP Hown]
    with HI
  · inext; ileft; isplitl [HP] <;> iassumption
  imodintro
  iexists i
  isplit
  · ipure_intro; assumption
  · iassumption

@[rocq_alias na_inv_acc]
nonrec theorem inv_acc {p : NaInvPoolName} {E F : CoPset} {N : Namespace} {P : IProp GF}
    (HNE : ↑N ⊆ E) (HNF : ↑N ⊆ F) :
    ⊢ inv p N P -∗ own p F ={E}=∗ ▷ P ∗ own p (F \ ↑N) ∗ (▷ P ∗ own p (F \ ↑N) ={E}=∗ own p F) := by
  unfold inv
  iintro #⟨%i, %Hin, Hinv⟩ Htoks
  have HNminusi : ↑N = {i} ∪ ((↑N : CoPset) \ {i}) := by
    refine (subset_union_diff ?_).symm
    intro x hx; rw [mem_singleton] at hx; exact hx ▸ Hin
  icases (own_union disjoint_diff_right).mp $$ [Htoks] with ⟨HtokN, HtokRest⟩
  · rw [subset_union_diff HNF]
    iassumption
  icases (own_union disjoint_diff_right).mp $$ [HtokN] with ⟨Htoki, HtokNdi⟩
  · rw [← HNminusi]; iassumption
  imod inv_acc _ _ _ HNE $$ Hinv with ⟨Hcontent, Hclose⟩
  icases Hcontent with (⟨HP, >Hdis⟩ | >Htoki2)
  · ihave Hreturn : ▷ (P ∗ iOwn (E := W.inv) p (.valid ∅, .valid {i}) ∨ own p {i}) $$ [Htoki]
    · inext; iright; iassumption
    imod Hclose $$ Hreturn with _
    imodintro
    isplitl [HP]; iassumption
    isplitl [HtokRest]; iassumption
    iintro ⟨HPret, HtokFret⟩
    imod inv_acc _ _ _ HNE $$ Hinv with ⟨Hcontent2, Hclose2⟩
    icases Hcontent2 with (⟨_HPconflict, >Hdis2⟩ | >Htoki_back)
    · iexfalso
      ihave Hk := iOwn_op (E := W.inv) $$ [Hdis Hdis2]
      · isplitl [Hdis] <;> iassumption
      ihave Hk := iOwn_cmraValid $$ Hk
      icases internalCmraValid_discrete $$ Hk with %Hbad
      have Hk := DisjointLeibnizSet.valid_op_iff_disj.mp Hbad.2
      exact Hk i ⟨mem_singleton.mpr rfl, mem_singleton.mpr rfl⟩ |>.elim
    · ihave Hreturn2 : ▷ (P ∗ iOwn (E := W.inv) p (.valid ∅, .valid {i}) ∨ own p {i}) $$ [HPret Hdis]
      · inext; ileft; isplitl [HPret] <;> iassumption
      imod Hclose2 $$ Hreturn2 with _
      imodintro
      ihave HtokN_new : own p ((↑N : CoPset)) $$ [Htoki_back HtokNdi]
      · conv => rhs; rw [HNminusi]
        iapply (own_union disjoint_diff_right).mpr
        isplitl [Htoki_back]
        · iexact Htoki_back
        · iexact HtokNdi
      conv => rhs; rw [← subset_union_diff HNF]
      iapply (own_union disjoint_diff_right).mpr
      isplitl [HtokN_new]
      · iexact HtokN_new
      · iexact HtokFret
  · iexfalso
    ihave Hbad : ⌜({i} : CoPset) ## {i}⌝ $$ [Htoki Htoki2]
    · iapply own_disjoint $$ Htoki Htoki2
    icases Hbad with %Hbad
    exact Hbad i ⟨mem_singleton.mpr rfl, mem_singleton.mpr rfl⟩ |>.elim

end NonAtomicInvariant
end Iris
end
