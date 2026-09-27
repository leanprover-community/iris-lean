/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.ProofMode
public import Iris.Instances.IProp.Instance
public import Iris.Instances.Lib.FUpdTransfinite
public import Iris.Instances.Lib.InvariantsTransfinite
public import Iris.Algebra.LeibnizSet
public import Iris.Std.Namespaces
public import Iris.Std.CoPset

/-! # Non-atomic invariants over arbitrary step-indices (Transfinite Iris)

This file ports `theories/base_logic/lib/na_invariants.v` for the credit-free fancy update of
`Iris.Instances.Lib.FUpdTransfinite`; the proofs follow `Iris.Instances.Lib.NaInvariants`. The
ghost state is lifted to the universe of the resources (`constOFU`).
-/

@[expose] public noncomputable section

universe u v

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

set_option linter.unusedSectionVars false

namespace Iris.Transfinite

open BI CMRA OFE Iris Iris.Std LawfulSet DisjointLeibnizSet COFE ProofMode

abbrev NaInvR := CoPsetDisjL × DisjointLeibnizSet PosSet

class NaInvG (GF : BundledGFunctors.{u}) where
  inv : ElemG GF (constOFU.{max u v} NaInvR)


attribute [reducible, instance] NaInvG.inv

abbrev NaInvPoolName := GName

instance coreId_valid_empty_empty' :
    CoreId (((valid (∅ : CoPset), valid (∅ : PosSet))) : NaInvR) where
  core_id := by rfl

instance isUnit_up_valid_empty_empty :
    IsUnit (ULift.up.{w} ((valid (∅ : CoPset), valid (∅ : PosSet)) : NaInvR)) where
  unit_valid := ⟨trivial, trivial⟩
  unit_left_id := congrArg ULift.up (Prod.ext CMRA.ucmra_unit_left_id CMRA.ucmra_unit_left_id)
  pcore_unit := (ULift.instCoreId (a := ((valid (∅ : CoPset), valid (∅ : PosSet)) : NaInvR))).core_id

namespace NonAtomicInvariant

variable {GF : BundledGFunctors} [WsatGS GF] [W : NaInvG GF]

def own (p : NaInvPoolName) (E : CoPset) : IProp GF :=
  iOwn (E := W.inv) p (ULift.up (.valid E, .valid ∅))

nonrec def inv (p : NaInvPoolName) (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(∃ i, ⌜i ∈ (↑N : CoPset)⌝ ∧
    inv N iprop(P ∗ iOwn (E := W.inv) p (ULift.up (.valid ∅, .valid {i})) ∨ own p {i}))

instance instTimeless_own (p : NaInvPoolName) (E : CoPset) : Timeless (own (GF := GF) p E) := by
  unfold own; infer_instance

instance instContractive_inv (p : NaInvPoolName) (N : Namespace) :
    Contractive (inv (GF := GF) p N) where
  distLater_dist {n x y} H := by
    refine exists_ne fun i => and_ne.ne .rfl ?_
    refine Contractive.distLater_dist fun m hm => ?_
    exact or_ne.ne (sep_ne.ne (H _ hm) .rfl) .rfl

instance instNonExpansive_inv (p : NaInvPoolName) (N : Namespace) : NonExpansive (inv (GF := GF) p N) :=
  ne_of_contractive _


instance instPersistentInv (p : NaInvPoolName) (N : Namespace) (P : IProp GF) :
    Persistent (inv p N P) := by
  unfold inv; infer_instance

instance instPersistent_own (p : NaInvPoolName) : Persistent (own (GF := GF) p ∅) := by
  unfold own
  haveI : CMRA.CoreId (α := (constOFU.{max u v} NaInvR).ap (IProp GF))
      (ULift.up ((valid (∅ : CoPset), valid (∅ : PosSet)) : NaInvR)) := ULift.instCoreId
  infer_instance

nonrec theorem inv_iff {p : NaInvPoolName} {N : Namespace} {P Q : IProp GF} :
    ⊢ inv p N P -∗ ▷ □ (P ↔ Q) -∗ inv p N Q := by
  unfold inv
  iintro ⟨%i, %Hin, HI⟩ #HPQ
  iexists i
  isplit; (· itrivial)
  iapply inv_iff $$ HI
  inext; imodintro
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

theorem alloc : ⊢@{IProp GF} |==> ∃ p : NaInvPoolName, own p ⊤ :=
  iOwn_alloc (E := W.inv) (ULift.up ((.valid (⊤ : CoPset), .valid (∅ : PosSet)) : NaInvR)) ⟨trivial, trivial⟩

theorem own_disjoint {p : NaInvPoolName} {E1 E2 : CoPset} :
    ⊢ own (GF := GF) p E1 -∗ own p E2 -∗ ⌜E1 ## E2⌝ := by
  unfold own
  iintro H1 H2
  ihave H := iOwn_op $$ [H1 H2]
  · isplitl [H1] <;> iassumption
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete $$ H with %H
  ipureintro
  exact valid_op_iff_disj.mp H.1

theorem own_union {p : NaInvPoolName} {E1 E2 : CoPset} (Hdisj : E1 ## E2) :
    own (GF := GF) p (E1 ∪ E2) ⊣⊢ own p E1 ∗ own p E2 := by
  refine .trans ?_ iOwn_op
  refine (congrArg (fun x : NaInvR => iOwn (E := W.inv) p (ULift.up x)) ?_).to_bi
  refine .symm (OFE.equiv_prod_ext (disj_op_union Hdisj) ?_)
  exact (disj_op_union disjoint_empty_left).trans (by simp)

theorem own_acc {E2 E1 : CoPset} {tid : NaInvPoolName} (Hsub : E2 ⊆ E1) :
    ⊢ own (GF := GF) tid E1 -∗ own tid E2 ∗ (own tid E2 -∗ own tid E1) := by
  rw [← subset_union_diff Hsub]
  iintro H
  icases (own_union disjoint_diff_right).mp $$ H with ⟨H1, H2⟩
  isplitl [H1]; iassumption
  iintro H1
  iapply (own_union disjoint_diff_right).mpr
  isplitl [H1] <;> iassumption

theorem own_empty (p : NaInvPoolName) : ⊢@{IProp GF} |==> own p ∅ := iOwn_unit (E := W.inv)

nonrec theorem inv_alloc {p : NaInvPoolName} {E : CoPset} {N : Namespace} {P : IProp GF} :
    ⊢ ▷ P ={E}=∗ inv p N P := by
  iintro HP
  imod (iOwn_unit (E := W.inv) (γ := p) (ε := ULift.up ((.valid ∅, .valid ∅) : NaInvR))) with Hempty
  have Hupd : (.valid (∅ : CoPset), .valid (∅ : PosSet)) ~~>:
      fun y : NaInvR => ∃ i, y = (.valid ∅, .valid {i}) ∧ i ∈ (↑N : CoPset) :=
    .prod (P := (· = .valid ∅)) (.id rfl) (alloc_empty_updateP_strong' (fresh_name · N))
      (fun a b ha ⟨i, hb, hi⟩ => ⟨i, Prod.ext ha hb, hi⟩)
  imod iOwn_updateP (ULift.updateP Hupd) $$ Hempty with ⟨%y, %Hy, Hown⟩
  obtain ⟨y⟩ := y
  obtain ⟨i, rfl, Hi⟩ := Hy
  unfold inv
  imod inv_alloc N E iprop( P ∗ iOwn (E := W.inv) p (ULift.up (.valid ∅, .valid {i})) ∨ own p {i}) $$ [HP Hown]
    with HI
  · inext; ileft; isplitl [HP] <;> iassumption
  imodintro
  iexists i
  isplit
  · ipureintro; assumption
  · iassumption

/-- Accessing a non-atomic invariant, weakening its contents to a timeless proposition
(Rocq: `na_inv_acc_open_timeless_weakening`). In Transfinite Iris, `▷ (P ∗ Q)` cannot be split in
general, so the contents of the invariant are only accessed through a timeless `Q`. -/
theorem inv_acc_open_timeless_weakening {p : NaInvPoolName} {E F : CoPset} {N : Namespace}
    {P Q : IProp GF} [Timeless Q] (HNE : ↑N ⊆ E) (HNF : ↑N ⊆ F) :
    ⊢ inv p N P -∗ own p F -∗ □ (P -∗ Q) ={E}=∗
      Q ∗ own p (F \ ↑N) ∗ (▷ P ∗ own p (F \ ↑N) ={E}=∗ own p F) := by
  unfold inv
  iintro #⟨%i, %Hin, Hinv⟩ Htoks #HPQ
  have HNminusi : ↑N = {i} ∪ ((↑N : CoPset) \ {i}) := by
    refine (subset_union_diff ?_).symm
    intro x hx; rw [mem_singleton] at hx; exact hx ▸ Hin
  icases (own_union disjoint_diff_right).mp $$ [Htoks] with ⟨HtokN, HtokRest⟩
  · rw [subset_union_diff HNF]
    iassumption
  icases (own_union disjoint_diff_right).mp $$ [HtokN] with ⟨Htoki, HtokNdi⟩
  · rw [← HNminusi]; iassumption
  imod inv_acc HNE $$ Hinv with ⟨Hcontent, Hclose⟩
  ihave Hc : ▷ (Q ∗ iOwn (E := W.inv) p (ULift.up (.valid ∅, .valid {i})) ∨ own p {i}) $$ [Hcontent]
  · inext
    icases Hcontent with (⟨HP, Ho⟩ | Ho)
    · ileft
      isplitl [HP]
      · iapply HPQ $$ HP
      · iexact Ho
    · iright
      iexact Ho
  icases Hc with >Hc
  icases Hc with (⟨HQ, Hdis⟩ | Htoki2)
  · ihave Hreturn : ▷ (P ∗ iOwn (E := W.inv) p (ULift.up (.valid ∅, .valid {i})) ∨ own p {i}) $$ [Htoki]
    · inext; iright; iassumption
    imod Hclose $$ Hreturn with _
    imodintro
    isplitl [HQ]; iassumption
    isplitl [HtokRest]; iassumption
    iintro ⟨HPret, HtokFret⟩
    imod inv_acc HNE $$ Hinv with ⟨Hcontent2, Hclose2⟩
    ihave Hc2 : ▷ (Q ∗ iOwn (E := W.inv) p (ULift.up (.valid ∅, .valid {i})) ∨ own p {i}) $$ [Hcontent2]
    · inext
      icases Hcontent2 with (⟨HP, Ho⟩ | Ho)
      · ileft
        isplitl [HP]
        · iapply HPQ $$ HP
        · iexact Ho
      · iright
        iexact Ho
    icases Hc2 with >Hc2
    icases Hc2 with (⟨_, Hdis2⟩ | Htoki_back)
    · iexfalso
      ihave Hk := iOwn_op (E := W.inv) $$ [Hdis Hdis2]
      · isplitl [Hdis] <;> iassumption
      ihave Hk := iOwn_cmraValid $$ Hk
      icases internalCmraValid_discrete $$ Hk with %Hbad
      have Hk := DisjointLeibnizSet.valid_op_iff_disj.mp Hbad.2
      exact Hk i ⟨mem_singleton.mpr rfl, mem_singleton.mpr rfl⟩ |>.elim
    · ihave Hreturn2 : ▷ (P ∗ iOwn (E := W.inv) p (ULift.up (.valid ∅, .valid {i})) ∨ own p {i})
        $$ [HPret Hdis]
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

/-- Rocq: `na_inv_acc_open_timeless`. -/
theorem inv_acc_open_timeless {p : NaInvPoolName} {E F : CoPset} {N : Namespace}
    {P : IProp GF} [Timeless P] (HNE : ↑N ⊆ E) (HNF : ↑N ⊆ F) :
    ⊢ inv p N P -∗ own p F ={E}=∗
      P ∗ own p (F \ ↑N) ∗ (▷ P ∗ own p (F \ ↑N) ={E}=∗ own p F) := by
  iintro #HI Hna
  iapply inv_acc_open_timeless_weakening HNE HNF $$ HI Hna
  iintro !> HP
  iexact HP

/-- Accessing a non-atomic invariant: the contents, the remaining tokens and the closing view
shift are available after a later (Rocq: `na_inv_acc_open`). -/
theorem inv_acc_open {p : NaInvPoolName} {E F : CoPset} {N : Namespace} {P : IProp GF}
    (HNE : ↑N ⊆ E) (HNF : ↑N ⊆ F) :
    ⊢ inv p N P -∗ own p F ={E}=∗
      ▷ (P ∗ own p (F \ ↑N) ∗ (▷ P ∗ own p (F \ ↑N) ={E}=∗ own p F)) := by
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
  imod inv_acc HNE $$ Hinv with ⟨Hcontent, Hclose⟩
  icases later_or.mp $$ Hcontent with (Hl | Htoki2)
  · imod Hclose $$ [Htoki] with _
    · inext; iright; iassumption
    imodintro
    inext
    icases Hl with ⟨HP, Hdis⟩
    isplitl [HP]; iassumption
    isplitl [HtokRest]; iassumption
    iintro ⟨HPret, HtokFret⟩
    imod inv_acc HNE $$ Hinv with ⟨Hcontent2, Hclose2⟩
    icases later_or.mp $$ Hcontent2 with (Hl2 | Hitok)
    · ihave Hfalse : ▷ (False : IProp GF) $$ [Hl2 Hdis]
      · inext
        icases Hl2 with ⟨_, Hdis2⟩
        ihave Hk := iOwn_op (E := W.inv) $$ [Hdis Hdis2]
        · isplitl [Hdis] <;> iassumption
        ihave Hk := iOwn_cmraValid $$ Hk
        icases internalCmraValid_discrete $$ Hk with %Hbad
        have Hk := DisjointLeibnizSet.valid_op_iff_disj.mp Hbad.2
        exact Hk i ⟨mem_singleton.mpr rfl, mem_singleton.mpr rfl⟩ |>.elim
      icases Hfalse with >Hfalse
      icases Hfalse with ⟨⟩
    · icases Hitok with >Htoki_back
      imod Hclose2 $$ [HPret Hdis] with _
      · inext; ileft; isplitl [HPret] <;> iassumption
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
  · icases Htoki2 with >Htoki2
    iexfalso
    ihave Hbad : ⌜({i} : CoPset) ## {i}⌝ $$ [Htoki Htoki2]
    · iapply own_disjoint $$ Htoki Htoki2
    icases Hbad with %Hbad
    exact Hbad i ⟨mem_singleton.mpr rfl, mem_singleton.mpr rfl⟩ |>.elim

instance intoInv_na (N : Namespace) (P : IProp GF) :
    IntoInv (inv p N P) N := {}

end NonAtomicInvariant
end Iris.Transfinite
