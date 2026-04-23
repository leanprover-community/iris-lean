/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
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

/-! ## Non-atomic ("thread-local") invariants
Port of `iris/base_logic/lib/na_invariants.v`.

Iris-Rocq's `into_inv_na` / `into_acc_na` proofmode instances are not ported,
because the Lean proofmode does not yet provide the corresponding `IntoInv` /
`IntoAcc` classes.
-/

namespace Iris

open BI CMRA OFE Iris Std LawfulSet DisjointLeibnizSet

/-- The functor underlying a non-atomic invariant pool: products of a coPset
of enabled tokens and a `PosSet` of currently-held thread-local permissions. -/
abbrev NaInvF : COFE.OFunctorPre :=
  ProdOF (COFE.constOF (DisjointLeibnizSet CoPset))
    (COFE.constOF (DisjointLeibnizSet PosSet))

@[rocq_alias na_invG]
class NaInvG (GF : BundledGFunctors) where
  [elemG : ElemG GF NaInvF]

attribute [reducible] NaInvG.elemG
attribute [instance] NaInvG.elemG

@[rocq_alias na_inv_pool_name]
abbrev NaInvPoolName := GName

/-- Discrete elements of the `DisjointLeibnizSet` CMRA. Needed for `Timeless`
instances on `iOwn` at this CMRA. -/
instance DisjointLeibnizSet.instDiscreteE {S : Type _} (x : DisjointLeibnizSet S) :
    DiscreteE x where
  discrete h := h

instance NaInvF.instDiscreteE {α β : Type _} (x : DisjointLeibnizSet α) (y : DisjointLeibnizSet β) :
    DiscreteE (x, y) :=
  prod.is_discrete (DisjointLeibnizSet.instDiscreteE _) (DisjointLeibnizSet.instDiscreteE _)

/-- The unit element of the non-atomic-invariants CMRA is core-id. -/
instance coreId_valid_empty_pair :
    CMRA.CoreId
      ((DisjointLeibnizSet.valid (∅ : CoPset), DisjointLeibnizSet.valid (∅ : PosSet))) where
  core_id := by
    show CMRA.pcore _ ≡ _
    rfl

instance isUnit_valid_empty_pair :
    IsUnit ((DisjointLeibnizSet.valid (∅ : CoPset), DisjointLeibnizSet.valid (∅ : PosSet))) where
  unit_valid := ⟨trivial, trivial⟩
  unit_left_id := ⟨UCMRA.unit_left_id, UCMRA.unit_left_id⟩
  pcore_unit := coreId_valid_empty_pair.core_id

section defs

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [W : NaInvG GF]

@[rocq_alias na_own]
def na_own (p : NaInvPoolName) (E : CoPset) : IProp GF :=
  iOwn (E := W.elemG) p (DisjointLeibnizSet.valid E, DisjointLeibnizSet.valid ∅)

@[rocq_alias na_inv]
def na_inv (p : NaInvPoolName) (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(∃ i, ⌜i ∈ (↑N : CoPset)⌝ ∧
        inv N iprop(
          P ∗ iOwn (E := W.elemG) p (DisjointLeibnizSet.valid ∅, DisjointLeibnizSet.valid {i})
          ∨ na_own p {i}))

end defs

section proofs

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [W : NaInvG GF]

@[rocq_alias na_own_timeless]
instance na_own_timeless (p : NaInvPoolName) (E : CoPset) :
    Timeless (na_own (GF := GF) p E) := by
  simp only [na_own]
  infer_instance

@[rocq_alias na_inv_contractive]
instance na_inv_contractive (p : NaInvPoolName) (N : Namespace) :
    Contractive (na_inv (GF := GF) p N) where
  distLater_dist {n x y} H := by
    simp only [na_inv]
    refine exists_ne fun i => ?_
    refine and_ne.ne .rfl ?_
    refine Contractive.distLater_dist ?_
    intro m hm
    refine or_ne.ne ?_ .rfl
    exact sep_ne.ne (H _ hm) .rfl

@[rocq_alias na_inv_ne]
instance na_inv_ne (p : NaInvPoolName) (N : Namespace) :
    NonExpansive (na_inv (GF := GF) p N) := ne_of_contractive _

@[rocq_alias na_inv_persistent]
instance na_inv_persistent (p : NaInvPoolName) (N : Namespace) (P : IProp GF) :
    Persistent (na_inv p N P) := by
  simp only [na_inv]
  infer_instance

@[rocq_alias na_own_empty_persistent]
instance na_own_empty_persistent (p : NaInvPoolName) :
    Persistent (na_own (GF := GF) p ∅) := by
  simp only [na_own]
  infer_instance

@[rocq_alias na_inv_iff]
theorem na_inv_iff (p : NaInvPoolName) (N : Namespace) (P Q : IProp GF) :
    ⊢ na_inv p N P -∗ ▷ □ (P ↔ Q) -∗ na_inv p N Q := by
  simp only [na_inv]
  iintro ⟨%i, %Hin, HI⟩ #HPQ
  iexists i
  isplit
  · ipure_intro; assumption
  iapply inv_iff $$ HI
  inext; imodintro
  simp only [BI.iff]
  isplit
  · iintro H
    icases H with (⟨HP, Ho⟩ | Htok)
    · ileft
      isplitr [Ho]
      · icases HPQ with ⟨HPQm, _⟩
        iapply HPQm $$ HP
      · iassumption
    · iright; iassumption
  · iintro H
    icases H with (⟨HQ, Ho⟩ | Htok)
    · ileft
      isplitr [Ho]
      · icases HPQ with ⟨_, HQPm⟩
        iapply HQPm $$ HQ
      · iassumption
    · iright; iassumption

@[rocq_alias na_alloc]
theorem na_alloc : ⊢@{IProp GF} |==> ∃ p : NaInvPoolName, na_own p ⊤ := by
  simp only [na_own]
  exact iOwn_alloc (E := W.elemG)
    (DisjointLeibnizSet.valid (⊤ : CoPset), DisjointLeibnizSet.valid (∅ : PosSet))
    ⟨trivial, trivial⟩

@[rocq_alias na_own_disjoint]
theorem na_own_disjoint (p : NaInvPoolName) (E1 E2 : CoPset) :
    ⊢ na_own (GF := GF) p E1 -∗ na_own p E2 -∗ ⌜E1 ## E2⌝ := by
  simp only [na_own]
  iintro H1 H2
  ihave H := iOwn_op (E := W.elemG) $$ [H1 H2]
  · isplitl [H1] <;> iassumption
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete (A := NaInvF.ap (IProp GF)) $$ H with %H
  ipure_intro
  exact valid_op_iff_disj.mp H.1

@[rocq_alias na_own_union]
theorem na_own_union (p : NaInvPoolName) (E1 E2 : CoPset) (Hdisj : E1 ## E2) :
    na_own (GF := GF) p (E1 ∪ E2) ⊣⊢ na_own p E1 ∗ na_own p E2 := by
  simp only [na_own]
  have hempty :
      DisjointLeibnizSet.valid (∅ : PosSet) ≡
        DisjointLeibnizSet.valid (∅ : PosSet) • DisjointLeibnizSet.valid ∅ := by
    refine .trans ?_ (disj_op_union (S := PosSet) disjoint_empty_left).symm
    exact Equiv.of_eq (by simp)
  have heq : (DisjointLeibnizSet.valid (E1 ∪ E2), DisjointLeibnizSet.valid ∅) ≡
      ((DisjointLeibnizSet.valid E1, DisjointLeibnizSet.valid ∅) •
       (DisjointLeibnizSet.valid E2, DisjointLeibnizSet.valid (∅ : PosSet))) :=
    equiv_prod_ext (disj_op_union Hdisj).symm hempty
  refine .trans ?_ iOwn_op
  exact BI.equiv_iff.mp (NonExpansive.eqv (f := iOwn (E := W.elemG) p) heq)

@[rocq_alias na_own_acc]
theorem na_own_acc (E2 E1 : CoPset) (tid : NaInvPoolName) (Hsub : E2 ⊆ E1) :
    ⊢ na_own (GF := GF) tid E1 -∗ na_own tid E2 ∗ (na_own tid E2 -∗ na_own tid E1) := by
  have Heq : E1 = E2 ∪ (E1 \ E2) := by
    rw [union_comm]; exact diff_subset_decomp Hsub
  rw [Heq]
  iintro H
  icases (na_own_union tid E2 (E1 \ E2) disjoint_diff_right).mp $$ H with ⟨H1, H2⟩
  isplitl [H1]; iassumption
  iintro H1
  iapply (na_own_union tid E2 (E1 \ E2) disjoint_diff_right).mpr
  isplitl [H1] <;> iassumption

@[rocq_alias na_own_empty]
theorem na_own_empty (p : NaInvPoolName) : ⊢@{IProp GF} |==> na_own p ∅ := by
  simp only [na_own]
  exact iOwn_unit (E := W.elemG)
    (ε := (DisjointLeibnizSet.valid ∅, DisjointLeibnizSet.valid ∅))

@[rocq_alias na_inv_alloc]
theorem na_inv_alloc (p : NaInvPoolName) (E : CoPset) (N : Namespace) (P : IProp GF) :
    ⊢ ▷ P ={E}=∗ na_inv p N P := by
  iintro HP
  imod (iOwn_unit (E := W.elemG) (γ := p)
      (ε := (DisjointLeibnizSet.valid ∅, DisjointLeibnizSet.valid ∅))) with Hempty
  have Hupd :
      ((DisjointLeibnizSet.valid (∅ : CoPset), DisjointLeibnizSet.valid (∅ : PosSet)))
      ~~>: (fun y : NaInvF.ap (IProp GF) =>
        ∃ i : Pos, y = (DisjointLeibnizSet.valid ∅, DisjointLeibnizSet.valid {i}) ∧
          i ∈ (↑N : CoPset)) := by
    refine UpdateP.prod (α := DisjointLeibnizSet CoPset) (β := DisjointLeibnizSet PosSet)
      (P := (· = DisjointLeibnizSet.valid ∅))
      (Q := fun y => ∃ i : Pos, y = DisjointLeibnizSet.valid {i} ∧ i ∈ (↑N : CoPset))
      (UpdateP.id rfl)
      (DisjointLeibnizSet.alloc_empty_updateP_strong' (fun Y => fresh_name Y N))
      (fun a b ha ⟨i, hb, hi⟩ => ⟨i, by simp [ha, hb], hi⟩)
  imod iOwn_updateP Hupd $$ Hempty with ⟨%y, %Hy, Hown⟩
  obtain ⟨i, rfl, Hi⟩ := Hy
  simp only [na_inv]
  imod inv_alloc N E iprop(
    P ∗ iOwn (E := W.elemG) p (DisjointLeibnizSet.valid ∅, DisjointLeibnizSet.valid {i})
    ∨ na_own p {i}) $$ [HP Hown] with HI
  · inext; ileft; isplitl [HP] <;> iassumption
  imodintro
  iexists i
  isplit
  · ipure_intro; assumption
  · iassumption

@[rocq_alias na_inv_acc]
theorem na_inv_acc (p : NaInvPoolName) (E F : CoPset) (N : Namespace) (P : IProp GF)
    (HNE : ↑N ⊆ E) (HNF : ↑N ⊆ F) :
    ⊢ na_inv p N P -∗ na_own p F ={E}=∗
      ▷ P ∗ na_own p (F \ ↑N) ∗
      (▷ P ∗ na_own p (F \ ↑N) ={E}=∗ na_own p F) := by
  simp only [na_inv]
  iintro #⟨%i, %Hin, Hinv⟩ Htoks
  -- Split Htoks : na_own p F = na_own p ({i} ∪ (↑N \ {i})) ∗ na_own p (F \ ↑N)
  have HiN : ({i} : CoPset) ⊆ (↑N : CoPset) := by
    intro x hx; rw [mem_singleton] at hx; subst hx; exact Hin
  have HeqN : ↑N = {i} ∪ ((↑N : CoPset) \ {i}) := by
    rw [union_comm]; exact diff_subset_decomp HiN
  have HeqF : F = ↑N ∪ (F \ ↑N) := by
    rw [union_comm]; exact diff_subset_decomp HNF
  ihave Htoks' : na_own p (↑N ∪ (F \ ↑N)) $$ [Htoks]
  · rw [← HeqF]; iassumption
  icases (na_own_union p ↑N (F \ ↑N) disjoint_diff_right).mp $$ Htoks' with ⟨HtokN, HtokRest⟩
  ihave HtokN' : na_own p ({i} ∪ ((↑N : CoPset) \ {i})) $$ [HtokN]
  · rw [← HeqN]; iassumption
  icases (na_own_union p {i} (↑N \ {i}) disjoint_diff_right).mp $$ HtokN' with ⟨Htoki, HtokNdi⟩
  -- Open the invariant.
  imod inv_acc _ _ _ HNE $$ Hinv with ⟨Hcontent, Hclose⟩
  icases Hcontent with (⟨HP, >Hdis⟩ | >Htoki2)
  · -- Left branch: got P and the stored token. Close with Htoki in right branch.
    ihave Hreturn : iprop(▷ (P ∗ iOwn (E := W.elemG) p
            (DisjointLeibnizSet.valid ∅, DisjointLeibnizSet.valid {i}) ∨ na_own p {i}))
        $$ [Htoki]
    · inext; iright; iassumption
    imod Hclose $$ Hreturn with _
    imodintro
    isplitl [HP]; iassumption
    isplitl [HtokRest]; iassumption
    -- Returner: user gives back ▷P and na_own p (F \ ↑N). We need to give back na_own p F.
    iintro ⟨HPret, HtokFret⟩
    imod inv_acc _ _ _ HNE $$ Hinv with ⟨Hcontent2, Hclose2⟩
    icases Hcontent2 with (⟨_HPconflict, >Hdis2⟩ | >Htoki_back)
    · -- Impossible: two copies of own p (ε, {i}) would have disjoint tokens.
      iexfalso
      ihave Hbad := iOwn_op (E := W.elemG) $$ [Hdis Hdis2]
      · isplitl [Hdis] <;> iassumption
      ihave Hbad := iOwn_cmraValid $$ Hbad
      icases internalCmraValid_discrete (A := NaInvF.ap (IProp GF)) $$ Hbad with %Hbad
      ipure_intro
      have Hbad2 := DisjointLeibnizSet.valid_op_iff_disj.mp Hbad.2
      exact Hbad2 i ⟨mem_singleton.mpr rfl, mem_singleton.mpr rfl⟩
    · -- Good branch: consume Htoki_back, close with (P, Hdis) left branch.
      ihave Hreturn2 : iprop(▷ (P ∗ iOwn (E := W.elemG) p
              (DisjointLeibnizSet.valid ∅, DisjointLeibnizSet.valid {i}) ∨ na_own p {i}))
          $$ [HPret Hdis]
      · inext; ileft; isplitl [HPret] <;> iassumption
      imod Hclose2 $$ Hreturn2 with _
      imodintro
      -- Combine Htoki_back, HtokNdi, HtokFret into na_own p F.
      ihave HtokN_new : na_own p ((↑N : CoPset)) $$ [Htoki_back HtokNdi]
      · conv => rhs; rw [show (↑N : CoPset) = {i} ∪ (↑N \ {i}) from HeqN]
        iapply (na_own_union p {i} (↑N \ {i}) disjoint_diff_right).mpr
        isplitl [Htoki_back]
        · iexact Htoki_back
        · iexact HtokNdi
      conv => rhs; rw [show F = (↑N : CoPset) ∪ (F \ ↑N) from HeqF]
      iapply (na_own_union p ↑N (F \ ↑N) disjoint_diff_right).mpr
      isplitl [HtokN_new]
      · iexact HtokN_new
      · iexact HtokFret
  · -- Right branch: two na_own p {i} would contradict disjointness.
    iexfalso
    ihave Hbad : ⌜({i} : CoPset) ## {i}⌝ $$ [Htoki Htoki2]
    · ihave Hd1 := na_own_disjoint p {i} {i} $$ Htoki
      iapply Hd1 $$ Htoki2
    icases Hbad with %Hbad
    exact Hbad i ⟨mem_singleton.mpr rfl, mem_singleton.mpr rfl⟩ |>.elim

end proofs

end Iris

end
