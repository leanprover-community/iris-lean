/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.ProofMode
public import Iris.BI.InternalEq
public import Iris.BI.BigOp.BigSepMap
public import Iris.BI.Algebra
public import Iris.Std.GenSetsInstances
public import Iris.Std.HeapInstances
public import Iris.Instances.IProp

@[expose] public section

/-! ## World satisfaction
This file defines the world satisfaction (wsat) predicate for Iris.
-/

namespace Iris

open Iris Std OFE COFE BI HeapView PartialMap DisjointLeibnizSet DFrac LawfulPartialMap BigSepM
  HeapView

section WsatGS

abbrev PosSet := Std.ExtTreeSet Pos compare

abbrev InvMap (x : Type _) := Std.ExtTreeMap Pos x compare

abbrev InvMapF (GF : BundledGFunctors) :=
  HeapViewURF (F := PNat) (H := InvMap) (AgreeRF (LaterOF (constOF (IProp GF))))

/-- Wsat inclusion typeclass (`GF` contains the necessary functors for wsat) -/
class WsatGpreS (GF : BundledGFunctors) where
  inv : ElemG GF (InvMapF GF)
  enabled : ElemG GF (constOF (DisjointLeibnizSet CoPset))
  disabled : ElemG GF (constOF (DisjointLeibnizSet PosSet))

attribute [reducible, instance] WsatGpreS.inv
attribute [reducible, instance] WsatGpreS.enabled
attribute [reducible, instance] WsatGpreS.disabled

/-- Wsat allocated class (Names in a global IProp resource for the Wsat resources). -/
class WsatGS (GF : BundledGFunctors) extends WsatGpreS GF where
  invariant_name : GName
  enabled_name : GName
  disabled_name : GName

end WsatGS

section Definitions

variable {GF : BundledGFunctors} [W : WsatGS GF]

abbrev invariant_unfold (P : IProp GF) : Later (IProp GF) := Later.next P

def ownI (i : Pos) (P : IProp GF) : IProp GF :=
  iOwn (E := W.inv) W.invariant_name (Frag i discard (toAgree (invariant_unfold P)))

def ownE (S : CoPset) : IProp GF :=
  iOwn (E := W.enabled) W.enabled_name (valid S)

def ownD (S : PosSet) : IProp GF :=
  iOwn (E := W.disabled) W.disabled_name (valid S)

def wsat : IProp GF := iprop(
  ∃ I : InvMap (IProp GF),
    iOwn (E := W.inv) W.invariant_name (Auth (own 1) (map toAgree (map invariant_unfold I))) ∗
    [∗map] i ↦ Q ∈ I, (▷ Q ∗ ownD {i}) ∨ ownE {i})

instance (i : Pos) : Contractive (ownI (W := W) i) where
  distLater_dist h := by
    unfold ownI
    refine NonExpansive.ne ?_
    refine NonExpansive.ne ?_
    refine NonExpansive.ne ?_
    exact Contractive.distLater_dist h

instance (i : Pos) (P : IProp GF) : Persistent (ownI (W := W) i P) := by
  unfold ownI; infer_instance

-- Here

end Definitions

section ownE

variable {GF : BundledGFunctors} [W : WsatGS GF]

theorem ownE_empty : ⊢ |==> ownE (W := W) ∅ := by
  unfold ownE; exact iOwn_unit (ε := UCMRA.unit)

theorem ownE_op (E1 E2 : CoPset) (Hdisj : E1 ## E2) :
    ownE (E1 ∪ E2) ⊣⊢@{IProp GF} ownE E1 ∗ ownE E2 := by
  unfold ownE
  simp only [show valid (E1 ∪ E2) = valid E1 • valid E2 from (disj_op_union Hdisj).symm]
  exact iOwn_op

theorem ownE_disjoint (E1 E2 : CoPset) :
    ownE E1 ∗ ownE E2 ⊢@{IProp GF} ⌜E1 ## E2⌝ := by
  unfold ownE
  iintro ⟨H1, H2⟩
  icases iOwn_op (E := W.enabled) $$ [H1 H2] with H;
    isplitl [H1] <;> iassumption
  icases iOwn_cmraValid (E := W.enabled) $$ H with H
  icases internalCmraValid_discrete (PROP := IProp GF) (A := DisjointLeibnizSet CoPset) $$ H with %H
  ipure_intro
  exact valid_op_iff_disj.mp H

theorem ownE_op' (E1 E2 : CoPset) :
    ⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2) ⊣⊢@{IProp GF} ownE E1 ∗ ownE E2 := by
  constructor
  · iintro ⟨%Hdisj, H⟩
    iapply (ownE_op E1 E2 Hdisj).mp $$ H
  · iintro ⟨H1, H2⟩
    ihave %Hdisj : ⌜E1 ## E2⌝ $$ [H1 H2]; iapply ownE_disjoint $$ [H1 H2]; isplitl [H1] <;> iassumption
    isplit
    · ipure_intro; assumption
    · iapply (ownE_op E1 E2 Hdisj).mpr $$ [H1 H2]; isplitl [H1] <;> iassumption

theorem ownE_singleton_twice (i : Pos) : ownE {i} ∗ ownE {i} ⊢@{IProp GF} False :=
  (ownE_disjoint {i} {i}).trans (pure_mono fun h => h i (by simp [mem_singleton]))

end ownE

section ownD

variable {GF : BundledGFunctors} [W : WsatGS GF]

theorem ownD_empty : ⊢@{IProp GF} |==> ownD ∅ := by
  unfold ownD; exact iOwn_unit (ε := UCMRA.unit)

theorem ownD_op (E1 E2 : PosSet) (Hdisj : E1 ## E2) :
    ownD (E1 ∪ E2) ⊣⊢@{IProp GF} ownD E1 ∗ ownD E2 := by
  unfold ownD
  simp only [show valid (E1 ∪ E2) = valid E1 • valid E2 from (disj_op_union Hdisj).symm]
  exact iOwn_op

theorem ownD_disjoint (E1 E2 : PosSet) :
    ownD E1 ∗ ownD E2 ⊢@{IProp GF}  ⌜E1 ## E2⌝ := by
  unfold ownD
  iintro ⟨H1, H2⟩
  icases iOwn_op (E := W.disabled) $$ [H1 H2] with H;
    isplitl [H1] <;> iassumption
  icases iOwn_cmraValid (E := W.disabled) $$ H with H
  icases internalCmraValid_discrete (PROP := IProp GF) (A := DisjointLeibnizSet PosSet) $$ H with %H
  ipure_intro
  exact valid_op_iff_disj.mp H

theorem ownD_op' (E1 E2 : PosSet) :
    ⌜E1 ## E2⌝ ∧ ownD (E1 ∪ E2) ⊣⊢@{IProp GF} ownD E1 ∗ ownD E2 := by
  constructor
  · iintro ⟨%Hdisj, H⟩
    iapply (ownD_op E1 E2 Hdisj).mp $$ H
  · iintro ⟨H1, H2⟩
    ihave %Hdisj : ⌜E1 ## E2⌝ $$ [H1 H2]; iapply ownD_disjoint $$ [H1 H2]; isplitl [H1] <;> iassumption
    isplit
    · ipure_intro; assumption
    · iapply (ownD_op E1 E2 Hdisj).mpr $$ [H1 H2]; isplitl [H1] <;> iassumption

theorem ownD_singleton_twice (i : Pos) :
    ownD {i} ∗ ownD {i} ⊢@{IProp GF} False :=
    (ownD_disjoint {i} {i}).trans (pure_mono fun h => h i (by simp))

end ownD

section operations

variable {GF : BundledGFunctors} [W : WsatGS GF]

theorem invariant_lookup (I : InvMap (IProp GF)) (i : Pos) (P : IProp GF) :
  iOwn (E := W.inv) W.invariant_name (Auth (own 1) (map toAgree (map invariant_unfold I)))
  ∗ ownI i P ⊢@{IProp GF}  ∃ Q, ⌜get? I i = .some Q⌝ ∗ ▷ internalEq Q P := by
  unfold ownI
  iintro H; icases iOwn_cmraValid_op (E := W.inv) $$ H with H
  icases (auth_op_frag_validI_total (F := PNat) (PROP := (IProp GF)) (own 1)
          (map toAgree (map invariant_unfold I))) $$ H
    with ⟨%v', %dp', %Hdp, %Hlookup, H1, H2⟩
  simp only [get?_map, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at Hlookup
  have ⟨Q', Hget, Hagree⟩ := Hlookup
  iexists Q'; isplit; ipure_intro; assumption
  rw [←Hagree]
  iapply later_equivI_mp; iapply internalEq.symm; iapply toAgree_includedI $$ H2

theorem ownI_open (i : Pos) (P : IProp GF) :
    wsat ∗ ownI i P ∗ ownE {i} ⊢ wsat ∗ ▷ P ∗ ownD {i} := by
    unfold wsat
    iintro ⟨⟨%I, Hown, Hmap⟩, #HI, HE⟩
    icases invariant_lookup I i P $$ [Hown HI] with #⟨%Q, %HEQ, #H⟩; isplit <;> iassumption
    icases bigSepM_delete (PROP := IProp GF) HEQ $$ Hmap with ⟨⟨⟨HProp, HD⟩ | HE'⟩, Hacc⟩
    · isplitr [HProp HD]
      · iexists I
        isplitl [Hown]; iassumption
        iapply bigSepM_delete HEQ
        isplitl [HE]; iright; iassumption
        iassumption
      · isplitl [HProp]
        · inext; iapply internalEq.rewrite (Ψ := fun x => x) (hΨ := OFE.id_ne) $$ H HProp
        · iassumption
    · iexfalso; iapply ownE_singleton_twice i $$ [HE HE']; isplitl [HE] <;> iassumption

theorem ownI_close (i : Pos) (P : IProp GF) :
    wsat ∗ ownI i P ∗ ▷ P ∗ ownD {i} ⊢ wsat ∗ ownE {i} := by
  unfold wsat
  iintro ⟨⟨%I, Hown, Hmap⟩, #HI, HProp, HE⟩
  icases invariant_lookup I i P $$ [Hown HI] with #⟨%Q, %HEQ, #H⟩; isplit <;> iassumption
  icases bigSepM_delete (PROP := IProp GF) HEQ $$ Hmap with ⟨⟨⟨HProp, HD⟩ | HE'⟩, Hacc⟩
  · iexfalso; iapply ownD_singleton_twice i $$ [HD HE]; isplitl [HE] <;> iassumption
  · isplitr [HE']
    · iexists I
      isplitl [Hown]; iassumption
      iapply bigSepM_delete HEQ
      isplitl [HE HProp]; ileft; isplitr [HE]
      · inext
        iapply internalEq.rewrite (Ψ := fun x => x) (hΨ := OFE.id_ne) $$ [H] HProp
        iapply internalEq.symm; iassumption
      · iassumption
      iassumption
    · iapply HE'

end operations

section allocation

variable {GF : BundledGFunctors}

open BI HeapView BigSepM Std.PartialMap DisjointLeibnizSet LawfulPartialMap FiniteMap LawfulFiniteMap

theorem ownI_alloc [W : WsatGS GF] (φ : Pos → Prop) (P : IProp GF)
    (Hfresh : ∀ E : PosSet, ∃ i, i ∉ E ∧ φ i) :
    ⊢ wsat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ wsat ∗ ownI i P := by
  letI elem1 : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := W.inv
  letI elem2 : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := W.enabled
  letI elem3 : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := W.disabled
  unfold wsat ownI ownE
  iintro ⟨⟨%I, ⟨Hown, Hmap⟩⟩, HProp⟩
  imod ownD_empty (W := W) with HD; unfold ownD
  imod iOwn_updateP (E := elem3)
    (alloc_empty_updateP_strong' (P := fun i => (get? I i = .none) ∧ φ i) _) $$ HD with HD
  · intro Y
    have ⟨j, H⟩ := Hfresh (Y ∪ dom_set I)
    simp only [mem_union, not_or] at H
    obtain ⟨⟨HnotY, HnotDom⟩, Hφ⟩ := H
    simp only [mem_dom_set, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at HnotDom
    exists j
  · icases HD with ⟨%X, %H, HD⟩; obtain ⟨j, HEQ, ⟨Hget, Hφ⟩⟩ := H
    imod iOwn_update (E := elem1)
      (update_one_alloc (k := j) (dq := .discard)
        (m1 := map toAgree (map invariant_unfold I)) (v1 := toAgree (invariant_unfold P))
        _ DFrac.valid_discard  _) $$ Hown with Hown
    · simpa [get?_map]
    · exact fun _ => ⟨⟩
    · icases iOwn_op (E := elem1) $$ Hown with ⟨Hown, Hpt⟩
      imodintro
      iexists j
      isplit; ipure_intro; assumption
      isplitr [Hpt]
      · iexists insert I j P
        isplitl [Hown]
        · rw [show insert (map toAgree (map invariant_unfold I)) j (toAgree (invariant_unfold P))
            = map toAgree (map invariant_unfold (insert I j P)) by
              apply ExtensionalPartialMap.equiv_iff_eq.mp
              intro k; simp only [get?_insert, get?_map, Option.map_map]
              by_cases h : j = k <;> simp [h]]
          iexact Hown
        · iapply bigSepM_insert (PROP := IProp GF) (x := P) Hget $$ [Hmap HProp HD]
          isplitl [HProp HD]
          · rw [HEQ]; ileft; isplitl [HProp] <;> iassumption
          · iexact Hmap
      · iexact Hpt

theorem ownI_alloc_open [W : WsatGS GF] (φ : Pos → Prop) (P : IProp GF)
  (Hfresh : ∀ E : PosSet, ∃ i, i ∉ E ∧ φ i) :
  ⊢ wsat ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE {i} -∗ wsat) ∗ ownI i P ∗ ownD {i} := by
  letI elem1 : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := W.inv
  letI elem2 : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := W.enabled
  letI elem3 : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := W.disabled
  unfold wsat
  iintro ⟨%I, Hown, Hmap⟩
  imod ownD_empty (W := W) with HD; unfold ownD
  imod iOwn_updateP (E := elem3)
    (alloc_empty_updateP_strong' (P := fun i => (get? I i = .none) ∧ φ i) _) $$ HD with HD
  · intro Y
    have ⟨j, H⟩ := Hfresh (Y ∪ dom_set I)
    simp only [mem_union, not_or] at H
    obtain ⟨⟨HnotY, HnotDom⟩, Hφ⟩ := H
    simp only [mem_dom_set, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at HnotDom
    exists j
  · icases HD with ⟨%X, %H, HD⟩; obtain ⟨j, HEQ, ⟨Hget, Hφ⟩⟩ := H
    imod iOwn_update (E := elem1)
      (update_one_alloc (k := j) (dq := .discard)
        (m1 := map toAgree (map invariant_unfold I)) (v1 := toAgree (invariant_unfold P))
        _ DFrac.valid_discard  _) $$ Hown with Hown
    · simpa [get?_map]
    · exact fun _ => ⟨⟩
    · icases iOwn_op (E := elem1) $$ Hown with ⟨Hown, Hpt⟩
      imodintro
      iexists j
      isplit; ipure_intro; assumption
      isplitr [Hpt HD]
      · iintro HE; unfold ownE
        iexists insert I j P
        isplitl [Hown]
        · rw [show Std.insert (map toAgree (map invariant_unfold I)) j (toAgree (invariant_unfold P))
            = map toAgree (map invariant_unfold (Std.insert I j P)) by
              apply ExtensionalPartialMap.equiv_iff_eq.mp
              intro k; simp only [get?_insert, get?_map, Option.map_map]
              by_cases h : j = k <;> simp [h]]
          iexact Hown
        · iapply bigSepM_insert (PROP := IProp GF) (x := P) Hget $$ [Hmap HE]
          isplitl [HE]
          · iright; iassumption
          · iexact Hmap
      · unfold ownI; rw [HEQ]; isplit <;> iassumption

theorem wsat_alloc [WP : WsatGpreS GF] :
    ⊢ |==> ∃ (W : WsatGS GF), wsat (W := W) ∗ ownE CoPset.full := by
  haveI elem1 : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := WP.inv
  haveI elem2 : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := WP.enabled
  haveI elem3 : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := WP.disabled
  imod (iOwn_alloc (E := elem1) (Auth (.own 1) empty)) with ⟨%γ, H⟩; apply auth_one_valid
  imod (iOwn_alloc (E := elem2) (valid CoPset.full)) with ⟨%γe, He⟩; exact ⟨⟩
  imod (iOwn_alloc (E := elem3) (valid ∅)) with ⟨%γd, Hd⟩; exact ⟨⟩
  imodintro
  let W : WsatGS GF := { inv := elem1, enabled := elem2, disabled := elem3,
                         invariant_name := γ, enabled_name := γe, disabled_name := γd }
  iexists W
  unfold wsat
  isplitr [He]
  · iexists empty
    isplitl
    · iclear Hd
      have : map toAgree (map invariant_unfold (empty : InvMap (IProp GF))) = empty :=
        ExtensionalPartialMap.equiv_iff_eq.mp
          (fun k => by simp [get?_map, get?_empty (M := InvMap)])
      rw [this]; iassumption
    · iapply bigSepM_empty; simp
  · unfold ownE; iexact He

end allocation

end Iris
