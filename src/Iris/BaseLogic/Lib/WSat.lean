/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This file defines the world satisfaction (wsat) predicate for Iris.
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

namespace Iris.BaseLogic.WSat

open Iris Std OFE COFE BI HeapView

section wsatGS

abbrev PosSet := Std.ExtTreeSet Pos compare
abbrev InvMap (x : Type) := Std.ExtTreeMap Pos x compare

-- TODO: move
private def dom (m : InvMap x) : PosSet :=
  LawfulSet.ofList (FiniteMap.mapFold (fun k _ acc => k :: acc) [] m)

private theorem mem_dom {m : InvMap x} :
  k ∈ dom m ↔ (get? m k).isSome := by
  simp only [dom]
  rw [←LawfulSet.mem_ofList]
  simp only [FiniteMap.mapFold, List.foldl_flip_cons_eq_append, List.append_nil, List.mem_reverse,
    List.mem_map, Prod.exists, exists_and_right, exists_eq_right, Option.isSome_iff_exists]
  simp [←LawfulFiniteMap.toList_get]; rfl

variable (GF : BundledGFunctors)

class wsatGpreS where
  inv : ElemG GF (HeapViewURF (F := PNat) (H := InvMap) (AgreeRF (LaterOF (constOF (IProp GF)))))
  enabled : ElemG GF (constOF (DisjointLeibnizSet CoPset))
  disabled : ElemG GF (constOF (DisjointLeibnizSet PosSet))

class wsatGS extends wsatGpreS GF where
  invariant_name : GName
  enabled_name : GName
  disabled_name : GName

end wsatGS

section definitions

variable {GF : BundledGFunctors} (W : wsatGS GF)

open Iris PartialMap HeapView DisjointLeibnizSet DFrac

abbrev invariant_unfold (P : IProp GF) : Later (IProp GF) := Later.next P

def ownI (i : Pos) (P : IProp GF) : IProp GF :=
  haveI E : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := W.inv
  iOwn (E := E) W.invariant_name (Frag i discard (toAgree (invariant_unfold P)))

def ownE (S : CoPset) : IProp GF :=
  haveI E : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := W.enabled
  iOwn (E := E) W.enabled_name (valid S)

def ownD (S : PosSet) : IProp GF :=
  haveI E : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := W.disabled
  iOwn (E := E) W.disabled_name (valid S)

def wsat : IProp GF :=
haveI E : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := W.inv
iprop(
  ∃ I : InvMap (IProp GF),
    iOwn (E := E)
      W.invariant_name
      (Auth (own 1) (map toAgree (map invariant_unfold I)))
    ∗ [∗map] i ↦ Q ∈ I, (▷ Q ∗ ownD W {i}) ∨ ownE W {i}
)

end definitions

section instances

variable {GF : BundledGFunctors} (W : wsatGS GF)

instance : Contractive (invariant_unfold (GF := GF)) := by
  apply NextContractive

instance (i : Pos) : Contractive (ownI W i) where
  distLater_dist {n P Q} h := by
    unfold ownI invariant_unfold
    apply NonExpansive.ne; apply NonExpansive.ne; apply NonExpansive.ne
    exact Contractive.distLater_dist h

-- bad + move
instance {F} [UFraction F] : CMRA.CoreId (DFrac.discard (F := F)) where
  core_id := by simp [CMRA.pcore, DFrac.pcore]
-- bad + move
instance {α} [OFE α] (a : α) : CMRA.CoreId (toAgree a) where
  core_id := by simp [CMRA.pcore]
-- mildly bad + move
instance : IsUnit (DisjointLeibnizSet.valid (∅ : PosSet)) := inferInstanceAs (IsUnit UCMRA.unit)
-- mildly bad + move
instance : IsUnit (DisjointLeibnizSet.valid (∅ : CoPset)) := inferInstanceAs (IsUnit UCMRA.unit)

instance (i : Pos) (P : IProp GF) : Persistent (ownI W i P) := by unfold ownI; infer_instance

end instances

section lemmas_ownE

variable {GF : BundledGFunctors} (W : wsatGS GF)

open BI DisjointLeibnizSet Std

theorem ownE_empty : ⊢ |==> ownE W ∅ := by
  letI E : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := W.enabled
  unfold ownE; exact iOwn_unit

theorem ownE_op (E1 E2 : CoPset) (Hdisj : E1 ## E2) :
    ownE W (E1 ∪ E2) ⊣⊢ ownE W E1 ∗ ownE W E2 := by
  letI : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := W.enabled
  unfold ownE
  simp only [show valid (E1 ∪ E2) = valid E1 • valid E2 from (disj_op_union Hdisj).symm]
  exact iOwn_op

theorem ownE_disjoint (E1 E2 : CoPset) :
    ownE W E1 ∗ ownE W E2 ⊢ ⌜E1 ## E2⌝ := by
  letI E : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := W.enabled
  unfold ownE
  iintro ⟨H1, H2⟩
  icases iOwn_op (E := E) $$ [H1 H2] with H;
    isplitl [H1] <;> iassumption
  icases iOwn_cmraValid (E := E) $$ H with H
  icases internalCmraValid_discrete (PROP := IProp GF) (A := DisjointLeibnizSet CoPset) $$ H with %H
  ipure_intro
  exact valid_op_iff_disj.mp H

theorem ownE_op' (E1 E2 : CoPset) :
    ⌜E1 ## E2⌝ ∧ ownE W (E1 ∪ E2) ⊣⊢ ownE W E1 ∗ ownE W E2 := by
  constructor
  · iintro ⟨%Hdisj, H⟩
    iapply (ownE_op W E1 E2 Hdisj).mp $$ H
  · iintro ⟨H1, H2⟩
    ihave %Hdisj : ⌜E1 ## E2⌝ $$ [H1 H2]; iapply ownE_disjoint $$ [H1 H2]; isplitl [H1] <;> iassumption
    isplit
    · ipure_intro; assumption
    · iapply (ownE_op W E1 E2 Hdisj).mpr $$ [H1 H2]; isplitl [H1] <;> iassumption

theorem ownE_singleton_twice (i : Pos) :
    ownE W {i} ∗ ownE W {i} ⊢ False := by
  apply (ownE_disjoint W {i} {i}).trans
  apply BI.pure_mono
  intro h
  apply h i
  simp [mem_singleton]

end lemmas_ownE

section lemmas_ownD

variable {GF : BundledGFunctors} (W : wsatGS GF)

open BI DisjointLeibnizSet Std

theorem ownD_empty : ⊢ |==> ownD W ∅ := by
  let E : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := W.disabled
  unfold ownD; exact iOwn_unit

theorem ownD_op (E1 E2 : PosSet) (Hdisj : E1 ## E2) :
    ownD W (E1 ∪ E2) ⊣⊢ ownD W E1 ∗ ownD W E2 := by
  letI : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := W.disabled
  unfold ownD
  simp only [show valid (E1 ∪ E2) = valid E1 • valid E2 from (disj_op_union Hdisj).symm]
  exact iOwn_op

theorem ownD_disjoint (E1 E2 : PosSet) :
    ownD W E1 ∗ ownD W E2 ⊢ ⌜E1 ## E2⌝ := by
  letI E : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := W.disabled
  unfold ownD
  iintro ⟨H1, H2⟩
  icases iOwn_op (E := E) $$ [H1 H2] with H;
    isplitl [H1] <;> iassumption
  icases iOwn_cmraValid (E := E) $$ H with H
  icases internalCmraValid_discrete (PROP := IProp GF) (A := DisjointLeibnizSet PosSet) $$ H with %H
  ipure_intro
  exact valid_op_iff_disj.mp H

theorem ownD_op' (E1 E2 : PosSet) :
    ⌜E1 ## E2⌝ ∧ ownD W (E1 ∪ E2) ⊣⊢ ownD W E1 ∗ ownD W E2 := by
  constructor
  · iintro ⟨%Hdisj, H⟩
    iapply (ownD_op W E1 E2 Hdisj).mp $$ H
  · iintro ⟨H1, H2⟩
    ihave %Hdisj : ⌜E1 ## E2⌝ $$ [H1 H2]; iapply ownD_disjoint $$ [H1 H2]; isplitl [H1] <;> iassumption
    isplit
    · ipure_intro; assumption
    · iapply (ownD_op W E1 E2 Hdisj).mpr $$ [H1 H2]; isplitl [H1] <;> iassumption

theorem ownD_singleton_twice (i : Pos) :
    ownD W {i} ∗ ownD W {i} ⊢ False := by
  apply (ownD_disjoint W {i} {i}).trans
  apply BI.pure_mono
  intro h
  apply h i
  simp

end lemmas_ownD

section lemmas_operations

variable {GF : BundledGFunctors} (W : wsatGS GF)

open BI Iris PartialMap LawfulPartialMap BigSepM DFrac HeapView

theorem invariant_lookup (I : InvMap (IProp GF)) (i : Pos) (P : IProp GF) :
  haveI E : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := W.inv
  iOwn (E := E) W.invariant_name (Auth (own 1) (map toAgree (map invariant_unfold I)))
  ∗ ownI W i P ⊢ ∃ Q, ⌜get? I i = .some Q⌝ ∗ ▷ internalEq Q P := by
  letI E : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := W.inv
  unfold ownI
  iintro H; icases iOwn_cmraValid_op (E := E) $$ H with H
  icases (auth_op_frag_validI_total (F := PNat) (PROP := (IProp GF)) (own 1)
          (map toAgree (map invariant_unfold I))) $$ H
    with ⟨%v', %dp', %Hdp, %Hlookup, H1, H2⟩
  simp only [get?_map, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at Hlookup
  have ⟨Q', Hget, Hagree⟩ := Hlookup
  iexists Q'; isplit; ipure_intro; assumption
  rw [←Hagree]
  iapply later_equivI_mp; iapply internalEq.symm; iapply toAgree_includedI $$ H2

theorem ownI_open (i : Pos) (P : IProp GF) :
    wsat W ∗ ownI W i P ∗ ownE W {i} ⊢
    wsat W ∗ ▷ P ∗ ownD W {i} := by
    unfold wsat
    iintro ⟨⟨%I, Hown, Hmap⟩, #HI, HE⟩
    icases invariant_lookup W I i P $$ [Hown HI] with #⟨%Q, %HEQ, #H⟩; isplit <;> iassumption
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
    · iexfalso; iapply ownE_singleton_twice W i $$ [HE HE']; isplitl [HE] <;> iassumption

theorem ownI_close (i : Pos) (P : IProp GF) :
    wsat W ∗ ownI W i P ∗ ▷ P ∗ ownD W {i} ⊢
    wsat W ∗ ownE W {i} := by
  unfold wsat
  iintro ⟨⟨%I, Hown, Hmap⟩, #HI, HProp, HE⟩
  icases invariant_lookup W I i P $$ [Hown HI] with #⟨%Q, %HEQ, #H⟩; isplit <;> iassumption
  icases bigSepM_delete (PROP := IProp GF) HEQ $$ Hmap with ⟨⟨⟨HProp, HD⟩ | HE'⟩, Hacc⟩
  · iexfalso; iapply ownD_singleton_twice W i $$ [HD HE]; isplitl [HE] <;> iassumption
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

end lemmas_operations

section lemmas_allocation

variable {GF : BundledGFunctors} (W : wsatGS GF)

open BI HeapView BigSepM Std.PartialMap DisjointLeibnizSet LawfulPartialMap

-- TODO: wrong prec ==∗ and *
theorem ownI_alloc (φ : Pos → Prop) (P : IProp GF)
    (Hfresh : ∀ E : PosSet, ∃ i, i ∉ E ∧ φ i) :
    ⊢ (wsat W ∗ ▷ P) ==∗ ∃ i, ⌜φ i⌝ ∗ wsat W ∗ ownI W i P := by
  letI elem1 : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := W.inv
  letI elem2 : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := W.enabled
  letI elem3 : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := W.disabled
  unfold wsat ownI ownE
  iintro ⟨⟨%I, ⟨Hown, Hmap⟩⟩, HProp⟩
  imod ownD_empty (W := W) with HD; unfold ownD
  imod iOwn_updateP (E := elem3)
    (alloc_empty_updateP_strong' (fun i => (get? I i = .none) ∧ φ i) _) $$ HD with HD
  · intro Y
    have ⟨j, H⟩ := Hfresh (Y ∪ dom I)
    simp only [mem_union, not_or] at H
    obtain ⟨⟨HnotY, HnotDom⟩, Hφ⟩ := H
    simp only [mem_dom, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at HnotDom
    exists j
  · icases HD with ⟨%X, %H, HD⟩; obtain ⟨j, HEQ, ⟨Hget, Hφ⟩⟩ := H
    imod iOwn_update (E := elem1)
      (update_one_alloc (k := j) (dq := .discard)
        (m1 := map toAgree (map invariant_unfold I)) (v1 := toAgree (invariant_unfold P))
        _ DFrac.valid_discard  _) $$ Hown with Hown
    · simpa [get?_map]
    · simp [CMRA.Valid, Agree.valid, Agree.validN, toAgree]
    · icases iOwn_op (E := elem1) $$ Hown with ⟨Hown, Hpt⟩
      imodintro
      iexists j
      isplit; ipure_intro; assumption
      isplitr [Hpt]
      · iexists insert I j P
        isplitl [Hown]
        · rw [show Std.insert (map toAgree (map invariant_unfold I)) j (toAgree (invariant_unfold P))
            = map toAgree (map invariant_unfold (Std.insert I j P)) by
              apply ExtensionalPartialMap.equiv_iff_eq.mp
              intro k; simp only [get?_insert, get?_map, Option.map_map]
              by_cases h : j = k <;> simp [h]]
          iexact Hown
        · iapply bigSepM_insert (PROP := IProp GF) (x := P) Hget $$ [Hmap HProp HD]
          isplitl [HProp HD]
          · rw [HEQ]; ileft; isplitl [HProp] <;> iassumption
          · iexact Hmap
      · iexact Hpt

theorem ownI_alloc_open (φ : Pos → Prop) (P : IProp GF)
  (Hfresh : ∀ E : PosSet, ∃ i, i ∉ E ∧ φ i) :
  ⊢ wsat W ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE W {i} -∗ wsat W)
    ∗ ownI W i P ∗ ownD W {i} := by
  letI elem1 : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := W.inv
  letI elem2 : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := W.enabled
  letI elem3 : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := W.disabled
  unfold wsat
  iintro ⟨%I, Hown, Hmap⟩
  imod ownD_empty (W := W) with HD; unfold ownD
  imod iOwn_updateP (E := elem3)
    (alloc_empty_updateP_strong' (fun i => (get? I i = .none) ∧ φ i) _) $$ HD with HD
  · intro Y
    have ⟨j, H⟩ := Hfresh (Y ∪ dom I)
    simp only [mem_union, not_or] at H
    obtain ⟨⟨HnotY, HnotDom⟩, Hφ⟩ := H
    simp only [mem_dom, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at HnotDom
    exists j
  · icases HD with ⟨%X, %H, HD⟩; obtain ⟨j, HEQ, ⟨Hget, Hφ⟩⟩ := H
    imod iOwn_update (E := elem1)
      (update_one_alloc (k := j) (dq := .discard)
        (m1 := map toAgree (map invariant_unfold I)) (v1 := toAgree (invariant_unfold P))
        _ DFrac.valid_discard  _) $$ Hown with Hown
    · simpa [get?_map]
    · simp [CMRA.Valid, Agree.valid, Agree.validN, toAgree]
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

theorem wsat_alloc [WP : wsatGpreS GF] :
    ⊢ |==> ∃ (W : wsatGS GF), wsat W ∗ ownE W CoPset.full := by
  haveI elem1 : ElemG GF (HeapViewURF (AgreeRF (LaterOF (constOF (IProp GF))))) := WP.inv
  haveI elem2 : ElemG GF (constOF (DisjointLeibnizSet CoPset)) := WP.enabled
  haveI elem3 : ElemG GF (constOF (DisjointLeibnizSet PosSet)) := WP.disabled
  imod (iOwn_alloc (E := elem1) (Auth (.own 1) ∅)) with ⟨%γ, H⟩; apply auth_one_valid
  imod (iOwn_alloc (E := elem2) (valid CoPset.full)) with ⟨%γe, He⟩; exact ⟨⟩
  imod (iOwn_alloc (E := elem3) (valid ∅)) with ⟨%γd, Hd⟩; exact ⟨⟩
  imodintro
  let W : wsatGS GF := { inv := elem1, enabled := elem2, disabled := elem3,
                         invariant_name := γ, enabled_name := γe, disabled_name := γd }
  iexists W
  unfold wsat
  isplitr [He]
  · iexists ∅
    isplitl
    · iclear Hd; simp only [W]
      -- TODO: bad, abstraction-breaking defeq
      rw [show (map toAgree (map invariant_unfold ∅)) = ∅ by rfl]
      iassumption
    · iapply bigSepM_empty; simp
  · unfold ownE; iexact He

end lemmas_allocation

end Iris.BaseLogic.WSat
