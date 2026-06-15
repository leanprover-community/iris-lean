/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.Algebra.Lib.ExclAuth
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Instances.Lib.Invariants
public import Iris.Std.PartialMap
public import Iris.Std.Namespaces

@[expose] public section

namespace Iris

open BI CMRA Agree OFE UPred IProp Std ProofMode COFE Auth ExclAuth Excl PartialMap BigSepM

abbrev BoolO := LeibnizO Bool

variable (GF : BundledGFunctors)

abbrev BoxF : OFunctorPre :=
  ProdOF (AuthURF (OptionOF (ExclOF (constOF BoolO))))
    (OptionOF (AgreeRF (LaterOF (constOF (IProp GF)))))

@[rocq_alias boxG]
class BoxG where
  [elemG : ElemG GF (BoxF GF)]

attribute [reducible, instance] BoxG.elemG

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [BoxG GF]

@[rocq_alias slice_name]
abbrev SliceName := GName

@[rocq_alias box_own_auth]
def box_own_auth (γ : SliceName) (a : Auth (Option (Excl BoolO))) : IProp GF :=
  iOwn (F := BoxF GF) γ (a, none)

instance box_own_auth_timeless (γ : SliceName) (a : Auth (Option (Excl BoolO))) :
    BI.Timeless (box_own_auth (GF := GF) γ a) := by
  unfold box_own_auth
  have hd : OFE.DiscreteE ((a, none) : (BoxF GF).ap (IProp GF)) :=
    prod.is_discrete inferInstance Option.none_is_discrete
  exact iOwn_timeless (F := BoxF GF) (a := ((a, none) : (BoxF GF).ap (IProp GF)))

@[rocq_alias box_own_prop]
def box_own_prop (γ : SliceName) (P : IProp GF) : IProp GF :=
  iOwn (F := BoxF GF) γ (UCMRA.unit, some (toAgree (Later.next P)))

instance box_own_prop_persistent (γ : SliceName) (P : IProp GF) :
    Persistent (box_own_prop γ P) := by
  unfold box_own_prop
  infer_instance

@[rocq_alias box_own_prop_ne]
instance box_own_prop_ne (γ : SliceName) : NonExpansive (box_own_prop (GF := GF) γ) := by
  constructor
  intro n P Q h
  unfold box_own_prop
  apply iOwn_ne.ne
  apply dist_prod_ext
  · exact Dist.rfl
  · exact toAgree.ne.ne (NextContractive.distLater_dist h.distLater)

@[rocq_alias box_own_prop_contractive]
instance box_own_prop_contractive (γ : SliceName) : Contractive (box_own_prop (GF := GF) γ) := by
  constructor
  intro n P Q h
  unfold box_own_prop
  apply iOwn_ne.ne
  apply dist_prod_ext
  · exact Dist.rfl
  · exact toAgree.ne.ne (NextContractive.distLater_dist h)

@[rocq_alias slice_inv]
def slice_inv (γ : SliceName) (P : IProp GF) : IProp GF :=
  iprop(∃ b : Bool, box_own_auth γ (●E (⟨b⟩ : BoolO)) ∗ if b then P else True)

@[rocq_alias slice]
def slice (N : Namespace) (γ : SliceName) (P : IProp GF) : IProp GF :=
  iprop(box_own_prop γ P ∗ inv N (slice_inv γ P))

@[rocq_alias box]
def box {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (N : Namespace) (f : M Bool) (P : IProp GF) : IProp GF :=
  iprop(∃ Φ : SliceName → IProp GF,
    ▷ internalEq P ([∗map] γ ↦ _x ∈ f, Φ γ) ∗
    [∗map] γ ↦ b ∈ f, box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
                       inv N (slice_inv γ (Φ γ)))

@[rocq_alias box_inv_ne]
instance slice_inv_ne (γ : SliceName) : NonExpansive (slice_inv (GF := GF) γ) := by
  constructor
  intro n P Q h
  unfold slice_inv
  apply exists_ne
  intro b
  apply sep_ne.ne Dist.rfl
  cases b
  · exact Dist.rfl
  · exact h

@[rocq_alias slice_ne]
instance slice_ne (N : Namespace) (γ : SliceName) : NonExpansive (slice (GF := GF) N γ) := by
  constructor
  intro n P Q h
  unfold slice
  apply sep_ne.ne
  · exact (box_own_prop_ne γ).ne h
  · exact (inv_ne N).ne ((slice_inv_ne γ).ne h)

@[rocq_alias slice_contractive]
instance slice_contractive (N : Namespace) (γ : SliceName) : Contractive (slice (GF := GF) N γ) where
  distLater_dist {n P Q} h := by
    unfold slice
    apply sep_ne.ne
    · exact (box_own_prop_contractive γ).distLater_dist h
    · exact (inv_contractive N).distLater_dist (fun m hm => (slice_inv_ne γ).ne (h m hm))

@[rocq_alias slice_persistent]
instance slice_persistent (N : Namespace) (γ : SliceName) (P : IProp GF) :
    Persistent (slice N γ P) := by
  unfold slice
  infer_instance

@[rocq_alias box_contractive]
instance box_contractive {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (N : Namespace) (f : M Bool) : Contractive (box (GF := GF) N f) where
  distLater_dist {n P Q} h := by
    unfold box
    apply exists_ne
    intro Φ
    apply sep_ne.ne _ Dist.rfl
    apply Contractive.distLater_dist
    intro m hm
    exact (internalEq.ne_l _).ne (h m hm)

@[rocq_alias box_ne]
instance box_ne {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (N : Namespace) (f : M Bool) : NonExpansive (box (GF := GF) N f) :=
  ne_of_contractive _

@[rocq_alias box_own_auth_agree]
theorem box_own_auth_agree (γ : SliceName) (b1 b2 : Bool) :
    box_own_auth (GF := GF) γ (●E (⟨b1⟩ : BoolO)) ∗ box_own_auth γ (◯E ⟨b2⟩) ⊢ ⌜b1 = b2⌝ := by
  unfold box_own_auth
  iintro ⟨H1, H2⟩
  icases iOwn_op $$ [$H1 $H2] with H
  icases iOwn_cmraValid $$ H with H
  icases (internalCmraValid_entails.mpr fun n h => Prod.validN_fst h) $$ H with %H
  ipureintro
  exact LeibnizO.eqv_inj $ Iris.ExclAuth.agree_L H

@[rocq_alias box_own_auth_update]
theorem box_own_auth_update (γ : SliceName) (b1 b2 b3 : Bool) :
    box_own_auth (GF := GF) γ (●E (⟨b1⟩ : BoolO)) ∗ box_own_auth γ (◯E ⟨b2⟩) ⊢
    |==> (box_own_auth γ (●E ⟨b3⟩) ∗ box_own_auth γ (◯E ⟨b3⟩)) := by
  unfold box_own_auth
  iintro ⟨H1, H2⟩
  icases iOwn_op $$ [$H1 $H2] with H
  iapply bupd_mono iOwn_op.mp
  iapply iOwn_update (Update.prod _ ExclAuth.update (Update.id (x := none))) $$ H

@[rocq_alias box_own_agree]
theorem box_own_agree (γ : SliceName) (Q1 Q2 : IProp GF) :
    box_own_prop γ Q1 ∗ box_own_prop γ Q2 ⊢ ▷ internalEq Q1 Q2 := by
  unfold box_own_prop
  iintro ⟨H1, H2⟩
  icases iOwn_op $$ [$H1 $H2] with H
  icases iOwn_cmraValid $$ H with H
  icases (internalCmraValid_entails.mpr fun n h => Prod.validN_snd h) $$ H with H
  icases option_validI.mp $$ H with H
  dsimp only [CMRA.op, optionOp, Option.elim_some]
  icases agree_op_invI $$ H with H
  icases (agree_equivI _ _).mp $$ H with H
  inext
  itrivial

@[rocq_alias box_alloc]
theorem box_alloc {M : Type _ → Type _} [LawfulFiniteMap M SliceName] (N : Namespace) :
    ⊢ box (GF := GF) N (∅ : M Bool) iprop(emp) := by
  simp only [box]
  iexists (fun _ => iprop(True))
  isplit
  · inext; simp only [Algebra.BigOpM.bigOpM_empty]; itrivial
  · simp

@[rocq_alias slice_insert_empty]
theorem slice_insert_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (Q P : IProp GF) (N : Namespace) :
    (▷?q box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? f γ = none⌝ ∗
      slice N γ Q ∗ ▷?q box N (insert f γ false) iprop(Q ∗ P) := by
  unfold box
  iintro ⟨%Φ, #Heq, H⟩
  imod (iOwn_alloc_cofinite (F := BoxF GF)
      ((((●E (⟨false⟩ : BoolO)), none) • ((◯E (⟨false⟩ : BoolO)), none)) •
        (UCMRA.unit, some (toAgree (Later.next Q))))
      ((toList f).map Prod.fst) _) with ⟨%γ, %Hγ, Hown⟩
  · exact ⟨ExclAuth.valid, Agree.toAgree_valid⟩
  have hfresh : get? f γ = none := by
    rcases h : get? f γ with _ | v
    · rfl
    · exact absurd (List.mem_map_of_mem (toList_get.mpr h)) Hγ
  icases iOwn_op $$ Hown with ⟨⟨Hauth, Hfrag⟩, #Hprop⟩
  imod inv_alloc N E (slice_inv γ Q) $$ [Hauth] with #Hinv
  · inext
    simp only [slice_inv, box_own_auth]
    iexists false
    simp only [Bool.false_eq_true, if_false]
    iframe
  imodintro
  iexists γ
  iframe %hfresh
  simp only [slice, box_own_prop]
  iframe Hprop Hinv
  iexists (fun γ'' => if γ'' = γ then Q else Φ γ'')
  simp only [BIBase.laterIf]
  inext
  isplitl [Heq]
  · inext
    irewrite [Heq]
    · refine ⟨fun _ _ _ H => ?_⟩
      refine (NonExpansive₂.ne_left internalEq _).ne ?_
      exact (sep_ne.ne_right _ _).ne H
    rw [(bigSepM_insert hfresh).to_eq]
    simp only [↓reduceIte]
    iclear Heq Hprop Hinv
    iapply prop_ext
    imodintro
    isplit
    · iintro ⟨$, H⟩
      iapply bigSepM_mono $$ H
      intro k v hk
      rw [if_neg]
      exact .rfl
      rintro rfl; rw [hfresh] at hk; simp at hk
    · iintro ⟨$, H⟩
      iapply bigSepM_mono $$ H
      intro k v hk
      rw [if_neg]
      exact .rfl
      rintro rfl; rw [hfresh] at hk; simp at hk
  · iapply (bigSepM_insert hfresh).mpr
    isplitl [Hfrag Hprop Hinv]
    · simp only [box_own_auth, ↓reduceIte]
      iframe Hinv Hprop Hfrag
    · iapply bigSepM_mono $$ H
      intro k v hk
      rw [if_neg]
      exact .rfl
      rintro rfl; rw [hfresh] at hk; simp at hk

@[rocq_alias slice_delete_empty]
theorem slice_delete_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q : IProp GF)
    (γ : SliceName) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some false →
    slice N γ Q ∗ ▷?q box N f P ⊢
    |={E}=> ∃ P', ▷?q (▷ internalEq P iprop(Q ∗ P')) ∗ ▷?q (box N (delete f γ) P') := by
  intro HE Hf
  unfold slice box
  iintro ⟨⟨#Hprop, #Hinv⟩, %Φ, #Heq, Hbig⟩
  simp only [BIBase.laterIf]
  icases bigSepM_laterN (n := q.toNat) $$ Hbig with Hbig
  icases bigSepM_delete Hf $$ Hbig with ⟨⟨Hfrag, #Hprop', #Hsliceinv⟩, Hbig⟩
  iexists iprop([∗map] γ' ↦ _x ∈ delete f γ, Φ γ')
  imodintro
  iapply laterN_sep
  icases bigSepM_laterN $$ Hbig with Hbig
  inext
  ihave #Heq' := (box_own_agree γ Q (Φ γ)) $$ [$Hprop $Hprop']
  isplit
  · inext
    irewrite [Heq']
    · refine ⟨fun _ _ _ H => ?_⟩
      refine (NonExpansive₂.ne_right internalEq P).ne ?_
      exact (sep_ne.ne_left _ _).ne H
    irewrite [Heq]
    · refine ⟨fun _ _ _ H => ?_⟩
      exact (NonExpansive₂.ne_left internalEq _).ne H
    iapply prop_ext
    iclear Hprop Hinv Hprop' Hsliceinv
    imodintro
    iapply bigSepM_delete (Φ := fun k _ => Φ k) Hf
  · iexists Φ; iframe; itrivial

@[rocq_alias slice_fill]
theorem slice_fill {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (γ : SliceName)
    (P Q : IProp GF) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some false →
    slice N γ Q ∗ ▷ Q ∗ ▷?q box N f P ⊢
    |={E}=> ▷?q box N (insert f γ true) P := by
  intro HE Hf
  unfold slice box
  iintro ⟨⟨#Hprop, #Hinv⟩, HQ, %Φ, #Heq, Hbig⟩
  simp only [BIBase.laterIf]
  icases bigSepM_laterN (n := q.toNat) $$ Hbig with Hbig
  icases bigSepM_delete Hf $$ Hbig with ⟨⟨Hfrag, Hprop', Hsliceinv⟩, Hbig⟩
  have hq : q.toNat ≤ 1 := by cases q <;> simp
  ihave Hfrag := (laterN_le (P := box_own_auth γ (◯E (⟨false⟩ : BoolO))) hq).trans
    ((laterN_later 0).trans laterN_0).1 $$ Hfrag
  imod inv_acc E N (slice_inv γ Q) HE $$ Hinv with ⟨Hsinv, Hclose⟩
  simp only [slice_inv]
  icases Hsinv with ⟨%b, >Hauth, Hb⟩
  icases Hfrag with >Hfrag
  imod box_own_auth_update γ b false true $$ [$Hauth $Hfrag] with ⟨Hauth, Hfrag⟩
  imod Hclose $$ [Hauth HQ]
  · inext; iexists true; simp only [if_true]; iframe
  imodintro
  icases bigSepM_laterN $$ Hbig with Hbig
  inext
  iexists Φ
  rewrite [((bigSepM_insert_delete (Φ := fun k _ => Φ k)).trans (bigSepM_delete (Φ := fun k _ => Φ k) Hf).symm).to_eq]
  iframe Heq
  iapply bigSepM_insert_delete.mpr
  iframe

@[rocq_alias slice_empty]
theorem slice_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q : IProp GF)
    (γ : SliceName) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some true →
    slice N γ Q ∗ ▷?q box N f P ⊢
    |={E}=> ▷ Q ∗ (▷?q box N (insert f γ false) P) := by
  intro HE Hf
  unfold slice box
  iintro ⟨⟨#Hprop, #Hinv⟩, %Φ, #Heq, Hbig⟩
  simp only [BIBase.laterIf]
  icases bigSepM_laterN (n := q.toNat) $$ Hbig with Hbig
  icases bigSepM_delete Hf $$ Hbig with ⟨⟨Hfrag, Hprop', Hsliceinv⟩, Hbig⟩
  have hq : q.toNat ≤ 1 := by cases q <;> simp
  ihave Hfrag := (laterN_le (P := box_own_auth γ (◯E (⟨true⟩ : BoolO))) hq).trans
    ((laterN_later 0).trans laterN_0).1 $$ Hfrag
  imod inv_acc E N (slice_inv γ Q) HE $$ Hinv with ⟨Hsinv, Hclose⟩
  simp only [slice_inv]
  icases Hsinv with ⟨%b, >Hauth, Hb⟩
  icases Hfrag with >Hfrag
  ihave %hb := box_own_auth_agree γ b true $$ [$Hauth $Hfrag]
  subst hb
  simp only [if_true]
  imod box_own_auth_update γ true true false $$ [$Hauth $Hfrag] with ⟨Hauth, Hfrag⟩
  imod Hclose $$ [Hauth]
  · inext; iexists false; simp only [Bool.false_eq_true, if_false]; iframe
  imodintro
  iframe Hb
  iexists Φ
  icases bigSepM_laterN $$ Hbig with Hbig
  inext
  rw [((bigSepM_insert_delete (Φ := fun k _ => Φ k)).trans (bigSepM_delete (Φ := fun k _ => Φ k) Hf).symm).to_eq]
  iframe Heq
  iapply bigSepM_insert_delete.mpr
  iframe

@[rocq_alias slice_insert_full]
theorem slice_insert_full {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q : IProp GF) (N : Namespace) :
    ↑N ⊆ E →
    ▷ Q ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? f γ = none⌝ ∗
      slice N γ Q ∗ (▷?q box N (insert f γ true) iprop(Q ∗ P)) := by
  intro HE
  unfold box
  iintro ⟨HQ, %Φ, #Heq, H⟩
  have hv : ✓ (((●E (⟨true⟩ : BoolO)) • (◯E (⟨true⟩ : BoolO)), some (toAgree (Later.next Q)))
      : (BoxF GF).ap (IProp GF)) := ⟨ExclAuth.valid, Agree.toAgree_valid⟩
  imod (iOwn_alloc_cofinite (F := BoxF GF)
      (((●E (⟨true⟩ : BoolO)) • (◯E (⟨true⟩ : BoolO)), some (toAgree (Later.next Q)))
        : (BoxF GF).ap (IProp GF)) ((toList f).map Prod.fst) hv) with ⟨%γ, %Hγ, Hown⟩
  have hfresh : get? f γ = none := by
    rcases h : get? f γ with _ | v
    · rfl
    · exact absurd (List.mem_map_of_mem (f := Prod.fst) (toList_get.mpr h)) Hγ
  have heqv : (((●E (⟨true⟩ : BoolO)) • (◯E (⟨true⟩ : BoolO)), some (toAgree (Later.next Q)))
      : (BoxF GF).ap (IProp GF)) ≡
      (((●E (⟨true⟩ : BoolO)), none) • ((◯E (⟨true⟩ : BoolO)), none)) •
        (UCMRA.unit, some (toAgree (Later.next Q))) := by
    constructor <;> simp [CMRA.op] <;> rfl
  ihave Hown := (equiv_iff.mp ((iOwn_ne (F := BoxF GF) (τ := γ)).eqv heqv)).1 $$ Hown
  icases iOwn_op $$ Hown with ⟨Hauth_frag, #Hprop⟩
  icases iOwn_op $$ Hauth_frag with ⟨Hauth, Hfrag⟩
  imod (inv_alloc N E (slice_inv γ Q)) $$ [Hauth HQ] with #Hinv
  · inext
    simp only [slice_inv, box_own_auth]
    iexists true
    simp only [if_true]
    isplitl [Hauth]
    · iexact Hauth
    · iassumption
  imodintro
  iexists γ
  isplit
  · ipureintro; exact hfresh
  isplitl [Hprop]
  · simp only [slice, box_own_prop]
    isplitl [Hprop]
    · iexact Hprop
    · iexact Hinv
  let Φ' : SliceName → IProp GF := fun γ'' => if γ'' = γ then Q else Φ γ''
  have hΦ'γ : Φ' γ = Q := by simp only [Φ', if_pos rfl]
  have hΦ'f : ∀ k v, get? f k = some v → Φ' k = Φ k := by
    intro k v hk; simp only [Φ']; rw [if_neg]; rintro rfl; rw [hfresh] at hk; simp at hk
  have hmapf : (iprop([∗map] k ↦ _x ∈ f, Φ' k) : IProp GF) ⊣⊢ [∗map] k ↦ _x ∈ f, Φ k :=
    ⟨bigSepM_mono (Φ := fun k _ => Φ' k) (Ψ := fun k _ => Φ k)
        (fun {k v} hk => by show Φ' k ⊢ Φ k; rw [hΦ'f k v hk]; exact .rfl),
     bigSepM_mono (Φ := fun k _ => Φ k) (Ψ := fun k _ => Φ' k)
        (fun {k v} hk => by show Φ k ⊢ Φ' k; rw [hΦ'f k v hk]; exact .rfl)⟩
  have hmap : (iprop([∗map] k ↦ _x ∈ insert f γ true, Φ' k) : IProp GF) ⊣⊢
      Q ∗ [∗map] k ↦ _x ∈ f, Φ k :=
    (bigSepM_insert (Φ := fun k _ => Φ' k) hfresh).trans
      (sep_congr (hΦ'γ ▸ BIBase.BiEntails.rfl) hmapf)
  simp only [BIBase.laterIf]
  iexists Φ'
  iapply (laterN_sep q.toNat).mpr
  isplitl [Heq]
  · have hcong : (iprop(internalEq P ([∗map] k ↦ _x ∈ f, Φ k)) : IProp GF) ⊢
        internalEq iprop(Q ∗ P) ([∗map] k ↦ _x ∈ insert f γ true, Φ' k) := by
      letI : NonExpansive (fun B : IProp GF => iprop(Q ∗ B)) :=
        NonExpansive₂.ne_right BIBase.sep Q
      exact (internalEq.of_internalEquiv_ne (PROP := IProp GF) (fun B => iprop(Q ∗ B))).trans
        (equiv_iff.mp ((internalEq.ne_r iprop(Q ∗ P)).eqv (equiv_iff.mpr hmap.symm))).1
    iapply laterN_mono q.toNat (later_mono hcong) $$ Heq
  · ihave Hfrag := laterN_intro q.toNat $$ Hfrag
    ihave Hprop := laterN_intro q.toNat $$ Hprop
    ihave Hinv := laterN_intro q.toNat $$ Hinv
    iapply bigSepM_laterN.mpr
    iapply (bigSepM_insert (Φ := fun k v => iprop(▷^[q.toNat] (box_own_auth k (◯E (⟨v⟩ : BoolO)) ∗
        box_own_prop k (Φ' k) ∗ inv N (slice_inv k (Φ' k))))) hfresh).mpr
    isplitl [Hfrag Hprop Hinv]
    · rw [hΦ'γ]
      iapply (laterN_sep q.toNat).mpr
      isplitl [Hfrag]
      · simp only [box_own_auth]; iexact Hfrag
      · iapply (laterN_sep q.toNat).mpr
        isplitl [Hprop]
        · simp only [box_own_prop]; iexact Hprop
        · iexact Hinv
    · iapply (bigSepM_laterN (Φ := fun k v => iprop(box_own_auth k (◯E (⟨v⟩ : BoolO)) ∗
        box_own_prop k (Φ' k) ∗ inv N (slice_inv k (Φ' k)))) (n := q.toNat)).mp
      iapply laterN_mono q.toNat _ $$ H
      iapply bigSepM_mono (Φ := fun k v => iprop(box_own_auth k (◯E (⟨v⟩ : BoolO)) ∗
        box_own_prop k (Φ k) ∗ inv N (slice_inv k (Φ k))))
      intro k v hk
      rw [← hΦ'f k v hk]
      exact .rfl

@[rocq_alias slice_delete_full]
theorem slice_delete_full {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q : IProp GF)
    (γ : SliceName) (N : Namespace) :
    ↑N ⊆ E →
    PartialMap.get? f γ = some true →
    slice N γ Q ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ P', ▷ Q ∗
      (▷?q ▷ internalEq P iprop(Q ∗ P')) ∗ (▷?q box N (delete f γ) P') := by
  intro HE Hf
  unfold slice box
  iintro ⟨⟨#Hprop, #Hinv⟩, %Φ, #Heq, Hbig⟩
  simp only [BIBase.laterIf]
  icases bigSepM_laterN (n := q.toNat) $$ Hbig with Hbig
  icases bigSepM_delete Hf $$ Hbig with ⟨⟨Hfrag, #Hprop', #Hsliceinv⟩, Hbig⟩
  have hq : q.toNat ≤ 1 := by cases q <;> simp
  ihave Hfrag := (laterN_le (P := box_own_auth γ (◯E (⟨true⟩ : BoolO))) hq).trans
    ((laterN_later 0).trans laterN_0).1 $$ Hfrag
  ihave HpropQ := laterN_intro q.toNat (P := box_own_prop γ Q) $$ Hprop
  ihave #Heq' := (laterN_sep q.toNat).mpr.trans
    (laterN_mono q.toNat (box_own_agree γ Q (Φ γ))) $$ [HpropQ Hprop']
  · isplitl [HpropQ] <;> iassumption
  imod inv_acc E N (slice_inv γ Q) HE $$ Hinv with ⟨Hsinv, Hclose⟩
  simp only [slice_inv]
  icases Hsinv with ⟨%b, >Hauth, Hb⟩
  icases Hfrag with >Hfrag
  ihave %hb := box_own_auth_agree γ b true $$ [Hauth Hfrag]
  · isplitl [Hauth] <;> iassumption
  subst hb
  simp only [if_true]
  imod box_own_auth_update γ true true false $$ [Hauth Hfrag] with ⟨Hauth, Hfrag⟩
  · isplitl [Hauth] <;> iassumption
  imod Hclose $$ [Hauth]
  · inext; iexists false; simp only [Bool.false_eq_true, if_false]
    isplitl [Hauth] <;> itrivial
  have hbd : (iprop([∗map] γ' ↦ _x ∈ f, Φ γ') : IProp GF) ⊣⊢
      Φ γ ∗ [∗map] γ' ↦ _x ∈ delete f γ, Φ γ' := bigSepM_delete (Φ := fun k _ => Φ k) Hf
  iexists iprop([∗map] γ' ↦ _x ∈ delete f γ, Φ γ')
  iapply fupd_intro
  isplitl [Hb]
  · iassumption
  isplitl [Heq Heq']
  · icombine Heq Heq' as Hc
    have hcong : (iprop(internalEq P ([∗map] γ' ↦ _x ∈ f, Φ γ') ∗
          internalEq Q (Φ γ)) : IProp GF) ⊢
        internalEq P iprop(Q ∗ [∗map] γ' ↦ _x ∈ delete f γ, Φ γ') := by
      letI : NonExpansive (fun B : IProp GF => iprop(B ∗ [∗map] γ' ↦ _x ∈ delete f γ, Φ γ')) :=
        NonExpansive₂.ne_left BIBase.sep _
      have hsep : (iprop(internalEq Q (Φ γ)) : IProp GF) ⊢
          internalEq iprop(Q ∗ [∗map] γ' ↦ _x ∈ delete f γ, Φ γ')
            iprop(Φ γ ∗ [∗map] γ' ↦ _x ∈ delete f γ, Φ γ') :=
        internalEq.of_internalEquiv_ne (PROP := IProp GF)
          (fun B => iprop(B ∗ [∗map] γ' ↦ _x ∈ delete f γ, Φ γ'))
      have hP : (iprop(internalEq P ([∗map] γ' ↦ _x ∈ f, Φ γ')) : IProp GF) ⊢
          internalEq P iprop(Φ γ ∗ [∗map] γ' ↦ _x ∈ delete f γ, Φ γ') :=
        (equiv_iff.mp ((internalEq.ne_r P).eqv (equiv_iff.mpr hbd))).1
      iintro ⟨H1, H2⟩
      iapply internalEq.trans
      isplitl [H1]
      · iapply hP $$ H1
      · iapply internalEq.symm
        iapply hsep $$ H2
    iapply laterN_mono q.toNat (later_mono hcong) $$ Hc
  · iclear Hfrag
    iexists Φ
    iapply (laterN_sep q.toNat).mpr
    isplitl []
    · inext
      inext
      itrivial
    · iapply bigSepM_laterN (n := q.toNat).mpr $$ Hbig

theorem box_empty_aux {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (N : Namespace) (Φ : SliceName → IProp GF) (HE : ↑N ⊆ E) :
    ∀ f : M Bool, all (fun _ b => b = true) f →
    ([∗map] γ ↦ b ∈ f, box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ))) ⊢
    |={E}=> (▷ [∗map] γ ↦ _x ∈ f, Φ γ) ∗
      ([∗map] γ ↦ _b ∈ f, box_own_auth γ (◯E (⟨false⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ))) := by
  refine LawfulFiniteMap.induction_on (P := fun f => all (fun _ b => b = true) f →
    ([∗map] γ ↦ b ∈ f, box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ))) ⊢
    |={E}=> (▷ [∗map] γ ↦ _x ∈ f, Φ γ) ∗
      ([∗map] γ ↦ _b ∈ f, box_own_auth γ (◯E (⟨false⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ)))) ?_ ?_ ?_
  · intro m₁ m₂ heqv ih hall
    have hall₁ : all (fun _ b => b = true) m₁ := fun k v hk => hall k v ((heqv k) ▸ hk)
    refine (bigSepM_eqv_of_perm heqv).2.trans ((ih hall₁).trans ?_)
    apply BIFUpdate.mono
    exact sep_mono (later_mono (bigSepM_eqv_of_perm heqv).1) (bigSepM_eqv_of_perm heqv).1
  · intro _
    simp only [Algebra.BigOpM.bigOpM_empty]
    iintro _
    iapply fupd_intro
    isplitl []
    · inext; itrivial
    · itrivial
  · intro i x m hi ih hall
    have hx : x = true := LawfulPartialMap.all_insert_of_all (fun _ b => b = true) hall
    subst hx
    have hall' : all (fun _ b => b = true) m :=
      LawfulPartialMap.all_of_all_insert (fun _ b => b = true) hi hall
    refine (bigSepM_insert (Φ := fun γ b => iprop(box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗
      box_own_prop γ (Φ γ) ∗ inv N (slice_inv γ (Φ γ)))) hi).1.trans ?_
    iintro ⟨⟨Hfrag, #Hprop', #Hsliceinv⟩, Hbig⟩
    imod inv_acc E N (slice_inv i (Φ i)) HE $$ Hsliceinv with ⟨Hsinv, Hclose⟩
    simp only [slice_inv]
    icases Hsinv with ⟨%b, >Hauth, Hb⟩
    ihave %hb := box_own_auth_agree i b true $$ [Hauth Hfrag]
    · isplitl [Hauth] <;> iassumption
    subst hb
    simp only [if_true]
    imod box_own_auth_update i true true false $$ [Hauth Hfrag] with ⟨Hauth, Hfrag⟩
    · isplitl [Hauth] <;> iassumption
    imod Hclose $$ [Hauth]
    · inext; iexists false; simp only [Bool.false_eq_true, if_false]
      isplitl [Hauth] <;> itrivial
    imod ih hall' $$ [Hbig] with ⟨Hrest, Hbigrest⟩
    · simp only [slice_inv]; iexact Hbig
    imodintro
    simp only [slice_inv]
    isplitl [Hb Hrest]
    · iapply (later_congr (bigSepM_insert (Φ := fun γ _x => Φ γ) hi)).mpr
      iapply later_sep.mpr
      isplitl [Hb] <;> iassumption
    · iapply (bigSepM_insert (Φ := fun γ _b => iprop(box_own_auth γ (◯E (⟨false⟩ : BoolO)) ∗
        box_own_prop γ (Φ γ) ∗ inv N iprop(∃ b, box_own_auth γ (●E (⟨b⟩ : BoolO)) ∗
          if b = true then Φ γ else True))) hi).mpr
      isplitl [Hfrag Hprop' Hsliceinv]
      · isplitl [Hfrag]
        · iassumption
        · isplitl [Hprop'] <;> iassumption
      · iassumption

theorem box_fill_aux {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (N : Namespace) (Φ : SliceName → IProp GF) (HE : ↑N ⊆ E) :
    ∀ f : M Bool,
    (▷ [∗map] γ ↦ _x ∈ f, Φ γ) ∗
      ([∗map] γ ↦ b ∈ f, box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ))) ⊢
    |={E}=> [∗map] γ ↦ _b ∈ f, box_own_auth γ (◯E (⟨true⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ)) := by
  refine LawfulFiniteMap.induction_on (P := fun f =>
    (▷ [∗map] γ ↦ _x ∈ f, Φ γ) ∗
      ([∗map] γ ↦ b ∈ f, box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ))) ⊢
    |={E}=> [∗map] γ ↦ _b ∈ f, box_own_auth γ (◯E (⟨true⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ))) ?_ ?_ ?_
  · intro m₁ m₂ heqv ih
    refine (sep_mono (later_mono (bigSepM_eqv_of_perm heqv).2)
      (bigSepM_eqv_of_perm heqv).2).trans (ih.trans ?_)
    exact BIFUpdate.mono (bigSepM_eqv_of_perm heqv).1
  · simp only [Algebra.BigOpM.bigOpM_empty]
    iintro _
    iapply fupd_intro
    itrivial
  · intro i x m hi ih
    refine (sep_mono (later_mono (bigSepM_insert (Φ := fun γ _x => Φ γ) hi).1)
      (bigSepM_insert (Φ := fun γ b => iprop(box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗
        box_own_prop γ (Φ γ) ∗ inv N (slice_inv γ (Φ γ)))) hi).1).trans ?_
    iintro ⟨Hbody, ⟨Hfrag, #Hprop', #Hsliceinv⟩, Hbig⟩
    icases later_sep.mp $$ Hbody with ⟨HΦi, Hbodyrest⟩
    imod inv_acc E N (slice_inv i (Φ i)) HE $$ Hsliceinv with ⟨Hsinv, Hclose⟩
    simp only [slice_inv]
    icases Hsinv with ⟨%b, >Hauth, Hb⟩
    imod box_own_auth_update i b x true $$ [Hauth Hfrag] with ⟨Hauth, Hfrag⟩
    · isplitl [Hauth] <;> iassumption
    imod Hclose $$ [Hauth HΦi]
    · inext; iexists true; simp only [if_true]; isplitl [Hauth] <;> iassumption
    imod ih $$ [Hbodyrest Hbig] with Hbigrest
    · simp only [slice_inv]; isplitl [Hbodyrest] <;> iassumption
    imodintro
    simp only [slice_inv]
    iapply (bigSepM_insert (Φ := fun γ _b => iprop(box_own_auth γ (◯E (⟨true⟩ : BoolO)) ∗
        box_own_prop γ (Φ γ) ∗ inv N iprop(∃ b, box_own_auth γ (●E (⟨b⟩ : BoolO)) ∗
          if b = true then Φ γ else True))) hi).mpr
    isplitl [Hfrag Hprop' Hsliceinv]
    · isplitl [Hfrag]
      · iassumption
      · isplitl [Hprop'] <;> iassumption
    · iassumption

@[rocq_alias box_fill]
theorem box_fill {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (f : M Bool) (P : IProp GF) (N : Namespace) :
    ↑N ⊆ E →
    box N f P ∗ ▷ P ⊢ |={E}=> box N (map _ (fun _ => true) f) P := by
  intro HE
  unfold box
  iintro ⟨⟨%Φ, #Heq, Hbig⟩, HP⟩
  letI : NonExpansive (fun X : IProp GF => X) := ⟨fun _ _ _ h => h⟩
  have hbody : (iprop(internalEq P ([∗map] γ ↦ _x ∈ f, Φ γ) ∗ P) : IProp GF) ⊢
      [∗map] γ ↦ _x ∈ f, Φ γ :=
    internalEq.rewrite' (a := P) (b := iprop([∗map] γ ↦ _x ∈ f, Φ γ))
      (fun X => X) sep_elim_left sep_elim_right
  icombine Heq HP as Hc
  ihave Hbody := later_mono hbody $$ Hc
  imod box_fill_aux E N Φ HE f $$ [Hbody Hbig] with Hres
  · isplitl [Hbody] <;> iassumption
  imodintro
  have hmapres : (iprop([∗map] γ ↦ b ∈ map _ (fun _ => true) f,
        box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
          inv N (slice_inv γ (Φ γ))) : IProp GF) ⊣⊢
      [∗map] γ ↦ _b ∈ f, box_own_auth γ (◯E (⟨true⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ)) :=
    equiv_iff.mp (bigSepM_map (Φ := fun γ b => (iprop(box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗
      box_own_prop γ (Φ γ) ∗ inv N (slice_inv γ (Φ γ))) : IProp GF)))
  have hmapeq : (iprop([∗map] γ ↦ _x ∈ f, Φ γ) : IProp GF) ⊣⊢
      [∗map] γ ↦ _x ∈ map _ (fun _ => true) f, Φ γ :=
    (equiv_iff.mp (bigSepM_map (Φ := fun γ _b => Φ γ) (f := (fun _ => true)))).symm
  have hcong : (iprop(internalEq P ([∗map] γ ↦ _x ∈ f, Φ γ)) : IProp GF) ⊢
      internalEq P ([∗map] γ ↦ _x ∈ map _ (fun _ => true) f, Φ γ) :=
    (equiv_iff.mp ((internalEq.ne_r P).eqv (equiv_iff.mpr hmapeq))).1
  iexists Φ
  isplitl [Heq]
  · iapply later_mono hcong $$ Heq
  · iapply hmapres.mpr $$ Hres

@[rocq_alias box_empty]
theorem box_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (f : M Bool) (P : IProp GF) (N : Namespace) :
    ↑N ⊆ E →
    all (fun _ b => b = true) f →
    box N f P ⊢ |={E}=> ▷ P ∗ box N (map _ (fun _ => false) f) P := by
  intro HE Hall
  unfold box
  iintro ⟨%Φ, #Heq, Hbig⟩
  imod box_empty_aux E N Φ HE f Hall $$ [Hbig] with ⟨Hbody, Hres⟩
  · iexact Hbig
  imodintro
  have hmapres : (iprop([∗map] γ ↦ b ∈ map _ (fun _ => false) f,
        box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
          inv N (slice_inv γ (Φ γ))) : IProp GF) ⊣⊢
      [∗map] γ ↦ _b ∈ f, box_own_auth γ (◯E (⟨false⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
        inv N (slice_inv γ (Φ γ)) :=
    equiv_iff.mp (bigSepM_map (Φ := fun γ b => (iprop(box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗
      box_own_prop γ (Φ γ) ∗ inv N (slice_inv γ (Φ γ))) : IProp GF)))
  have hmapeq : (iprop([∗map] γ ↦ _x ∈ f, Φ γ) : IProp GF) ⊣⊢
      [∗map] γ ↦ _x ∈ map _ (fun _ => false) f, Φ γ :=
    (equiv_iff.mp (bigSepM_map (Φ := fun γ _b => Φ γ) (f := (fun _ => false)))).symm
  letI : NonExpansive (fun X : IProp GF => X) := ⟨fun _ _ _ h => h⟩
  have hrecover : (iprop(internalEq P ([∗map] γ ↦ _x ∈ f, Φ γ) ∗
      [∗map] γ ↦ _x ∈ f, Φ γ) : IProp GF) ⊢ P :=
    internalEq.rewrite' (a := iprop([∗map] γ ↦ _x ∈ f, Φ γ)) (b := P)
      (fun X => X) (sep_elim_left.trans internalEq.symm) sep_elim_right
  have hcong : (iprop(internalEq P ([∗map] γ ↦ _x ∈ f, Φ γ)) : IProp GF) ⊢
      internalEq P ([∗map] γ ↦ _x ∈ map _ (fun _ => false) f, Φ γ) :=
    (equiv_iff.mp ((internalEq.ne_r P).eqv (equiv_iff.mpr hmapeq))).1
  isplitl [Heq Hbody]
  · icombine Heq Hbody as Hc
    iapply later_mono hrecover $$ Hc
  · iexists Φ
    isplitl [Heq]
    · iapply later_mono hcong $$ Heq
    · iapply hmapres.mpr $$ Hres

@[rocq_alias slice_iff]
theorem slice_iff {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q Q' : IProp GF)
    (γ : SliceName) (b : Bool) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some b →
    □ (▷ (Q ↔ Q')) ∗ slice N γ Q ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ' P', ⌜get? (delete f γ) γ' = none⌝ ∗
      (▷?q ▷ □ (P ↔ P')) ∗
      slice N γ' Q' ∗
      (▷?q box N (insert (delete f γ) γ' b) P') := by
  intro HE Hf
  iintro ⟨#Hiff, Hslice, Hbox⟩
  cases b
  · imod slice_delete_empty E q f P Q γ N HE Hf $$ [$Hslice $Hbox] with ⟨%Pold, #HeqP, Hbox⟩
    imod slice_insert_empty E q (delete f γ) Q' Pold N $$ Hbox with ⟨%γ', %Hfresh, Hslice', Hbox⟩
    imodintro
    iexists γ', iprop(Q' ∗ Pold)
    iframe %Hfresh Hslice' Hbox
    simp only [BIBase.laterIf]
    inext; inext
    imodintro
    irewrite [HeqP]
    · refine ⟨fun _ _ _ H => ?_⟩
      exact (iff_ne.ne_left _ _).ne H
    isplit
    · iintro ⟨HQ, $⟩
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HQ
    · iintro ⟨HQ, $⟩
      icases Hiff with ⟨-, Hiff⟩
      iapply Hiff $$ HQ
  · imod slice_delete_full E q f P Q γ N HE Hf $$ [$Hslice $Hbox] with ⟨%Pold, HQ, #HeqP, Hbox⟩
    ihave HQ' : ▷ Q' $$ [Hiff HQ]
    · inext
      icases Hiff with ⟨Hif, -⟩
      iapply Hif $$ HQ
    imod slice_insert_full E q (delete f γ) Pold Q' N HE $$ [$HQ' $Hbox] with
      ⟨%γ', %Hfresh, Hslice', Hbox⟩
    imodintro
    iexists γ', iprop(Q' ∗ Pold)
    iframe %Hfresh Hslice' Hbox
    simp only [BIBase.laterIf]
    inext; inext
    imodintro
    irewrite [HeqP]
    · refine ⟨fun _ _ _ H => ?_⟩
      exact (iff_ne.ne_left _ _).ne H
    icases Hiff with ⟨#Hiff1, #Hiff2⟩
    isplit
    · iintro ⟨HQ, $⟩
      iapply Hiff1 $$ HQ
    · iintro ⟨HQ, $⟩
      iapply Hiff2 $$ HQ

@[rocq_alias slice_split]
theorem slice_split {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    [DecidableEq SliceName] (E : CoPset) (q : Bool) (f : M Bool) (P Q1 Q2 : IProp GF)
    (γ : SliceName) (b : Bool) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some b →
    slice N γ iprop(Q1 ∗ Q2) ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ1 γ2, ⌜get? (delete f γ) γ1 = none⌝ ∗
      ⌜get? (delete f γ) γ2 = none⌝ ∗ ⌜γ1 ≠ γ2⌝ ∗
      slice N γ1 Q1 ∗ slice N γ2 Q2 ∗
      (▷?q box N (insert (insert (delete f γ) γ1 b) γ2 b) P) := by
  intro HE Hf
  cases b
  · iintro ⟨Hslice, Hbox⟩
    imod slice_delete_empty E q f P iprop(Q1 ∗ Q2) γ N HE Hf $$ [Hslice Hbox] with
      ⟨%Pold, #HeqP, Hbox⟩
    · isplitl [Hslice] <;> iassumption
    imod slice_insert_empty E q (delete f γ) Q1 Pold N $$ [Hbox] with
      ⟨%γ1, %Hfresh1, Hslice1, Hbox⟩
    · iexact Hbox
    imod slice_insert_empty E q (insert (delete f γ) γ1 false) Q2 iprop(Q1 ∗ Pold) N $$ [Hbox] with
      ⟨%γ2, %Hfresh2, Hslice2, Hbox⟩
    · iexact Hbox
    rw [LawfulPartialMap.get?_insert_none_iff] at Hfresh2
    obtain ⟨Hfresh2, Hne⟩ := Hfresh2
    imodintro
    iexists γ1, γ2
    iframe %Hfresh1 %Hfresh2 %Hne Hslice1 Hslice2
    simp only [BIBase.laterIf]
    inext
    unfold box
    icases Hbox with ⟨%Φ, #Heq, Hbig⟩
    iexists Φ
    isplitl [Heq]
    · inext
      iapply internalEq.trans
      iframe Heq
      iapply internalEq.trans
      iframe HeqP
      iclear HeqP Heq
      rw [←sep_assoc.to_eq, (sep_comm (P := Q1)).to_eq]
      itrivial
    · iexact Hbig
  · iintro ⟨Hslice, Hbox⟩
    imod slice_delete_full E q f P iprop(Q1 ∗ Q2) γ N HE Hf $$ [$Hslice $Hbox] with
      ⟨%Pold, ⟨HQ1, HQ2⟩, #HeqP, Hbox⟩
    imod slice_insert_full E q (delete f γ) Pold Q1 N HE $$ [$HQ1 $Hbox] with
      ⟨%γ1, %Hfresh1, Hslice1, Hbox⟩
    imod slice_insert_full E q (insert (delete f γ) γ1 true) iprop(Q1 ∗ Pold) Q2 N HE $$
      [$HQ2 $Hbox] with ⟨%γ2, %Hfresh2, Hslice2, Hbox⟩
    rw [LawfulPartialMap.get?_insert_none_iff] at Hfresh2
    obtain ⟨Hfresh2, Hne⟩ := Hfresh2
    imodintro
    iexists γ1, γ2
    iframe %Hfresh1 %Hfresh2 %Hne Hslice1 Hslice2
    simp only [BIBase.laterIf]
    inext
    unfold box
    icases Hbox with ⟨%Φ, #Heq, Hbig⟩
    iexists Φ
    isplitl [Heq]
    · inext
      iapply internalEq.trans
      iframe Heq
      iapply internalEq.trans
      iframe HeqP
      iclear HeqP Heq
      rw [←sep_assoc.to_eq, (sep_comm (P := Q1)).to_eq]
      itrivial
    · iexact Hbig

@[rocq_alias slice_combine]
theorem slice_combine {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q1 Q2 : IProp GF)
    (γ1 γ2 : SliceName) (b : Bool) (N : Namespace) :
    ↑N ⊆ E →
    γ1 ≠ γ2 →
    get? f γ1 = some b →
    get? f γ2 = some b →
    slice N γ1 Q1 ∗ slice N γ2 Q2 ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? (delete (delete f γ1) γ2) γ = none⌝ ∗
      slice N γ iprop(Q1 ∗ Q2) ∗
      (▷?q box N (insert (delete (delete f γ1) γ2) γ b) P) := by
  intro HE Hne Hf1 Hf2
  have Hf2' : get? (delete f γ1) γ2 = some b := by rw [get?_delete_ne Hne]; exact Hf2
  cases b
  · iintro ⟨Hslice1, Hslice2, Hbox⟩
    imod slice_delete_empty E q f P Q1 γ1 N HE Hf1 $$ [$Hslice1 $Hbox] with
      ⟨%Pold1, #HeqP1, Hbox⟩
    imod slice_delete_empty E q (delete f γ1) Pold1 Q2 γ2 N HE Hf2' $$ [$Hslice2 $Hbox] with
      ⟨%Pold2, #HeqP2, Hbox⟩
    imod slice_insert_empty E q (delete (delete f γ1) γ2) iprop(Q1 ∗ Q2) Pold2 N $$ Hbox with
      ⟨%γ, %Hfresh, Hslice, Hbox⟩
    imodintro
    iexists γ
    iframe %Hfresh Hslice
    simp only [BIBase.laterIf]
    inext
    unfold box
    icases Hbox with ⟨%Φ, #Heq, Hbig⟩
    iexists Φ
    isplitl [Heq]
    · inext
      iapply internalEq.trans
      iframe Heq
      iapply internalEq.trans
      iframe HeqP1
      irewrite [HeqP2]
      · refine ⟨fun _ _ _ H => ?_⟩
        refine (NonExpansive₂.ne_left internalEq _).ne ?_
        exact (sep_ne.ne_right _ _).ne H
      iclear HeqP1 HeqP2 Heq
      rw [←sep_assoc.to_eq, (sep_comm (P := Q1)).to_eq]
      itrivial
    · iexact Hbig
  · iintro ⟨Hslice1, Hslice2, Hbox⟩
    imod slice_delete_full E q f P Q1 γ1 N HE Hf1 $$ [$Hslice1 $Hbox] with
      ⟨%Pold1, HQ1, #HeqP1, Hbox⟩
    imod slice_delete_full E q (delete f γ1) Pold1 Q2 γ2 N HE Hf2' $$ [$Hslice2 $Hbox] with
      ⟨%Pold2, HQ2, #HeqP2, Hbox⟩
    icombine HQ1 HQ2 as HQ12
    imod slice_insert_full E q (delete (delete f γ1) γ2) Pold2 iprop(Q1 ∗ Q2) N HE $$
      [$HQ12 $Hbox] with ⟨%γ, %Hfresh, Hslice, Hbox⟩
    imodintro
    iexists γ
    iframe %Hfresh Hslice
    simp only [BIBase.laterIf]
    inext
    unfold box
    icases Hbox with ⟨%Φ, #Heq, Hbig⟩
    iexists Φ
    isplitl [Heq]
    · inext
      iapply internalEq.trans
      iframe Heq
      iapply internalEq.trans
      iframe HeqP1
      irewrite [HeqP2]
      · refine ⟨fun _ _ _ H => ?_⟩
        refine (NonExpansive₂.ne_left internalEq _).ne ?_
        exact (sep_ne.ne_right _ _).ne H
      iclear HeqP1 HeqP2 Heq
      rw [←sep_assoc.to_eq, (sep_comm (P := Q1)).to_eq]
      itrivial
    · iexact Hbig

end Iris

end
