/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko, Xiaoyang Lu, Zongyuan Liu
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
    (OptionOF (AgreeRF (LaterOF IdOF)))

@[rocq_alias boxG]
class BoxG where
  [elemG : ElemG GF BoxF]

attribute [reducible, instance] BoxG.elemG

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [BoxG GF]

@[rocq_alias slice_name]
abbrev SliceName := GName

@[rocq_alias box_own_auth]
def box_own_auth (γ : SliceName) (a : Auth (Option (Excl BoolO))) : IProp GF :=
  iOwn (F := BoxF) γ (a, none)

instance box_own_auth_timeless (γ : SliceName) (a : Auth (Option (Excl BoolO))) :
    BI.Timeless (box_own_auth (GF := GF) γ a) :=
  iOwn_timeless (F := BoxF) (a := ((a, none) : BoxF.ap (IProp GF)))

@[rocq_alias box_own_prop]
def box_own_prop (γ : SliceName) (P : IProp GF) : IProp GF :=
  iOwn (F := BoxF) γ (UCMRA.unit, some (toAgree (Later.next P)))

instance box_own_prop_persistent (γ : SliceName) (P : IProp GF) :
    Persistent (box_own_prop γ P) := by
  unfold box_own_prop; infer_instance

@[rocq_alias box_own_prop_contractive]
instance box_own_prop_contractive (γ : SliceName) : Contractive (box_own_prop (GF := GF) γ) :=
  ⟨fun {_ _ _} h => iOwn_ne.ne <|
    dist_prod_ext Dist.rfl (toAgree.ne.ne (NextContractive.distLater_dist h))⟩

@[rocq_alias box_own_prop_ne]
instance box_own_prop_ne (γ : SliceName) : NonExpansive (box_own_prop (GF := GF) γ) := ne_of_contractive _

@[rocq_alias slice_inv]
def slice_inv (γ : SliceName) (P : IProp GF) : IProp GF :=
  iprop% ∃ b : Bool, box_own_auth γ (●E (⟨b⟩ : BoolO)) ∗ if b then P else True

@[rocq_alias slice]
def slice (N : Namespace) (γ : SliceName) (P : IProp GF) : IProp GF :=
  iprop% box_own_prop γ P ∗ inv N (slice_inv γ P)

@[rocq_alias box]
def box {M : Type _ → Type _} [LawfulFiniteMap M SliceName] (N : Namespace) (f : M Bool)
  (P : IProp GF) : IProp GF :=
  iprop% ∃ Φ : SliceName → IProp GF,
    ▷ internalEq P ([∗map] γ ↦ _x ∈ f, Φ γ) ∗
    [∗map] γ ↦ b ∈ f, box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗ inv N (slice_inv γ (Φ γ))

@[rocq_alias box_inv_ne]
instance slice_inv_ne (γ : SliceName) : NonExpansive (slice_inv (GF := GF) γ) :=
  ⟨fun _ _ _ h => exists_ne (fun b => sep_ne.ne Dist.rfl (b.casesOn Dist.rfl h))⟩

@[rocq_alias slice_ne]
instance slice_ne (N : Namespace) (γ : SliceName) : NonExpansive (slice (GF := GF) N γ) :=
  ⟨fun {_ _ _} h => sep_ne.ne ((box_own_prop_ne γ).ne h) ((inv_ne N).ne ((slice_inv_ne γ).ne h))⟩

@[rocq_alias slice_contractive]
instance slice_contractive (N : Namespace) (γ : SliceName) : Contractive (slice (GF := GF) N γ) :=
  ⟨fun {_ _ _} h => sep_ne.ne ((box_own_prop_contractive γ).distLater_dist h)
    ((inv_contractive N).distLater_dist (fun m hm => (slice_inv_ne γ).ne (h m hm)))⟩

@[rocq_alias slice_persistent]
instance slice_persistent (N : Namespace) (γ : SliceName) (P : IProp GF) :
    Persistent (slice N γ P) := by
  unfold slice; infer_instance

@[rocq_alias box_contractive]
instance box_contractive {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (N : Namespace) (f : M Bool) : Contractive (box (GF := GF) N f) :=
  ⟨fun {_ _ _} h => exists_ne fun _ => sep_ne.ne
    (Contractive.distLater_dist fun _ hm => (internalEq.ne_l _).ne (h _ hm)) Dist.rfl⟩

@[rocq_alias box_ne]
instance box_ne {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
  (N : Namespace) (f : M Bool) : NonExpansive (box (GF := GF) N f) := ne_of_contractive _

@[rocq_alias box_own_auth_agree]
theorem box_own_auth_agree {γ : SliceName} {b1 b2 : Bool} :
    box_own_auth (GF := GF) γ (●E (⟨b1⟩ : BoolO)) ∗ box_own_auth γ (◯E ⟨b2⟩) ⊢ ⌜b1 = b2⌝ := by
  simp only [box_own_auth, ← iOwn_op.to_eq]
  iintro H
  icases iOwn_cmraValid $$ H with H
  icases (prod_validI _).mp $$ H with ⟨%H, -⟩
  ipureintro; exact LeibnizO.eqv_inj $ Iris.ExclAuth.agree_L H

@[rocq_alias box_own_auth_update]
theorem box_own_auth_update {γ : SliceName} {b1 b2: Bool} (b3 : Bool) :
    box_own_auth (GF := GF) γ (●E (⟨b1⟩ : BoolO)) ∗ box_own_auth γ (◯E ⟨b2⟩) ==∗
    box_own_auth γ (●E ⟨b3⟩) ∗ box_own_auth γ (◯E ⟨b3⟩) := by
  simp only [box_own_auth, ← iOwn_op.to_eq]
  iapply iOwn_update (Update.prod _ ExclAuth.update (Update.id (x := none)))

@[rocq_alias box_own_agree]
theorem box_own_agree (γ : SliceName) (Q1 Q2 : IProp GF) :
    box_own_prop γ Q1 ∗ box_own_prop γ Q2 ⊢ ▷ internalEq Q1 Q2 := by
  simp only [box_own_prop, ←iOwn_op.to_eq]
  iintro H
  icases iOwn_cmraValid $$ H with H
  icases (prod_validI _).mp $$ H with ⟨-, H⟩
  rw [option_validI.to_eq, ←(later_equivI ..).to_eq, ←(agree_equivI ..).to_eq]
  -- TODO: Goal display is broken
  exact (agree_op_invI ..)

@[rocq_alias box_alloc]
theorem box_alloc {M : Type _ → Type _} [LawfulFiniteMap M SliceName] (N : Namespace) :
    ⊢ box (GF := GF) N (∅ : M Bool) iprop(emp) := by
  unfold box
  iexists (fun _ => iprop(True))
  simp only [bigSepM_empty.to_eq]; itrivial

@[rocq_alias slice_insert_empty]
theorem slice_insert_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
  (E : CoPset) {q : Bool} {f : M Bool} (Q : IProp GF) {P : IProp GF} {N : Namespace} :
    (▷?q box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? f γ = none⌝ ∗
      slice N γ Q ∗ ▷?q box N (insert f γ false) iprop(Q ∗ P) := by
  unfold box
  iintro ⟨%Φ, #Heq, H⟩
  imod (iOwn_alloc_cofinite (F := BoxF) ((((●E (⟨false⟩ : BoolO)), none) • ((◯E (⟨false⟩ : BoolO)), none)) •
        (UCMRA.unit, some (toAgree (Later.next Q)))) ((toList f).map Prod.fst)) with ⟨%γ, %Hγ, Hown⟩
  · exact ⟨ExclAuth.valid, Agree.toAgree_valid⟩
  have hfresh : get? f γ = none := by
    rw [Option.eq_none_iff_forall_not_mem]
    exact fun v h => Hγ (List.mem_map_of_mem (toList_get.mpr h))
  icases iOwn_op $$ Hown with ⟨⟨Hauth, Hfrag⟩, #Hprop⟩
  imod inv_alloc N E (slice_inv γ Q) $$ [Hauth] with #Hinv
  · inext
    unfold slice_inv box_own_auth; iexists false
    simp only [Bool.false_eq_true, if_false]; iframe
  imodintro
  iexists γ
  unfold slice; iframe %hfresh Hinv
  isplit
  · unfold box_own_prop; iframe Hprop
  iexists (fun γ'' => if γ'' = γ then Q else Φ γ'')
  inext
  isplit
  · inext
    irewrite [Heq]
    · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_left internalEq _).ne ((sep_ne.ne_right _ _).ne H)⟩
    rw [(bigSepM_fn_insert_key hfresh).to_eq]; exact internalEq.refl
  · rw [(bigSepM_fn_insert (g := fun k b P' =>
        iprop% box_own_auth k (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop k P' ∗ inv N (slice_inv k P')) hfresh).to_eq]
    unfold box_own_prop box_own_auth; iframe H Hfrag Hprop Hinv

@[rocq_alias slice_delete_empty]
theorem slice_delete_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    {E : CoPset} {q : Bool} {f : M Bool} {P Q : IProp GF}
    {γ : SliceName} {N : Namespace}
    (Hf : get? f γ = some false) :
    slice N γ Q ∗ ▷?q box N f P ⊢
    |={E}=> ∃ P', ▷?q (▷ internalEq P iprop(Q ∗ P')) ∗ ▷?q (box N (delete f γ) P') := by
  unfold slice box
  iintro ⟨⟨#Hprop, #Hinv⟩, %Φ, #Heq, Hbig⟩
  iexists iprop([∗map] γ' ↦ _x ∈ delete f γ, Φ γ')
  icases bigSepM_laterN $$ Hbig with Hbig
  icases bigSepM_delete Hf $$ Hbig with ⟨⟨Hfrag, #Hprop', #Hsliceinv⟩, Hbig⟩
  imodintro
  rw [← (laterN_sep _).to_eq]
  icases bigSepM_laterN $$ Hbig with Hbig
  inext
  ihave #Heq' := (box_own_agree γ Q (Φ γ)) $$ [$Hprop $Hprop']
  isplit
  · inext
    irewrite [Heq']
    · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_right _ _).ne ((sep_ne.ne_left _ _).ne H)⟩
    irewrite [Heq]
    · exact internalEq.ne_l _
    iapply prop_ext
    iclear Hprop Hinv Hprop' Hsliceinv
    imodintro
    iapply bigSepM_delete Hf
  · iexists Φ; iframe; itrivial

@[rocq_alias slice_fill]
theorem slice_fill {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    {E : CoPset} {q : Bool} {f : M Bool} {γ : SliceName}
    {P Q : IProp GF} {N : Namespace}
    (HE : ↑N ⊆ E) (Hf : get? f γ = some false) :
    slice N γ Q ∗ ▷ Q ∗ ▷?q box N f P ⊢
    |={E}=> ▷?q box N (insert f γ true) P := by
  unfold slice box
  iintro ⟨⟨#Hprop, #Hinv⟩, HQ, %Φ, #Heq, Hbig⟩
  icases bigSepM_laterN $$ Hbig with Hbig
  icases bigSepM_delete Hf $$ Hbig with ⟨⟨Hfrag, Hprop', Hsliceinv⟩, Hbig⟩
  imod inv_acc HE $$ Hinv with ⟨Hsinv, Hclose⟩
  unfold slice_inv; icases Hsinv with ⟨%b, >Hauth, Hb⟩
  icases Hfrag with >Hfrag
  imod box_own_auth_update true $$ [$Hauth $Hfrag] with ⟨Hauth, Hfrag⟩
  imod Hclose $$ [Hauth HQ] with ⟨-⟩
  · inext; iexists true; simp only [if_true]; iframe
  imodintro
  icases bigSepM_laterN $$ Hbig with Hbig
  inext
  iexists Φ
  rw [(bigSepM_insert_delete.trans (bigSepM_delete (Φ := fun k _ => Φ k) Hf).symm).to_eq]
  iframe Heq
  rw [bigSepM_insert_delete.to_eq]
  iframe

@[rocq_alias slice_empty]
theorem slice_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    {E : CoPset} {q : Bool} {f : M Bool} {P Q : IProp GF}
    {γ : SliceName} {N : Namespace}
    (HE : ↑N ⊆ E) (Hf : get? f γ = some true) :
    slice N γ Q ∗ ▷?q box N f P ⊢
    |={E}=> ▷ Q ∗ (▷?q box N (insert f γ false) P) := by
  unfold slice box
  iintro ⟨⟨#Hprop, #Hinv⟩, %Φ, #Heq, Hbig⟩
  simp only [bigSepM_laterN.to_eq]
  icases bigSepM_delete Hf $$ Hbig with ⟨⟨Hfrag, Hprop', Hsliceinv⟩, Hbig⟩
  imod inv_acc HE $$ Hinv with ⟨Hsinv, Hclose⟩
  unfold slice_inv
  icases Hsinv with ⟨%b, >Hauth, Hb⟩
  icases Hfrag with >Hfrag
  ihave %hb := box_own_auth_agree $$ [$Hauth $Hfrag]; subst hb
  imod box_own_auth_update false $$ [$Hauth $Hfrag] with ⟨Hauth, Hfrag⟩
  imod Hclose $$ [Hauth]
  · inext; iexists false; simp only [Bool.false_eq_true, if_false]; iframe
  imodintro
  simp only [if_true]; iframe Hb
  iexists Φ
  icases bigSepM_laterN $$ Hbig with Hbig
  inext
  rw [(bigSepM_insert_delete.trans (bigSepM_delete (Φ := fun k _ => Φ k) Hf).symm).to_eq]
  iframe Heq
  rw [bigSepM_insert_delete.to_eq]
  iframe

@[rocq_alias slice_insert_full]
theorem slice_insert_full {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    {E : CoPset} {q : Bool} {f : M Bool} {P Q : IProp GF} {N : Namespace}
    (HE : ↑N ⊆ E) :
    ▷ Q ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? f γ = none⌝ ∗
      slice N γ Q ∗ (▷?q box N (insert f γ true) iprop(Q ∗ P)) := by
  iintro ⟨HQ, Hbox⟩
  imod slice_insert_empty E Q $$ Hbox with ⟨%γ, %Hfresh, #Hslice, Hbox⟩
  iexists γ
  iframe %Hfresh Hslice
  imod slice_fill HE (get?_insert_eq rfl) $$ [$Hslice $HQ $Hbox] with Hbox
  imodintro
  simp only [box, (bigSepM_eqv_of_perm LawfulPartialMap.insert_insert_same).to_eq]
  itrivial

@[rocq_alias slice_delete_full]
theorem slice_delete_full {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    {E : CoPset} {q : Bool} {f : M Bool} {P Q : IProp GF}
    {γ : SliceName} {N : Namespace}
    (HE : ↑N ⊆ E) (Hf : PartialMap.get? f γ = some true) :
    slice N γ Q ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ P', ▷ Q ∗
      (▷?q ▷ internalEq P iprop(Q ∗ P')) ∗ (▷?q box N (delete f γ) P') := by
  iintro ⟨#Hslice, Hbox⟩
  imod slice_empty HE Hf $$ [$Hslice $Hbox] with ⟨HQ, Hbox⟩
  imod slice_delete_empty (get?_insert_eq rfl) $$ [$Hslice $Hbox] with ⟨%P', #Heq, Hbox⟩
  iexists P'
  iframe HQ Heq
  have hdel : delete (insert f γ false) γ ≡ₘ delete f γ := fun j => by
    by_cases h : γ = j
    · simp only [get?_delete_eq h]
    · simp only [get?_delete_ne h, get?_insert_ne h]
  simp only [box, (bigSepM_eqv_of_perm hdel).to_eq]
  itrivial

@[rocq_alias box_fill]
theorem box_fill {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) {f : M Bool} {P : IProp GF} {N : Namespace}
    (HE : ↑N ⊆ E) :
    box N f P ∗ ▷ P ⊢ |={E}=> box N (Std.PartialMap.map (fun _ => true) f) P := by
  unfold box
  iintro ⟨⟨%Φ, #Heq, Hbig⟩, HP⟩
  iexists Φ
  isplitr
  · rw [(bigSepM_map (f := fun x => true)).to_eq]
    iframe Heq
  · ihave Hiff : (▷ (P ↔ ([∗map] γ ↦ x ∈ f, Φ γ))) $$ []
    · inext; iapply internalEq_iff $$ Heq
    icases later_iff $$ Hiff with ⟨Hif, -⟩
    icases Hif $$ HP with HP
    icases bigSepM_later $$ HP with HP
    icombine Hbig HP as Hbig
    icases bigSepM_sep_eqv $$ Hbig with Hbig
    rw [(bigSepM_map (f := fun x => true)).to_eq]
    iapply bigSepM_fupd
    iapply bigSepM_impl $$ Hbig
    imodintro
    iintro %k %v %Heq ⟨⟨Hγ', #HγΦ, #Hinv⟩, H⟩
    imod inv_acc HE $$ Hinv with ⟨Hsinv, Hclose⟩
    unfold slice_inv; icases Hsinv with ⟨%b, >Hauth, Hb⟩
    imod box_own_auth_update true $$ [$Hauth $Hγ'] with ⟨Hauth, Hfrag⟩
    imod Hclose $$ [Hauth H]
    · inext; iexists true; simp only [↓reduceIte]; iframe Hauth H
    imodintro
    iframe Hfrag HγΦ Hinv

@[rocq_alias box_empty]
theorem box_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) {f : M Bool} {P : IProp GF} {N : Namespace}
    (HE : ↑N ⊆ E) (Hall: all (fun _ b => b = true) f) :
    box N f P ⊢ |={E}=> ▷ P ∗ box N (Std.PartialMap.map (fun _ => false) f) P := by
  unfold box
  iintro ⟨%Φ, #Heq, Hbig⟩
  ihave >⟨HΦ, H⟩ : iprop(|={E}=> (([∗map] γ ↦ b ∈ f, ▷ Φ γ) ∗
    [∗map] γ ↦ b ∈ f, box_own_auth γ (◯E ⟨false⟩) ∗  box_own_prop γ (Φ γ) ∗
      inv N (slice_inv γ (Φ γ)))) $$ [Hbig]
  · rw [←bigSepM_sep_eqv.to_eq]
    iapply bigSepM_fupd
    iapply bigSepM_impl $$ Hbig
    imodintro
    iintro %k %v %Heq ⟨Hγ', #HγΦ, #Hinv⟩
    have Heq' : v = true := Hall k v Heq; subst v
    imod inv_acc HE $$ Hinv with ⟨Hsinv, Hclose⟩
    unfold slice_inv; icases Hsinv with ⟨%b, >Hauth, Hb⟩
    ihave %hb := box_own_auth_agree $$ [$Hauth $Hγ']; subst hb
    imod box_own_auth_update false $$ [$Hauth $Hγ'] with ⟨Hauth, Hfrag⟩
    imod Hclose $$ [Hauth]
    · inext; iexists false; simp only [Bool.false_eq_true, if_false]; iframe
    imodintro
    simp only [if_true]; iframe Hb HγΦ Hfrag Hinv
  · imodintro
    isplitl [HΦ]
    · icases bigSepM_later $$ HΦ with HΦ
      inext
      icases internalEq_iff $$ Heq with ⟨-, Himpl⟩
      iapply Himpl $$ HΦ
    · iexists Φ
      rw [(bigSepM_map (Φ := fun k _ => Φ k)).to_eq]
      isplit
      · inext; itrivial
      · rw [bigSepM_map.to_eq]; itrivial

@[rocq_alias slice_iff]
theorem slice_iff {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q Q' : IProp GF)
    (γ : SliceName) (b : Bool) (N : Namespace)
    (HE : ↑N ⊆ E) (Hf : get? f γ = some b) :
    □ (▷ (Q ↔ Q')) ∗ slice N γ Q ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ' P', ⌜get? (delete f γ) γ' = none⌝ ∗
      (▷?q ▷ □ (P ↔ P')) ∗
      slice N γ' Q' ∗
      (▷?q box N (insert (delete f γ) γ' b) P') := by
  iintro ⟨#Hiff, Hslice, Hbox⟩
  cases b
  · imod slice_delete_empty Hf $$ [$Hslice $Hbox] with ⟨%Pold, #HeqP, Hbox⟩
    imod slice_insert_empty E Q' $$ Hbox with ⟨%γ', %Hfresh, Hslice', Hbox⟩
    imodintro
    iexists γ', iprop(Q' ∗ Pold)
    iframe %Hfresh Hslice' Hbox
    inext; inext
    imodintro
    irewrite [HeqP]
    · refine ⟨fun _ _ _ H => (iff_ne.ne_left _ _).ne H⟩
    icases Hiff with ⟨#Hiff1, #Hiff2⟩
    isplit
    · iintro ⟨HQ, $⟩
      iapply Hiff1 $$ HQ
    · iintro ⟨HQ, $⟩
      iapply Hiff2 $$ HQ
  · imod slice_delete_full HE Hf $$ [$Hslice $Hbox] with ⟨%Pold, HQ, #HeqP, Hbox⟩
    icases later_iff $$ Hiff with ⟨Hif, -⟩
    icases Hif $$ HQ with HQ'
    imod slice_insert_full HE $$ [$HQ' $Hbox] with ⟨%γ', %Hfresh, Hslice', Hbox⟩
    imodintro
    iexists γ', iprop(Q' ∗ Pold)
    iframe %Hfresh Hslice' Hbox
    inext; inext
    imodintro
    irewrite [HeqP]
    · refine ⟨fun _ _ _ H => (iff_ne.ne_left _ _).ne H⟩
    icases Hiff with ⟨#Hiff1, #Hiff2⟩
    isplit
    · iintro ⟨HQ, $⟩
      iapply Hiff1 $$ HQ
    · iintro ⟨HQ, $⟩
      iapply Hiff2 $$ HQ

@[rocq_alias slice_split]
theorem slice_split {M : Type _ → Type _} [LawfulFiniteMap M SliceName] [DecidableEq SliceName]
  {E : CoPset} {q : Bool} {f : M Bool} {P Q1 Q2 : IProp GF} {γ : SliceName} {b : Bool} {N : Namespace}
  (HE : ↑N ⊆ E) (Hf : get? f γ = some b) :
    slice N γ iprop(Q1 ∗ Q2) ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ1 γ2, ⌜get? (delete f γ) γ1 = none⌝ ∗
      ⌜get? (delete f γ) γ2 = none⌝ ∗ ⌜γ1 ≠ γ2⌝ ∗
      slice N γ1 Q1 ∗ slice N γ2 Q2 ∗
      (▷?q box N (insert (insert (delete f γ) γ1 b) γ2 b) P) := by
  cases b
  · iintro ⟨Hslice, Hbox⟩
    imod slice_delete_empty Hf $$ [$Hslice $Hbox] with ⟨%Pold, #HeqP, Hbox⟩
    imod slice_insert_empty E Q1 $$ Hbox with ⟨%γ1, %Hfresh1, Hslice1, Hbox⟩
    imod slice_insert_empty E Q2 $$ Hbox with ⟨%γ2, %Hfresh2, Hslice2, Hbox⟩
    rw [LawfulPartialMap.get?_insert_none_iff] at Hfresh2
    obtain ⟨Hfresh2, Hne⟩ := Hfresh2
    imodintro
    iexists γ1, γ2
    iframe %Hfresh1 %Hfresh2 %Hne Hslice1 Hslice2
    inext
    iapply (internalEq_rewrite_contractive iprop(Q2 ∗ Q1 ∗ Pold) P (box N _))
    · inext
      iapply internalEq.symm
      irewrite [HeqP]
      · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_left internalEq _).ne H⟩
      rw [←sep_assoc.to_eq, (sep_comm (P := Q1)).to_eq]; itrivial
    · itrivial
  · iintro ⟨Hslice, Hbox⟩
    imod slice_delete_full HE Hf $$ [$Hslice $Hbox] with ⟨%Pold, ⟨HQ1, HQ2⟩, #HeqP, Hbox⟩
    imod slice_insert_full HE $$ [$HQ1 $Hbox] with ⟨%γ1, %Hfresh1, Hslice1, Hbox⟩
    imod slice_insert_full HE $$ [$HQ2 $Hbox] with ⟨%γ2, %Hfresh2, Hslice2, Hbox⟩
    rw [LawfulPartialMap.get?_insert_none_iff] at Hfresh2
    obtain ⟨Hfresh2, Hne⟩ := Hfresh2
    imodintro
    iexists γ1, γ2
    iframe %Hfresh1 %Hfresh2 %Hne Hslice1 Hslice2
    inext
    iapply (internalEq_rewrite_contractive iprop(Q2 ∗ Q1 ∗ Pold) P (box N _))
    · inext
      iapply internalEq.symm
      irewrite [HeqP]
      · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_left internalEq _).ne H⟩
      rw [←sep_assoc.to_eq, (sep_comm (P := Q1)).to_eq]
      itrivial
    · itrivial

@[rocq_alias slice_combine]
theorem slice_combine {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) {q : Bool} {f : M Bool} {P Q1 Q2 : IProp GF}
    {γ1 γ2 : SliceName} {b : Bool} {N : Namespace}
    (HE : ↑N ⊆ E) (Hne : γ1 ≠ γ2) (Hf1 : get? f γ1 = some b) (Hf2 : get? f γ2 = some b) :
    slice N γ1 Q1 ∗ slice N γ2 Q2 ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? (delete (delete f γ1) γ2) γ = none⌝ ∗
      slice N γ iprop(Q1 ∗ Q2) ∗
      (▷?q box N (insert (delete (delete f γ1) γ2) γ b) P) := by
  have Hf2' : get? (delete f γ1) γ2 = some b := by rw [get?_delete_ne Hne]; exact Hf2
  cases b
  · iintro ⟨Hslice1, Hslice2, Hbox⟩
    imod slice_delete_empty Hf1 $$ [$Hslice1 $Hbox] with ⟨%Pold1, #HeqP1, Hbox⟩
    imod slice_delete_empty Hf2' $$ [$Hslice2 $Hbox] with ⟨%Pold2, #HeqP2, Hbox⟩
    imod slice_insert_empty E iprop(Q1 ∗ Q2) $$ Hbox with ⟨%γ, %Hfresh, Hslice, Hbox⟩
    imodintro
    iexists γ
    iframe %Hfresh Hslice
    inext
    iapply (internalEq_rewrite_contractive iprop((Q1 ∗ Q2) ∗ Pold2) P (box N _))
    · inext
      iapply internalEq.symm
      irewrite [HeqP1]
      · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_left internalEq _).ne H⟩
      irewrite [HeqP2]
      · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_left internalEq _).ne ((sep_ne.ne_right _ _).ne H)⟩
      rw [sep_assoc.to_eq]
      itrivial
    · itrivial
  · iintro ⟨Hslice1, Hslice2, Hbox⟩
    imod slice_delete_full HE Hf1 $$ [$Hslice1 $Hbox] with ⟨%Pold1, HQ1, #HeqP1, Hbox⟩
    imod slice_delete_full HE Hf2' $$ [$Hslice2 $Hbox] with ⟨%Pold2, HQ2, #HeqP2, Hbox⟩
    icombine HQ1 HQ2 as HQ12
    imod slice_insert_full HE $$ [$HQ12 $Hbox] with ⟨%γ, %Hfresh, Hslice, Hbox⟩
    imodintro
    iexists γ
    iframe %Hfresh Hslice
    inext
    iapply (internalEq_rewrite_contractive iprop((Q1 ∗ Q2) ∗ Pold2) P (box N _))
    · inext
      iapply internalEq.symm
      irewrite [HeqP1]
      · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_left internalEq _).ne H⟩
      irewrite [HeqP2]
      · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_left internalEq _).ne ((sep_ne.ne_right _ _).ne H)⟩
      rw [sep_assoc.to_eq]
      itrivial
    · itrivial

end Iris

end
