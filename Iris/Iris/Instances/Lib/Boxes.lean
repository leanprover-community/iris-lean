/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyang Lu
-/
module

public import Iris.ProofMode
public import Iris.Algebra.Lib.ExclAuth
public import Iris.Algebra.Agree
public import Iris.Instances.Lib.Invariants
public import Iris.Algebra.BigOp

@[expose] public section

namespace Iris

open OFE COFE ExclAuth Agree CMRA UCMRA Std BI Prod Option

abbrev BoxF : OFunctorPre :=
  ProdOF (constOF (ExclAuthR (A := LeibnizO Bool)))
         (OptionOF (AgreeRF (LaterOF (IdOF))))

@[rocq_alias boxG]
class BoxG (GF : BundledGFunctors) where
  inG : ElemG GF BoxF

attribute [reducible, instance] BoxG.inG

namespace Box

section Definitions

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [W : BoxG GF] (N : Namespace)

@[rocq_alias slice_name]
abbrev SliceName := GName
abbrev SliceMap V := Std.ExtTreeMap SliceName V compare

@[rocq_alias box_own_auth]
def own_auth (γ : SliceName) (a : ExclAuthR (A := LeibnizO Bool)) : IProp GF :=
  iOwn (E := W.inG) γ (a, none)

@[rocq_alias box_own_prop]
def own_prop (γ : SliceName) (P : IProp GF) : IProp GF :=
  iOwn (E := W.inG) γ (unit, some (toAgree (Later.next P)))

@[rocq_alias slice_inv]
def slice_inv (γ : SliceName) (P : IProp GF) : IProp GF :=
  iprop(∃ b, own_auth γ (●E (.mk b)) ∗ if b then P else True)

@[rocq_alias slice]
def slice (γ : SliceName) (P : IProp GF) : IProp GF :=
  iprop(own_prop γ P ∗ inv N (slice_inv γ P))

@[rocq_alias box]
def box (f : SliceMap Bool) (P : IProp GF) : IProp GF :=
  iprop(∃ (Φ : SliceName → IProp GF),
          ▷ internalEq P ([∗map] γ ↦ _b ∈ f, Φ γ) ∗
          [∗map] γ ↦ b ∈ f, own_auth γ (◯E (.mk b)) ∗ own_prop γ (Φ γ) ∗
                            inv N (slice_inv γ (Φ γ)))

end Definitions

section Instances

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [BoxG GF] (N : Namespace)

@[rocq_alias box_own_prop_contractive]
instance own_prop_contractive γ : Contractive (own_prop (GF := GF) γ) where
  distLater_dist H := by
    unfold own_prop
    apply NonExpansive.ne
    apply NonExpansive₂.ne .rfl
    apply NonExpansive.ne
    apply NonExpansive.ne
    .exact Contractive.distLater_dist H

@[rocq_alias box_own_prop_ne]
instance own_prop_ne γ : NonExpansive (own_prop (GF := GF) γ) := ne_of_contractive _

@[rocq_alias box_inv_ne]
instance slice_inv_ne γ : NonExpansive (slice_inv (GF := GF) γ) where
  ne {n P Q} H := by
    unfold slice_inv
    refine exists_ne (fun b => ?_)
    refine sep_ne.ne .rfl ?_
    cases b with
    | true => exact H
    | false => .rfl

@[rocq_alias slice_contractive]
instance slice_contractive γ : Contractive (slice (GF := GF) N γ) where
  distLater_dist H := by
    unfold slice
    refine sep_ne.ne ?_ ?_
    · exact Contractive.distLater_dist H
    · refine Contractive.distLater_dist (fun i H' => ?_)
      refine NonExpansive.ne ?_
      exact (H _ H')

@[rocq_alias slice_ne]
instance slice_ne γ : NonExpansive (own_prop (GF := GF) γ) := ne_of_contractive _

#rocq_ignore slice_proper "?"

@[rocq_alias slice_persistent]
instance slice_persistent γ P : Persistent (slice (GF := GF) N γ P) := by
  simp only [slice, own_prop]
  infer_instance

instance own_prop_persistent γ P : Persistent (own_prop (GF := GF) γ P) := by
  unfold own_prop
  infer_instance

@[rocq_alias box_contractive]
instance box_contractive f : Contractive (box (GF := GF) N f) where
  distLater_dist H := by
    unfold box
    refine exists_ne (fun Φ => ?_)
    refine sep_ne.ne ?_ .rfl
    refine Contractive.distLater_dist (fun i H' => ?_)
    refine NonExpansive₂.ne ?_ .rfl
    exact (H _ H')

@[rocq_alias box_ne]
instance box_ne f : NonExpansive (box (GF := GF) N f) := ne_of_contractive _

#rocq_ignore box_proper "?"

end Instances

section Lemmas

open scoped PartialMap
open Std ProofMode BigSepM Algebra.BigOpM LawfulPartialMap

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [W : BoxG GF] (N : Namespace)

@[rocq_alias box_own_auth_agree]
theorem own_auth_agree γ b1 b2 :
  own_auth (GF := GF) γ (●E b1) ∗ own_auth γ (◯E b2) ⊢ ⌜b1 = b2⌝ := by
  simp only [own_auth, ←iOwn_op.to_eq]
  iintro H
  ihave H := iOwn_cmraValid $$ H
  ihave H := (prod_validI _).mp $$ H
  ihave %H := and_elim_l $$ H
  ipureintro; apply agree_L; assumption

@[rocq_alias box_own_auth_update]
theorem own_auth_update γ b1 b2 b3 :
  ⊢ own_auth (GF := GF) γ (●E b1) ∗ own_auth γ (◯E b2)
    ==∗ own_auth γ (●E b3) ∗ own_auth γ (◯E b3) := by
  simp only [own_auth, ←iOwn_op.to_eq]
  iapply iOwn_update
  apply Update.prod
  · apply ExclAuth.update
  · apply Update.id

@[rocq_alias box_own_agree]
theorem own_agree γ Q1 Q2 :
  own_prop (GF := GF) γ Q1 ∗ own_prop γ Q2 ⊢ ▷ internalEq Q1 Q2 := by
  simp only [own_prop, ←iOwn_op.to_eq]
  iintro H
  ihave H := iOwn_cmraValid $$ H
  ihave H := (prod_validI _).mp $$ H
  ihave H := and_elim_r $$ H
  rw [(option_validI _).to_eq, ←(later_equivI ..).to_eq, ←(agree_equivI ..).to_eq]
  exact (agree_op_invI ..)

@[rocq_alias box_alloc]
theorem box_alloc : ⊢ box (GF := GF) N (∅ : SliceMap Bool) iprop(True) := by
  unfold box
  iexists (fun _ => iprop(True))
  simp only [bigSepM_empty.to_eq]
  isplit; imodintro; ipureintro; rfl; iempintro

private theorem prod_unit_split_r [CMRA A] [UCMRA B] (a b : A) :
  ((a • b, unit) : A × B) ≡ (a, unit) • (b, unit) := ⟨.rfl, unit_left_id.symm⟩

private theorem mem_fmap {A B} (f : A → B) x (l : List A) :
  x ∈ l → f x ∈ f <$> l := by
  intro h; induction h
  · apply List.Mem.head
  · apply List.Mem.tail; assumption

private theorem not_elem_get_none {γ} {f : SliceMap A} :
  ¬γ ∈ Prod.fst <$> toList f → get? f γ = none := by
  intro h; cases h' : (get? f γ); rfl
  rw [←LawfulFiniteMap.toList_get] at h'
  exfalso; exact h (mem_fmap _ _ _ h')

@[rocq_alias slice_insert_empty]
theorem slice_insert_empty E q f Q P :
  ▷?q box (GF := GF) N f P ={E}=∗ ∃ γ, ⌜get? f γ = none⌝ ∗
    slice N γ Q ∗ ▷?q box N (insert f γ false) iprop(Q ∗ P) := by
  unfold box
  iintro ⟨%Φ, #HeqP, HF⟩
  imod (iOwn_alloc_cofinite (E := W.inG)
                            ((●E (LeibnizO.mk false)) • (◯E (LeibnizO.mk false)),
                            some (toAgree (Later.next Q))) (Prod.fst <$> toList f))
  with ⟨%γ, Hdom, Hγ⟩
  · constructor
    · rw [Auth.auth_both_valid_discrete]
      exact ⟨.rfl, .intro⟩
    · rw [some_valid]
      apply toAgree_valid
  ihave Hγ := (iOwn_ne.eqv (prod_split ..).symm) $$ Hγ
  icases iOwn_op $$ Hγ with ⟨Hγ, #HγQ⟩
  ihave Hγ := (iOwn_ne.eqv (prod_unit_split_r ..).symm) $$ Hγ
  icases iOwn_op $$ Hγ with ⟨Hγ, Hγ'⟩
  icases Hdom with %Hdom
  have Hdom' : get? f γ = none := not_elem_get_none Hdom
  imod inv_alloc N _ (slice_inv γ Q) $$ [Hγ] with #Hinv
  · inext; unfold slice_inv own_auth; iexists false; simp; iframe
  imodintro; iexists γ; isplit
  · ipureintro; exact Hdom'
  isplit; simp only [slice, own_prop]; iframe #
  inext; iexists (fun γ' => if γ' = γ then Q else Φ γ')
  isplit
  · inext; irewrite [HeqP]
    · constructor; rintro _ _ _ h
      refine (internalEq.ne_l _).ne ?_
      exact sep_ne.ne .rfl h
    · ipureintro; symm; apply bigOpM_fn_insert_eqv'; assumption
  · iapply (BI.equiv_iff.mp (bigOpM_fn_insert_eqv (fun γ b P' => iprop(own_auth γ (◯E { car := b }) ∗ own_prop γ P' ∗ inv N (slice_inv γ P'))) _ _ _ Hdom').symm)
    simp only [own_prop, own_auth, unit]; iframe HF Hγ' #

@[rocq_alias slice_delete_empty]
theorem slice_delete_empty E q f P Q γ :
  ↑N ⊆ E →
  get? f γ = some false →
  slice (GF := GF) N γ Q -∗ ▷?q box N f P ={E}=∗ ∃ P',
    ▷?q (▷ internalEq P iprop(Q ∗ P') ∗ box N (delete f γ) P') := by
  unfold slice box
  iintro %HN %Hγ ⟨#HγQ, Hinv⟩ H; icases H with ⟨%Φ, #HeqP, Hf⟩
  iexists iprop([∗map] γ' ↦ b ∈ delete f γ, Φ γ')
  iapply inv_open_fupd_strong HN $$ Hinv; iintro Hγ
  unfold slice_inv own_auth; icases Hγ with ⟨%b, >Hγ, _⟩
  -- cannot do iapply
  icases laterN_mono _ (bigSepM_delete Hγ).mp $$ Hf with ⟨⟨>Hγ', #HγΦ, #_⟩, _⟩
  icases own_auth_agree γ (.mk b) (.mk false) $$ [-] with %eq
  · unfold own_auth; iframe;
  imodintro; isplitl [Hγ]
  · iexists false; imodintro; simp; rw [eq]; iframe
  imodintro; inext; isplit
  · icases own_agree γ Q (Φ γ) $$ [] with HeqQ; iframe #
    inext; irewrite [HeqP]; exact internalEq.ne_l _
    irewrite [HeqQ]
    · constructor; rintro _ _ _ h
      refine (internalEq.ne_r _).ne ?_
      exact sep_ne.ne h .rfl
    ipureintro; apply bigOpM_delete_eqv _ Hγ
  · iexists Φ; iframe; inext; ipureintro; rfl

@[rocq_alias slice_fill]
theorem slice_fill E q f γ (P Q : IProp GF) :
  ↑N ⊆ E →
  get? f γ = some false →
  slice N γ Q -∗ ▷ Q -∗ ▷?q box N f P ={E}=∗ ▷?q box N (insert f γ true) P := by
  unfold slice box
  iintro %HN %Hγ ⟨#HγQ, Hinv⟩ HQ H; icases H with ⟨%Φ, #HeqP, Hf⟩
  iapply inv_open_fupd_strong HN $$ Hinv; iintro Hγ
  unfold slice_inv own_auth; icases Hγ with ⟨%b, >Hγ, _⟩
  icases laterN_mono _ (bigSepM_delete Hγ).mp $$ Hf with ⟨⟨>Hγ', #HγΦ, #Hinv'⟩, _⟩
  imod own_auth_update γ (.mk b) (.mk false) (.mk true) $$ [Hγ Hγ'] with ⟨Hγ, Hγ'⟩
  · unfold own_auth; iframe
  imodintro; isplitl [Hγ HQ]; inext; iexists true; unfold own_auth; simp; iframe
  imodintro; inext; iexists Φ; isplit
  · inext; irewrite [HeqP]; exact internalEq.ne_l _
    ipureintro; apply (bigOpM_insert_override_eqv Hγ _).symm; rfl
  · iapply (BI.equiv_iff.mp (bigOpM_eqv_of_perm _ insert_delete))
    iapply (BI.equiv_iff.mp (bigOpM_insert_eqv _ _ (get?_delete_eq rfl)))
    unfold own_prop own_auth; iframe; iframe #

@[rocq_alias slice_empty]
theorem slice_empty E q f (P Q : IProp GF) γ :
  ↑N ⊆ E →
  get? f γ = some true →
  slice N γ Q -∗ ▷?q box N f P ={E}=∗ ▷ Q ∗ ▷?q box N (insert f γ false) P := by
  unfold slice box
  iintro %HN %Hγ ⟨#HγQ, Hinv⟩ H; icases H with ⟨%Φ, #HeqP, Hf⟩
  iapply inv_open_fupd_strong HN $$ Hinv; iintro Hγ
  unfold slice_inv own_auth; icases Hγ with ⟨%b, >Hγ, HQ⟩
  icases laterN_mono _ (bigSepM_delete Hγ).mp $$ Hf with ⟨⟨>Hγ', #HγΦ, #Hinv'⟩, _⟩
  icases own_auth_agree γ (.mk b) (.mk true) $$ [-] with %eq
  · unfold own_auth; iframe;
  injection eq with eq; rw [eq]; simp; iframe HQ
  imod own_auth_update γ (.mk b) (.mk true) (.mk false) $$ [Hγ Hγ'] with ⟨Hγ, Hγ'⟩
  · unfold own_auth; rw [eq]; iframe
  imodintro; isplitl [Hγ]; inext; iexists false; unfold own_auth; simp; iframe
  imodintro; inext; iexists Φ; isplit
  · inext; irewrite [HeqP]; exact internalEq.ne_l _
    ipureintro; apply (bigOpM_insert_override_eqv Hγ _).symm; rfl
  · iapply (BI.equiv_iff.mp (bigOpM_eqv_of_perm _ insert_delete))
    iapply (BI.equiv_iff.mp (bigOpM_insert_eqv _ _ (get?_delete_eq rfl)))
    unfold own_prop own_auth; iframe; iframe #

private theorem box_eqv_of_perm (f₁ f₂ : SliceMap Bool) (P : IProp GF) :
  f₁ ≡ₘ f₂ →
  box N f₁ P ⊢ box N f₂ P := by
  iintro %Heqf Hbox
  unfold box; icases Hbox with ⟨%Φ, Heq, HF⟩
  iexists Φ; isplit
  · inext; irewrite [Heq]; exact internalEq.ne_l _
    ipureintro; apply (bigOpM_eqv_of_perm _ Heqf)
  · iapply (BI.equiv_iff.mp (bigOpM_eqv_of_perm _ Heqf)); iassumption

@[rocq_alias slice_insert_full]
theorem slice_insert_full E q f (P Q : IProp GF) :
  ↑N ⊆ E →
  ▷ Q -∗ ▷?q box N f P ={E}=∗ ∃ γ, ⌜get? f γ = none⌝ ∗
    slice N γ Q ∗ ▷?q box N (insert f γ true) iprop(Q ∗ P) := by
  iintro %Hsub HQ Hbox
  imod slice_insert_empty $$ Hbox with ⟨%γ, _, #Hslice, Hbox⟩
  iexists γ; iframe #; imod slice_fill $$ Hslice HQ Hbox with Hbox; assumption
  · apply get?_insert_eq; rfl
  · imodintro; iframe; inext
    iapply box_eqv_of_perm $$ Hbox
    apply insert_insert_same

@[rocq_alias slice_delete_full]
theorem slice_delete_full E q f (P Q : IProp GF) γ :
  ↑N ⊆ E →
  get? f γ = some true →
  slice N γ Q -∗ ▷?q box N f P ={E}=∗
  ∃ P', ▷ Q ∗ ▷?q ▷ internalEq P iprop(Q ∗ P') ∗ ▷?q box N (delete f γ) P' := by
  iintro %Hsub %Hsome #Hslice Hbox
  imod slice_empty $$ Hslice Hbox with ⟨HQ, Hbox⟩ <;> try assumption
  imod slice_delete_empty $$ Hslice Hbox with ⟨%P', Heq, Hbox⟩ <;> try assumption
  · apply get?_insert_eq; rfl
  iexists P'; iframe; imodintro; inext
  iapply box_eqv_of_perm $$ Hbox
  intro k; by_cases h : γ = k
  · simp only [get?_delete_eq h]
  · simp only [get?_delete_ne h, get?_insert_ne h]

@[rocq_alias box_fill]
theorem box_fill E f (P : IProp GF) :
  ↑N ⊆ E →
  box N f P -∗ ▷ P ={E}=∗ box N (Std.PartialMap.map (fun _ => true) f) P := by -- why must Std.?
  unfold box; iintro %Hsub ⟨%Φ, #HeqP, Hf⟩ HP
  iexists Φ; isplitr
  · imodintro; inext; irewrite [HeqP]; exact internalEq.ne_l _
    ipureintro; symm; apply bigOpM_map_eqv
  · ihave HeqP' := later_mono (internalEq_iff _ _) $$ HeqP
    icases later_iff $$ HeqP' with ⟨HeqP'', _⟩
    ihave HP := HeqP'' $$ HP
    ihave HP := bigSepM_later $$ HP
    icombine Hf HP as Hf
    ihave Hf := (BI.equiv_iff.mp bigSepM_sep_eqv.symm) $$ Hf
    iapply bigSepM_fupd
    iapply (BI.equiv_iff.mp (bigOpM_map_eqv ..).symm)
    iapply bigSepM_impl $$ Hf
    iintro !> %γ %b' %Hsome ⟨⟨Hγ', #$, #Hinv⟩, HΦ⟩; iframe Hinv
    iapply inv_open_fupd_strong Hsub $$ Hinv; iintro Hγ
    unfold slice_inv own_auth; icases Hγ with ⟨%b, >Hγ, HQ⟩
    imod own_auth_update γ (.mk b) (.mk b') (.mk true) $$ [Hγ Hγ'] with ⟨Hγ, Hγ'⟩
    · unfold own_auth; iframe
    imodintro; isplitr [Hγ']
    · inext; iexists true; simp; unfold own_auth; iframe
    · imodintro; unfold own_auth; iframe

@[rocq_alias box_empty]
theorem box_empty E f (P : IProp GF) :
  ↑N ⊆ E →
  (∀ γ b, get? f γ = some b → true = b) →
  box N f P ={E}=∗ ▷ P ∗ box N (Std.PartialMap.map (fun _ => false) f) P := by
  unfold box; iintro %Hsub %Htrue ⟨%Φ, #HeqP, Hf⟩
  ihave ⟨> ⟨HΦ, H⟩⟩ : (|={E}=> ([∗map] γ ↦ _b ∈ f, ▷ Φ γ) ∗
    [∗map] γ ↦ _b ∈ f, own_auth γ (◯E (.mk false)) ∗ own_prop γ (Φ γ) ∗
       inv N (slice_inv γ (Φ γ))) $$ [Hf]
  · iapply (BIFUpdate.mono (BI.equiv_iff.mp bigSepM_sep_eqv).mp)
    iapply bigSepM_fupd
    iapply bigSepM_impl $$ Hf
    iintro !> %γ %b %Hsome ⟨Hγ', #HγΦ, #Hinv⟩
    rw [←Htrue _ _ Hsome]; clear b Hsome
    iapply inv_open_fupd_strong Hsub $$ Hinv; iintro Hγ
    unfold slice_inv own_auth; icases Hγ with ⟨%b, >Hγ, HΦ⟩
    icases own_auth_agree γ (.mk b) (.mk true) $$ [-] with %eq
    · unfold own_auth; iframe
    injection eq with eq; rw [eq]; simp
    imod own_auth_update γ (.mk true) (.mk true) (.mk false) $$ [Hγ Hγ'] with ⟨Hγ, Hγ'⟩
    · unfold own_auth; iframe
    imodintro; isplitl [Hγ]
    · inext; iexists false; simp; unfold own_auth; iframe
    · imodintro; unfold own_auth; iframe; iframe #
  imodintro; isplitl [HΦ]
  · ihave HeqP' := later_mono (internalEq_iff _ _) $$ HeqP
    icases later_iff $$ HeqP' with ⟨_, HeqP''⟩
    iapply HeqP''; iapply bigSepM_later; iassumption
  · iexists Φ; isplit
    · inext; irewrite [HeqP]; exact internalEq.ne_l _
      ipureintro; symm; apply bigOpM_map_eqv
    · iapply (BI.equiv_iff.mp (bigOpM_map_eqv ..).symm)
      iassumption

@[rocq_alias slice_iff]
theorem slice_iff E q f (P Q Q' : IProp GF) γ b :
  ↑N ⊆ E → get? f γ = some b →
  ▷ □ (Q ↔ Q') -∗ slice N γ Q -∗ ▷?q box N f P ={E}=∗ ∃ γ' P',
    ⌜get? (delete f γ) γ' = none⌝ ∗ ▷?q ▷ □ (P ↔ P') ∗
    slice N γ' Q' ∗ ▷?q box N (insert (delete f γ) γ' b) P' := by
  iintro %Hsub %Hsome #HQQ' #Hs Hb; cases b
  · imod slice_delete_empty $$ Hs Hb with ⟨%P', #Heq, Hb⟩ <;> try assumption
    icases HQQ' with ⟨HQQ', HQ'Q⟩
    imod slice_insert_empty $$ Hb with ⟨%γ', %Hnone, #Hs', Hb⟩
    iexists γ', iprop(Q' ∗ P'); iframe; iframe % #; imodintro; inext; inext; imodintro
    isplit
    · irewrite [Heq]; exact imp_ne.ne_left ..
      iintro ⟨_, $⟩; iapply HQQ'; iassumption
    · irewrite [Heq]; exact imp_ne.ne_right ..
      iintro ⟨_, $⟩; iapply HQ'Q; iassumption
  · imod slice_delete_full $$ Hs Hb with ⟨%P', HQ, #Heq, Hb⟩ <;> try assumption
    icases HQQ' with ⟨HQQ', HQ'Q⟩
    ihave HQ' := HQQ' $$ HQ
    imod slice_insert_full $$ HQ' Hb with ⟨%γ', %Hnone, #Hs', Hb⟩; assumption
    iexists γ', _; iframe; iframe % #; imodintro; inext; inext; imodintro
    isplit
    · irewrite [Heq]; exact imp_ne.ne_left ..
      iintro ⟨_, $⟩; iapply HQQ'; iassumption
    · irewrite [Heq]; exact imp_ne.ne_right ..
      iintro ⟨_, $⟩; iapply HQ'Q; iassumption

@[rocq_alias slice_split]
theorem slice_split E q f (Q₁ Q₂ : IProp GF) γ b :
  ↑N ⊆ E → get? f γ = some b →
  slice N γ iprop(Q₁ ∗ Q₂) -∗ ▷?q box N f P ={E}=∗ ∃ γ₁ γ₂,
    ⌜get? (delete f γ) γ₁ = none⌝ ∗ ⌜get? (delete f γ) γ₂ = none⌝ ∗ ⌜γ₁ ≠ γ₂⌝ ∗
    slice N γ₁ Q₁ ∗ slice N γ₂ Q₂ ∗ ▷?q box N (insert (insert (delete f γ) γ₁ b) γ₂ b) P := by
  iintro %Hsub %Hsome #Hslice Hbox
  cases b
  · imod slice_delete_empty $$ Hslice Hbox with ⟨%P', Heq, Hbox⟩ <;> try assumption
    imod slice_insert_empty $$ Hbox with ⟨%γ₁, %Hnone1, #Hslice1, Hbox⟩
    imod slice_insert_empty $$ Hbox with ⟨%γ₂, %Hnone2, #Hslice2, Hbox⟩
    iexists γ₁, γ₂; iframe # %; imodintro; isplit <;> try isplit
    · ipureintro; exact (get?_insert_none_iff.mp Hnone2).1
    · ipureintro; exact (get?_insert_none_iff.mp Hnone2).2
    inext; iapply (internalEq_rewrite_contractive _ _ (box _ _)) $$ [Heq] Hbox
    inext; irewrite [Heq]; exact internalEq.ne_r _
    ipureintro; rw [←sep_assoc.to_eq]
    refine NonExpansive₂.eqv ?_ .rfl; rw [sep_comm.to_eq]
  · imod slice_delete_full $$ Hslice Hbox with ⟨%P', ⟨HQ₁, HQ₂⟩, Heq, Hbox⟩ <;> try assumption
    imod slice_insert_full $$ HQ₁ Hbox with ⟨%γ₁, %Hnone1, #Hslice1, Hbox⟩; assumption
    imod slice_insert_full $$ HQ₂ Hbox with ⟨%γ₂, %Hnone2, #Hslice2, Hbox⟩; assumption
    iexists γ₁, γ₂; iframe # %; imodintro; isplit <;> try isplit
    · ipureintro; exact (get?_insert_none_iff.mp Hnone2).1
    · ipureintro; exact (get?_insert_none_iff.mp Hnone2).2
    inext; iapply (internalEq_rewrite_contractive _ _ (box _ _)) $$ [Heq] Hbox
    inext; irewrite [Heq]; exact internalEq.ne_r _
    ipureintro; rw [←sep_assoc.to_eq]
    refine NonExpansive₂.eqv ?_ .rfl; rw [sep_comm.to_eq]

@[rocq_alias slice_combine]
theorem slice_combine E q f (Q₁ Q₂ : IProp GF) γ₁ γ₂ b :
  ↑N ⊆ E → γ₁ ≠ γ₂ → get? f γ₁ = some b → get? f γ₂ = some b →
  slice N γ₁ Q₁ -∗ slice N γ₂ Q₂ -∗ ▷?q box N f P ={E}=∗ ∃ γ,
    ⌜get? (delete (delete f γ₁) γ₂) γ = none⌝ ∗ slice N γ iprop(Q₁ ∗ Q₂) ∗
    ▷?q box N (insert (delete (delete f γ₁) γ₂) γ b) P := by
  iintro %Hsub %Hne %Hsome1 %Hsome2 #Hslice1 #Hslice2 Hbox; cases b
  · imod slice_delete_empty $$ Hslice1 Hbox with ⟨%P1, Heq1, Hbox⟩ <;> try assumption
    imod slice_delete_empty $$ Hslice2 Hbox with ⟨%P2, Heq2, Hbox⟩ <;> try assumption
    · apply get?_delete_some_iff.mpr; trivial
    imod slice_insert_empty $$ Hbox with ⟨%γ, %Hnone, #Hslice, Hbox⟩
    iexists γ; iframe # %; imodintro; inext
    iapply (internalEq_rewrite_contractive _ _ (box _ _)) $$ [Heq1 Heq2] Hbox
    inext; irewrite [Heq1]; exact internalEq.ne_r _
    irewrite [Heq2]
    · constructor; rintro _ _ _ h;
      refine (internalEq.ne_r _).ne ?_;
      exact (sep_ne.ne .rfl h)
    ipureintro; rw [sep_assoc.to_eq];
  · imod slice_delete_full $$ Hslice1 Hbox with ⟨%P1, HQ1, Heq1, Hbox⟩ <;> try assumption
    imod slice_delete_full $$ Hslice2 Hbox with ⟨%P2, HQ2, Heq2, Hbox⟩ <;> try assumption
    · apply get?_delete_some_iff.mpr; trivial
    imod slice_insert_full _ _ _ _ _ iprop(Q₁ ∗ Q₂) $$ [$HQ1 $HQ2] Hbox with
      ⟨%γ, %Hnone, #Hslice, Hbox⟩; assumption
    iexists γ; iframe # %; imodintro; inext
    iapply (internalEq_rewrite_contractive _ _ (box _ _)) $$ [Heq1 Heq2] Hbox
    inext; irewrite [Heq1]; exact internalEq.ne_r _
    irewrite [Heq2]
    · constructor; rintro _ _ _ h;
      refine (internalEq.ne_r _).ne ?_;
      exact (sep_ne.ne .rfl h)
    ipureintro; rw [sep_assoc.to_eq];

end Lemmas
