/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.BI.Extensions
public import Iris.BI.Sbi
public import Iris.ProofMode
public import Iris.ProofMode.Classes
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

open Iris.Std BI ProofMode

namespace AffineEM

variable {PROP : Type _} [BI PROP]
variable (em : ∀ P : PROP, ⊢ P ∨ ¬P)
variable (P Q : PROP)
include em

@[rocq_alias affine_em.sep_dup]
theorem sep_dup [Affine P] : P ⊢ P ∗ P := by
  iintro HP
  icases (em P) with (HP' | HnotP)
  · iframe HP HP'
  · iexfalso
    iapply HnotP $$ HP

@[rocq_alias affine_em.and_sep]
theorem and_sep [BIAffine PROP] : P ∧ Q ⊢ P ∗ Q := by
  iintro HPQ
  icases sep_dup $$ HPQ with ⟨HPQ, HPQ'⟩
  · assumption
  · isplitl [HPQ]
    · icases HPQ with ⟨HP, -⟩
      iassumption
    · icases HPQ' with ⟨-, HQ⟩
      iassumption

end AffineEM

namespace LoebEM

@[rocq_alias löb_em.later_anything]
theorem later_anything [BI PROP] (em : ∀ P : PROP, ⊢ P ∨ ¬P) [BILoeb PROP] :
    ⊢@{PROP} ▷ P := by
  icases (em iprop(▷ False)) with #(HP | HnotP)
  · inext
    iexfalso
    iassumption
  · iexfalso
    iloeb as IH
    ispecialize HnotP $$ IH
    iassumption

@[rocq_alias löb_em.later_inconsistent]
theorem later_inconsistent [Sbi PROP] (em : ∀ P : PROP, ⊢ P ∨ ¬P) : ⊢@{PROP} False := by
  apply later_soundness (PROP := PROP) (P := iprop(False))
  apply later_anything
  assumption

end LoebEM

namespace SavedProp

variable [BI PROP] [instAffine : BIAffine PROP] {P Q : PROP}
variable (bupd : PROP → PROP)
variable (ident : Type _) (saved : ident → PROP → PROP)
variable [instPers : ∀ (i : ident) (P : PROP), Persistent (saved i P)]

variable (bupd_intro : ∀ {P : PROP}, P ⊢ bupd P)
variable (bupd_mono : ∀ {P Q : PROP}, (P ⊢ Q) → bupd P ⊢ bupd Q)
variable (bupd_trans : ∀ {P : PROP}, bupd (bupd P) ⊢ bupd P)
variable (bupd_frame_right : ∀ {P R : PROP}, bupd P ∗ R ⊢ bupd iprop(P ∗ R))
variable (sprop_alloc_dep : ∀ {P : ident → PROP}, ⊢ bupd (∃ i, saved i (P i)))
variable (sprop_agree : ∀ (i : ident) (P Q : PROP), saved i P ∧ saved i Q ⊢ □ (P ↔ Q))
variable (consistency : ¬(⊢ bupd iprop(False)))

include bupd_mono in
omit instAffine in
@[rw_mono_rule, rocq_alias savedprop.bupd_mono']
theorem bupd_mono' (h : P ⊢ Q) : bupd P ⊢ bupd Q := bupd_mono h

include bupd_frame_right bupd_trans bupd_mono in
omit instAffine in
@[rocq_alias savedprop.elim_modal_bupd]
theorem elim_modal_bupd (p : Bool) : ElimModal True p io false (bupd P) P (bupd Q) (bupd Q) where
  elim_modal _ := calc
    _ ⊢ bupd P ∗ (P -∗ bupd Q)        := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ bupd iprop(P ∗ (P -∗ bupd Q)) := bupd_frame_right
    _ ⊢ bupd (bupd Q)                 := bupd_mono wand_elim_right
    _ ⊢ bupd Q                        := bupd_trans

@[reducible, rocq_alias savedprop.A]
def A (i : ident) : PROP := iprop(∃ P, □ (¬P ∗ saved i P))

include sprop_alloc_dep in
omit instAffine instPers in
@[rocq_alias savedprop.A_alloc]
theorem A_alloc : ⊢ bupd (∃ i, saved i (A ident saved i)) := sprop_alloc_dep

include sprop_agree in
@[rocq_alias savedprop.saved_NA]
theorem saved_NA (i : ident) : saved i (A ident saved i) ⊢ ¬A ident saved i := by
  iintro #Hs #HA
  ihave ⟨%P, HNP, HsP⟩ := HA
  iapply HNP
  icases sprop_agree i P (A ident saved i) $$ [] with #⟨_, HP⟩
  · isplit <;> iassumption
  · iapply HP; iassumption

include sprop_agree in
@[rocq_alias savedprop.saved_A]
theorem saved_A (i : ident) : saved i (A ident saved i) ⊢ A ident saved i := by
  iintro #Hs
  iexists A ident saved i
  iintro {$Hs} !>
  iapply saved_NA
  · exact sprop_agree
  · iassumption

include consistency bupd_frame_right bupd_intro bupd_trans bupd_mono sprop_alloc_dep sprop_agree in
@[rocq_alias savedprop.contradiction]
theorem contradiction : False := by
  haveI {p : Bool} {P Q : PROP} : ElimModal True p .out false (bupd P) P (bupd Q) (bupd Q) :=
    elim_modal_bupd (io := .out) bupd bupd_mono bupd_trans bupd_frame_right p
  apply consistency
  imod A_alloc bupd ident saved sprop_alloc_dep with ⟨%i, #H⟩
  iapply bupd_intro
  iapply saved_NA _ $$ H
  · exact sprop_agree
  · iapply saved_A
    · exact sprop_agree
    · iassumption

end SavedProp

namespace Inv

@[rocq_alias inv.mask]
inductive Mask where | M0 | M1 deriving DecidableEq, Inhabited

open Mask

variable {PROP : Type _} [BI PROP] [instAffine : BIAffine PROP] [instBFupd : BIFUpdate PROP]
variable {P Q R : PROP}
variable (fupd : Mask → PROP → PROP)
variable (name : Type _) (inv : name → PROP → PROP)
variable [∀ (i : name) (P : PROP), Persistent (inv i P)]

variable (fupd_intro : ∀ {E : Mask} {P : PROP}, P ⊢ fupd E P)
variable (fupd_mono : ∀ {E : Mask} {P Q : PROP}, (P ⊢ Q) → fupd E P ⊢ fupd E Q)
variable (fupd_fupd : ∀ {E : Mask} {P : PROP}, fupd E (fupd E P) ⊢ fupd E P)
variable (fupd_frame_left : ∀ {E : Mask} {P Q : PROP}, P ∗ fupd E Q ⊢ fupd E iprop(P ∗ Q))
variable (fupd_mask_mono : ∀ {P : PROP}, fupd M0 P ⊢ fupd M1 P)
variable (inv_alloc : ∀ P : PROP, P ⊢ fupd M1 (∃ i, inv i P))
variable (inv_fupd :
  ∀ {i : name} (P Q R : PROP), (P ∗ Q ⊢ fupd M0 iprop(P ∗ R)) → inv i P ∗ Q ⊢ fupd M1 R)
variable (consistency : ¬(⊢ fupd M1 iprop(False)))

include fupd_fupd inv_fupd in
omit instBFupd in
@[rocq_alias inv.inv_fupd']
theorem inv_fupd' (i : name) : inv i P ∗ (P -∗ fupd M0 iprop(P ∗ fupd M1 R)) ⊢ fupd M1 R := by
  iintro ⟨#HiP, HP⟩
  iapply fupd_fupd
  iapply inv_fupd P iprop(P -∗ fupd M0 iprop(P ∗ fupd M1 R))
  · iintro ⟨HP, HPw⟩
    iapply HPw $$ HP
  · iframe HiP HP

include fupd_mono in
omit instAffine instBFupd in
@[rw_mono_rule, rocq_alias inv.fupd_mono']
theorem fupd_mono' (E : Mask) (h : P ⊢ Q) : fupd E P ⊢ fupd E Q := fupd_mono h

include fupd_mono in
omit instAffine instBFupd in
@[rocq_alias inv.fupd_proper]
theorem fupd_proper (E : Mask) (h : P ⊣⊢ Q) : fupd E P ⊣⊢ fupd E Q :=
  ⟨fupd_mono h.mp, fupd_mono h.mpr⟩

include fupd_mono fupd_frame_left in
omit instAffine instBFupd in
@[rocq_alias inv.fupd_frame_r]
theorem fupd_frame_right (E : Mask) : fupd E P ∗ Q ⊢ fupd E iprop(P ∗ Q) :=
  sep_comm.mp.trans <| fupd_frame_left.trans <| fupd_mono sep_comm.mp

include fupd_mono fupd_frame_left fupd_fupd in
omit instAffine instBFupd in
@[rocq_alias inv.elim_fupd_fupd]
theorem elim_fupd_fupd (p : Bool) (E : Mask) :
    ElimModal True p io false (fupd E P) P (fupd E Q) (fupd E Q) where
  elim_modal _ := calc
    _ ⊢ fupd E P ∗ (P -∗ fupd E Q)        := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ fupd E iprop(P ∗ (P -∗ fupd E Q)) := fupd_frame_right fupd fupd_mono fupd_frame_left _
    _ ⊢ fupd E (fupd E Q)                 := fupd_mono wand_elim_right
    _ ⊢ fupd E Q                          := fupd_fupd

include fupd_mono fupd_frame_left fupd_fupd fupd_mask_mono in
omit instAffine instBFupd in
@[rocq_alias inv.elim_fupd0_fupd1]
theorem elim_fupd0_fupd1 (p : Bool) :
    ElimModal True p io false (fupd M0 P) P (fupd M1 Q) (fupd M1 Q) where
  elim_modal _ := calc
    _ ⊢ fupd M0 P ∗ (P -∗ fupd M1 Q)        := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ fupd M1 P ∗ (P -∗ fupd M1 Q)        := sep_mono_left fupd_mask_mono
    _ ⊢ fupd M1 iprop(P ∗ (P -∗ fupd M1 Q)) := fupd_frame_right fupd fupd_mono fupd_frame_left _
    _ ⊢ fupd M1 (fupd M1 Q)                 := fupd_mono wand_elim_right
    _ ⊢ fupd M1 Q                           := fupd_fupd

include fupd_mono in
omit instAffine instBFupd in
@[rocq_alias inv.exists_split_fupd0]
theorem exists_split_fupd0 {α : Type _} (E : Mask) (Φ : α → PROP) [inst : FromExists P Φ] :
    FromExists (fupd E P) (fun a => fupd E (Φ a)) where
  from_exists :=
    exists_elim <| fun h => fupd_mono <| (exists_intro h).trans inst.from_exists

section Inv1

variable (gname : Type _) (start finished : gname → PROP)

variable (sts_alloc : ⊢ fupd M0 (∃ γ, start γ))
variable (start_finish : ∀ γ, start γ ⊢ fupd M0 (finished γ))
variable (finished_not_start : ∀ γ, start γ ∗ finished γ ⊢ (False : PROP))
variable (finished_dup : ∀ γ, finished γ ⊢ finished γ ∗ finished γ)

@[reducible, rocq_alias inv.saved]
def saved (γ : gname) (P : PROP) : PROP :=
  iprop(∃ i, inv i iprop(start γ ∨ iprop(finished γ ∗ □ P)))

omit instAffine instBFupd in
@[rocq_alias inv.saved_persistent]
theorem saved_persistent (γ : gname) (P : PROP) :
    Persistent (saved name inv gname start finished γ P) := by infer_instance

include sts_alloc fupd_mono fupd_intro fupd_fupd fupd_frame_left fupd_mask_mono inv_alloc in
omit instBFupd in
@[rocq_alias inv.saved_alloc]
theorem saved_alloc (P : gname → PROP) :
    ⊢ fupd M1 iprop(∃ γ, saved name inv gname start finished γ (P γ)) := by
  haveI {p : Bool} {P Q : PROP} :
      ElimModal True p .out false (fupd M0 P) P (fupd M1 Q) (fupd M1 Q) :=
    elim_fupd0_fupd1 fupd fupd_mono fupd_fupd fupd_frame_left fupd_mask_mono p
  haveI {p : Bool} {E : Mask} {P Q : PROP} :
      ElimModal True p .out false (fupd E P) P (fupd E Q) (fupd E Q) :=
    elim_fupd_fupd fupd fupd_mono fupd_fupd fupd_frame_left p E
  imod sts_alloc with ⟨%γ, Hs⟩
  imod inv_alloc iprop(start γ ∨ finished γ ∗ □ (P γ)) $$ [Hs] with ⟨%i, #Hi⟩
  · ileft; iassumption
  · iapply fupd_intro
    iexists γ, i; iassumption

include fupd_intro fupd_mono fupd_fupd fupd_frame_left inv_fupd
  start_finish finished_not_start finished_dup in
omit instBFupd in
@[rocq_alias inv.saved_cast]
theorem saved_cast (γ : gname) :
    saved name inv gname start finished γ P ∗
    saved name inv gname start finished γ Q ∗ □ P ⊢ fupd M1 iprop(□ Q) := by
  haveI {p : Bool} {E : Mask} {P Q : PROP} :
      ElimModal True p .out false (fupd E P) P (fupd E Q) (fupd E Q) :=
    elim_fupd_fupd fupd fupd_mono fupd_fupd fupd_frame_left p E
  iintro ⟨#⟨%i, HiP⟩, #HsQ, #HP⟩
  iapply inv_fupd' fupd name inv fupd_fupd inv_fupd i
  · isplit
    · iexact HiP
    · iintro HaP
      ihave >Hf : fupd M0 (finished γ) $$ [HaP]
      · icases HaP with (Hs | ⟨Hf, -⟩)
        · iapply start_finish; iexact Hs
        · iapply fupd_intro; iexact Hf
      icases finished_dup γ $$ Hf with ⟨Hf, Hf'⟩
      iapply fupd_intro
      isplitl [Hf']
      · iright; iframe Hf' HP
      · iclear HiP
        icases HsQ with ⟨%j, HiQ⟩
        iapply inv_fupd' fupd name inv fupd_fupd inv_fupd j
        isplit
        · iexact HiQ
        · iintro (HaQ | ⟨-, #HQ⟩)
          · iexfalso
            iapply finished_not_start γ
            iframe HaQ Hf
          · iapply fupd_intro
            isplitl [Hf]
            · iright; iframe Hf HQ
            · iapply fupd_intro; iexact HQ

@[reducible]
def notFUpd (P : PROP) : PROP := iprop(□ (P -∗ fupd M1 iprop(False)))

@[reducible, rocq_alias inv.A]
def A (i : gname) : PROP :=
  iprop(∃ P, notFUpd fupd P ∗ saved name inv gname start finished i P)

@[rocq_alias inv.A_persistent]
instance A_persistent (i : gname) :
    Persistent (A fupd name inv gname start finished i) := by infer_instance

include sts_alloc fupd_intro fupd_mono fupd_fupd fupd_frame_left fupd_mask_mono inv_alloc in
omit instBFupd in
@[rocq_alias inv.A_alloc]
theorem A_alloc :
    ⊢ fupd M1 (∃ i, saved name inv gname start finished i
      (A fupd name inv gname start finished i)) :=
  saved_alloc fupd name inv fupd_intro fupd_mono fupd_fupd fupd_frame_left fupd_mask_mono
    inv_alloc gname start finished sts_alloc
    (P := fun i => A fupd name inv gname start finished i)

include fupd_intro fupd_mono fupd_fupd fupd_frame_left inv_fupd
  start_finish finished_not_start finished_dup in
omit instBFupd in
@[rocq_alias inv.saved_NA]
theorem saved_NA (i : gname) :
    saved name inv gname start finished i (A fupd name inv gname start finished i) ⊢
      notFUpd fupd (A fupd name inv gname start finished i) := by
  haveI {p : Bool} {E : Mask} {P Q : PROP} :
      ElimModal True p .out false (fupd E P) P (fupd E Q) (fupd E Q) :=
    elim_fupd_fupd fupd fupd_mono fupd_fupd fupd_frame_left p E
  iintro #Hi !> #HA
  ihave ⟨%P', HNP, Hi'⟩ := HA
  imod saved_cast fupd name inv fupd_intro fupd_mono fupd_fupd fupd_frame_left
    inv_fupd gname start finished start_finish finished_not_start finished_dup
    (P := A fupd name inv gname start finished i) (Q := P') i $$ [] with HP
  · iframe #
  · iapply HNP; iassumption

include fupd_intro fupd_mono fupd_fupd fupd_frame_left inv_fupd
  start_finish finished_not_start finished_dup in
omit instBFupd in
@[rocq_alias inv.saved_A]
theorem saved_A (i : gname) :
    saved name inv gname start finished i (A fupd name inv gname start finished i) ⊢
      A fupd name inv gname start finished i := by
  iintro #Hi
  iexists A fupd name inv gname start finished i
  iframe Hi
  iapply saved_NA fupd name inv fupd_intro fupd_mono fupd_fupd fupd_frame_left
    inv_fupd gname start finished start_finish finished_not_start finished_dup i
  iexact Hi

include fupd_intro fupd_mono fupd_fupd fupd_frame_left fupd_mask_mono
  inv_alloc inv_fupd consistency sts_alloc start_finish finished_not_start finished_dup in
omit instBFupd in
@[rocq_alias inv.contradiction]
theorem contradiction : False := by
  apply consistency
  haveI {p : Bool} {E : Mask} {P Q : PROP} :
      ElimModal True p .out false (fupd E P) P (fupd E Q) (fupd E Q) :=
    elim_fupd_fupd fupd fupd_mono fupd_fupd fupd_frame_left p E
  imod A_alloc fupd name inv fupd_intro fupd_mono fupd_fupd fupd_frame_left fupd_mask_mono
    inv_alloc gname start finished sts_alloc with ⟨%i, #H⟩
  ihave HN := saved_NA fupd name inv fupd_intro fupd_mono fupd_fupd fupd_frame_left
    inv_fupd gname start finished start_finish finished_not_start finished_dup i $$ [H]
  · iexact H
  · iapply HN
    iapply saved_A fupd name inv fupd_intro fupd_mono fupd_fupd fupd_frame_left
      inv_fupd gname start finished start_finish finished_not_start finished_dup i
    iassumption

end Inv1

section Inv2

variable {gname : Type _} (start finished : gname → PROP)
variable [∀ γ, Persistent (finished γ)]

variable (sts_alloc : ⊢ fupd M0 (∃ γ, start γ))
variable (start_finish : ∀ γ, start γ ⊢ fupd M0 (finished γ))
variable (finished_not_start : ∀ γ, start γ ∗ finished γ ⊢ (False : PROP))

@[reducible, rocq_alias inv.B]
def B : PROP := iprop(□ fupd M1 iprop(False))

@[reducible, rocq_alias inv.P]
def P' (γ : gname) : PROP := iprop(start γ ∨ B fupd)

@[reducible, rocq_alias inv.I]
def I (i : name) (γ : gname) : PROP := inv i (P' fupd start γ)

include fupd_intro fupd_fupd inv_fupd finished_not_start in
omit instBFupd in
@[rocq_alias inv.finished_contradiction]
theorem finished_contradiction (γ : gname) (i : name) :
    finished γ ∗ I fupd name inv start i γ ⊢ B fupd := by
  iintro ⟨#Hfin, #Hi⟩ !>
  iapply inv_fupd' fupd name inv fupd_fupd inv_fupd i
  isplit
  · iexact Hi
  · iintro (Hstart | #Hfalse)
    · iexfalso
      iapply finished_not_start γ
      iframe Hstart Hfin
    · iapply fupd_intro
      isplitl []
      · iright; iexact Hfalse
      · iexact Hfalse

include fupd_intro fupd_mono fupd_fupd fupd_frame_left inv_fupd
  start_finish finished_not_start in
omit instBFupd in
@[rocq_alias inv.invariant_contradiction]
theorem invariant_contradiction {γ : gname} {i : name} :
    I fupd name inv start i γ ⊢ B fupd := by
  haveI {p : Bool} {E : Mask} {P Q : PROP} :
      ElimModal True p .out false (fupd E P) P (fupd E Q) (fupd E Q) :=
    elim_fupd_fupd fupd fupd_mono fupd_fupd fupd_frame_left p E
  iintro #Hi !>
  iapply inv_fupd' fupd name inv fupd_fupd inv_fupd i
  isplit
  · iexact Hi
  · iintro HP
    ihave >#Hfalse : fupd M0 (B fupd) $$ [HP]
    · icases HP with (Hstart | #Hfalse)
      · imod start_finish γ $$ [Hstart] with Hfin
        iexact Hstart
        iapply fupd_intro
        iapply finished_contradiction fupd name inv
          fupd_intro fupd_fupd inv_fupd start finished finished_not_start γ i
        iframe Hfin Hi
      · iapply fupd_intro; iexact Hfalse
    · iapply fupd_intro
      isplitl []
      · iright; iexact Hfalse
      · iexact Hfalse

include fupd_intro fupd_mono fupd_fupd fupd_frame_left fupd_mask_mono
  inv_alloc inv_fupd consistency sts_alloc start_finish finished_not_start in
omit instBFupd in
@[rocq_alias inv.contradiction']
theorem contradiction' : False := by
  apply consistency
  haveI {p : Bool} {P Q : PROP} :
      ElimModal True p .out false (fupd M0 P) P (fupd M1 Q) (fupd M1 Q) :=
    elim_fupd0_fupd1 fupd fupd_mono fupd_fupd fupd_frame_left fupd_mask_mono p
  haveI {p : Bool} {E : Mask} {P Q : PROP} :
      ElimModal True p .out false (fupd E P) P (fupd E Q) (fupd E Q) :=
    elim_fupd_fupd fupd fupd_mono fupd_fupd fupd_frame_left p E
  imod sts_alloc with ⟨%γ, Hstart⟩
  imod inv_alloc (P' fupd start γ) $$ [Hstart] with ⟨%i, Hi⟩
  · ileft; iassumption
  · ihave #HB := invariant_contradiction fupd name inv
      fupd_intro fupd_mono fupd_fupd fupd_frame_left inv_fupd
      start finished start_finish finished_not_start $$ [Hi] <;> iassumption

end Inv2

end Inv

namespace Linear

@[rocq_alias linear.mask]
inductive Mask where | M0 | M1 deriving DecidableEq, Inhabited

variable {PROP : Type _} [BI PROP]
variable {P Q : PROP}
variable (fupd : Mask → Mask → PROP → PROP)
variable (gname : Type _) (cinv : gname → PROP → PROP) (cinv_own : gname → PROP)

variable (fupd_intro : ∀ {E : Mask} {P : PROP}, P ⊢ fupd E E P)
variable (fupd_mono : ∀ {E1 E2 : Mask} {P Q : PROP}, (P ⊢ Q) → fupd E1 E2 P ⊢ fupd E1 E2 Q)
variable (fupd_fupd :
  ∀ {E1 E2 E3 : Mask} {P : PROP}, fupd E1 E2 (fupd E2 E3 P) ⊢ fupd E1 E3 P)
variable (fupd_frame_left :
  ∀ {E1 E2 : Mask} {P Q : PROP}, P ∗ fupd E1 E2 Q ⊢ fupd E1 E2 iprop(P ∗ Q))
variable (cinv_alloc : ∀ {E : Mask} (P : PROP), ▷ P ⊢ fupd E E iprop(∃ γ, cinv γ P ∗ cinv_own γ))
variable (cinv_acc :
  ∀ (P : PROP) (γ : gname), cinv γ P -∗ cinv_own γ -∗
    fupd M1 M0 iprop(▷ P ∗ cinv_own γ ∗ (▷ P -∗ fupd M0 M1 (emp : PROP))))

include fupd_mono in
@[rw_mono_rule, rocq_alias linear.fupd_mono']
theorem fupd_mono' {E1 E2 : Mask} (h : P ⊢ Q) : fupd E1 E2 P ⊢ fupd E1 E2 Q := fupd_mono h

include fupd_mono in
@[rocq_alias linear.fupd_proper]
theorem fupd_proper {E1 E2 : Mask} (h : P ⊣⊢ Q) : fupd E1 E2 P ⊣⊢ fupd E1 E2 Q := by
  constructor
  · apply fupd_mono h.mp
  · apply fupd_mono h.mpr

include fupd_frame_left fupd_mono in
@[rocq_alias linear.fupd_frame_r]
theorem fupd_frame_right {E1 E2 : Mask} : fupd E1 E2 P ∗ Q ⊢ fupd E1 E2 iprop(P ∗ Q) := calc
  _ ⊢ Q ∗ fupd E1 E2 P        := sep_comm.mp
  _ ⊢ fupd E1 E2 iprop(Q ∗ P) := fupd_frame_left
  _ ⊢ fupd E1 E2 iprop(P ∗ Q) := fupd_mono sep_comm.mp

include fupd_frame_left fupd_mono fupd_fupd in
@[rocq_alias linear.elim_fupd_fupd]
theorem elim_fupd_fupd {p : Bool} {E1 E2 E3 : Mask} :
    ElimModal True p io false (fupd E1 E2 P) P (fupd E1 E3 Q) (fupd E2 E3 Q) where
  elim_modal _ := calc
    _ ⊢ fupd E1 E2 P ∗ (P -∗ fupd E2 E3 Q)        := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ fupd E1 E2 iprop(P ∗ (P -∗ fupd E2 E3 Q)) := fupd_frame_right fupd fupd_mono fupd_frame_left
    _ ⊢ fupd E1 E2 (fupd E2 E3 Q)                 := fupd_mono wand_elim_right
    _ ⊢ fupd E1 E3 Q                              := fupd_fupd

include cinv_alloc cinv_acc fupd_mono fupd_fupd fupd_frame_left in
@[rocq_alias linear.leak]
theorem leak : P ⊢ fupd M1 M1 (emp : PROP) := by
  haveI {p : Bool} {E1 E2 E3 : Mask} {P Q : PROP} :
      ElimModal True p .out false (fupd E1 E2 P) P (fupd E1 E3 Q) (fupd E2 E3 Q) :=
    elim_fupd_fupd (io := .out) fupd fupd_mono fupd_fupd fupd_frame_left
  iintro HP
  imod cinv_alloc iprop(True) $$ [//] with ⟨%γ, Hinv, Htok⟩
  imod cinv_acc $$ Hinv Htok with ⟨Htrue, Htok, Hclose⟩
  iapply Hclose
  iassumption

end Linear

namespace LaterCreditsPlain

variable [instSbi : Sbi PROP] [instBFupd : BIFUpdate PROP]
variable {lc : PROP}

variable (lc_fupd_elim_later : ∀ E P, lc ∗ ▷ P ⊢ |={E}=> P)
variable (lc_soundness : ∀ P [Plain P] E, (lc ⊢ |={E}=> P) → ⊢ P)

variable (fupd_keep_si_pure' : ∀ {E : CoPset} (E' : CoPset) (Pi : SiProp) (R : PROP),
  (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R)

include lc_fupd_elim_later fupd_keep_si_pure' in
@[rocq_alias later_credits_plain.lc_fupd_elim_later_keep]
theorem lc_fupd_elim_later_keep {E : CoPset} {P : PROP} [inst1 : Plain P] [inst2 : Absorbing P] :
    ⊢ lc -∗ ▷ P ={E}=∗ lc ∗ P := by
  iintro Hlc HP
  iapply fupd_keep_si_pure' E iprop(<si_emp_valid> P)
  isplit
  · iapply lc_fupd_elim_later
    iintro {$Hlc} !>
    exact Plain.plain
  · iintro HP' !> {$Hlc} {HP}
    exact siPure_siEmpValid_elim

omit instBFupd in
@[rocq_alias later_credits_plain.laterN_False]
theorem laterN_False [BILoeb PROP] : ⊢@{PROP} ∃ n, ▷^[n] False := by
  iloeb as IH
  icases IH with ⟨%n, Hn⟩
  iexists n + 1
  dsimp [BIBase.laterN, Nat.repeat]
  iassumption

include lc_fupd_elim_later lc_soundness fupd_keep_si_pure' in
@[rocq_alias later_credits_plain.contradiction]
theorem contradiction [BILoeb PROP] : False := by
  apply pure_soundness (PROP := PROP)
  apply lc_soundness _ ⊤
  iintro Hlc
  icases laterN_False with ⟨%n, ∗Hfalse⟩
  icases affinely_elim $$ Hfalse with Hfalse
  iinduction n with
  | zero =>
    dsimp [BIBase.laterN, Nat.repeat]
    iexfalso; iexact Hfalse
  | succ n IH =>
    ihave Hfalse := Hfalse
    /- Necessary to unfold `▷^[n + 1]` as `▷ ▷^[n]`, or else we get
       `∗Hfalse : ▷^[n + 1] False` after `imod`. -/
    icases (later_laterN n).mp $$ Hfalse with Hfalse
    imod lc_fupd_elim_later_keep
      lc_fupd_elim_later fupd_keep_si_pure' $$ Hlc Hfalse with ⟨Hlc, Hfalse⟩
    iapply IH $$ Hlc Hfalse

end LaterCreditsPlain
