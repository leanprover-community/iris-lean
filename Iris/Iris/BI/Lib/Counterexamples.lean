/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

/-! # Counterexamples for overly strong separation-logic principles -/

namespace Iris
open BI ProofMode

namespace AffineEM

variable {PROP : Type _} [BI PROP] (em : ∀ P : PROP, ⊢ iprop(P ∨ ¬ P))
include em

@[rocq_alias affine_em.sep_dup]
theorem sep_dup (P : PROP) [Affine P] : P -∗ P ∗ P := by
  iintro HP
  icases em P with #(HP' | HnotP)
  · iframe HP HP'
  · iexfalso
    iapply HnotP
    iexact HP

@[rocq_alias affine_em.and_sep]
theorem and_sep [BIAffine PROP] (P Q : PROP) : P ∧ Q -∗ P ∗ Q := by
  iintro HPQ
  icases sep_dup em iprop(P ∧ Q) $$ HPQ with ⟨HPQ, HPQ'⟩
  icases HPQ with ⟨HP, -⟩
  icases HPQ' with ⟨-, HQ⟩
  iframe HP HQ

end AffineEM

namespace LoebEM

variable {PROP : Type _}

@[rocq_alias löb_em.later_anything]
theorem later_anything [BI PROP] (em : ∀ P : PROP, ⊢ iprop(P ∨ ¬ P))
    [BILoeb PROP] (P : PROP) :
    ⊢ iprop(▷ P) := by
  icases em iprop(▷ False) with #(HP | HnotP)
  · inext
    iexfalso
    iexact HP
  · iexfalso
    iloeb as IH
    iapply imp_elim_left
    iframe HnotP IH

@[rocq_alias löb_em.later_inconsistent]
theorem later_inconsistent [Sbi PROP] (em : ∀ P : PROP, ⊢ iprop(P ∨ ¬ P)) :
    ⊢@{PROP} False :=
  later_soundness (later_anything em iprop(False))

end LoebEM

namespace SavedProp

structure SavedPropAxioms PROP [BI PROP] where
  bupd : PROP → PROP
  bupdIntro : ∀ P, P ⊢ bupd P
  bupdMono : ∀ P Q, (P ⊢ Q) → bupd P ⊢ bupd Q
  bupdTrans : ∀ P, bupd (bupd P) ⊢ bupd P
  bupdFrameRight : ∀ P R, bupd P ∗ R ⊢ bupd iprop(P ∗ R)
  ident : Type u
  saved : ident → PROP → PROP
  [spropPersistent : ∀ i P, Persistent (saved i P)]
  spropAllocDep : ∀ P : ident → PROP, ⊢ bupd iprop(∃ i, saved i (P i))
  spropAgree : ∀ i P Q, saved i P ∧ saved i Q ⊢ iprop(□ (P ↔ Q))
  consistency : ¬(⊢ bupd iprop(False))

attribute [instance] SavedPropAxioms.spropPersistent

variable {PROP : Type _} [BI PROP]

#rocq_ignore savedprop.bupd_mono' "Use explicit `bupdMono` directly."

@[rocq_alias savedprop.elim_modal_bupd]
local instance elim_modal_bupd {axioms : SavedPropAxioms PROP}
    (p : Bool) (io : InOut) (P Q : PROP) :
    ElimModal True p io false (axioms.bupd P) P (axioms.bupd Q) (axioms.bupd Q) := by
  exact ⟨fun _ ↦
    (sep_mono_left intuitionisticallyIf_elim).trans <|
      (axioms.bupdFrameRight P _).trans <|
        (axioms.bupdMono _ _ wand_elim_right).trans <| axioms.bupdTrans Q⟩

@[rocq_alias savedprop.A]
def a {axioms : SavedPropAxioms PROP} (i : axioms.ident) : PROP :=
  iprop(∃ P, □ (¬ P ∗ axioms.saved i P))

@[rocq_alias savedprop.A_alloc]
theorem a_alloc {axioms : SavedPropAxioms PROP} :
    ⊢ axioms.bupd iprop(∃ i, axioms.saved i (a i)) :=
  axioms.spropAllocDep a

variable [BIAffine PROP]

@[rocq_alias savedprop.saved_NA]
theorem saved_na {axioms : SavedPropAxioms PROP} (i : axioms.ident) :
    axioms.saved i (a i) ⊢ ¬ a i := by
  iunfold a
  iintro #Hs #HA
  icases +keep HA with ⟨%P, HNP, #HsP⟩
  iapply HNP
  icases axioms.spropAgree i P (a i) $$ [] with ⟨-, HAP⟩
  · iunfold a; iframe #
  iapply HAP
  iunfold a; itrivial

@[rocq_alias savedprop.saved_A]
theorem saved_a {axioms : SavedPropAxioms PROP} (i : axioms.ident) :
    axioms.saved i (a i) ⊢ a i := by
  iintro #Hs
  iunfold a
  iexists a i
  iframe Hs
  iapply saved_na i $$ Hs

@[rocq_alias savedprop.contradiction]
theorem contradiction (axioms : SavedPropAxioms PROP) : False := by
  apply axioms.consistency
  imod a_alloc with ⟨%i, #Hs⟩
  iapply axioms.bupdIntro
  iapply saved_na i $$ Hs
  iapply saved_a i $$ Hs

end SavedProp

namespace Inv

variable {PROP : Type _} [BI PROP]

@[rocq_alias inv.mask]
inductive Mask where
  | M0
  | M1

structure InvAxioms PROP [BI PROP] where
  fupd : Mask → PROP → PROP
  fupdIntro : ∀ E P, P ⊢ fupd E P
  fupdMono : ∀ E P Q, (P ⊢ Q) → fupd E P ⊢ fupd E Q
  fupdFupd : ∀ E P, fupd E (fupd E P) ⊢ fupd E P
  fupdFrameLeft : ∀ E P Q, P ∗ fupd E Q ⊢ fupd E iprop(P ∗ Q)
  fupdMaskMono : ∀ P, fupd Mask.M0 P ⊢ fupd Mask.M1 P
  name : Type u
  inv : name → PROP → PROP
  [invPersistent : ∀ i P, Persistent (inv i P)]
  invAlloc : ∀ P, P ⊢ fupd Mask.M1 iprop(∃ i, inv i P)
  invFupd : ∀ i P Q R,
    (P ∗ Q ⊢ fupd Mask.M0 iprop(P ∗ R)) → inv i P ∗ Q ⊢ fupd Mask.M1 R
  consistency : ¬(⊢ fupd Mask.M1 iprop(False))

structure FirstParadoxAxioms {PROP} [BI PROP] (axioms : InvAxioms PROP) where
  gname : Type v
  start : gname → PROP
  finished : gname → PROP
  stsAlloc : ⊢ axioms.fupd Mask.M0 iprop(∃ gamma, start gamma)
  startFinish : ∀ gamma, start gamma ⊢ axioms.fupd Mask.M0 (finished gamma)
  finishedNotStart : ∀ gamma, start gamma ∗ finished gamma ⊢ iprop(False)
  finishedDup : ∀ gamma, finished gamma ⊢ finished gamma ∗ finished gamma

structure SecondParadoxAxioms {PROP} [BI PROP] (axioms : InvAxioms PROP) where
  gname : Type v
  start : gname → PROP
  finished : gname → PROP
  stsAlloc : ⊢ axioms.fupd Mask.M0 iprop(∃ gamma, start gamma)
  startFinish : ∀ gamma, start gamma ⊢ axioms.fupd Mask.M0 (finished gamma)
  finishedNotStart : ∀ gamma, start gamma ∗ finished gamma ⊢ iprop(False)
  [finishedPersistent : ∀ gamma, Persistent (finished gamma)]

attribute [instance] InvAxioms.invPersistent SecondParadoxAxioms.finishedPersistent

@[rocq_alias inv.inv_fupd']
theorem inv_fupd' [BIAffine PROP] {axioms : InvAxioms PROP}
    (i : axioms.name) (P R : PROP) :
    axioms.inv i P ∗
      iprop(P -∗ axioms.fupd Mask.M0 iprop(P ∗ axioms.fupd Mask.M1 R)) ⊢
        axioms.fupd Mask.M1 R := by
  iintro ⟨#HiP, HP⟩
  iapply axioms.fupdFupd
  iapply axioms.invFupd i P _ (axioms.fupd Mask.M1 R) wand_elim_right
  iframe HiP HP

#rocq_ignore inv.fupd_mono'
  "`Proper` is absent in Lean; use explicit `fupdMono` directly."
#rocq_ignore inv.fupd_proper
  "`Proper` is absent in Lean; use explicit `fupdMono` separately in both entailment directions."

@[rocq_alias inv.fupd_frame_r]
theorem fupd_frame_right {axioms : InvAxioms PROP} (E : Mask) (P Q : PROP) :
    axioms.fupd E P ∗ Q ⊢ axioms.fupd E iprop(P ∗ Q) :=
  (sep_comm.mp).trans <|
    (axioms.fupdFrameLeft E Q P).trans <| axioms.fupdMono E _ _ sep_comm.mp

variable [BIAffine PROP]

@[rocq_alias inv.elim_fupd_fupd]
local instance elim_fupd_fupd {axioms : InvAxioms PROP}
    (p : Bool) (io : InOut) (E : Mask) (P Q : PROP) :
    ElimModal True p io false
      (axioms.fupd E P) P (axioms.fupd E Q) (axioms.fupd E Q) := by
  exact ⟨fun _ ↦
    (sep_mono_left intuitionisticallyIf_elim).trans <|
      (sep_comm.mp).trans <| (axioms.fupdFrameLeft E _ _).trans <|
        (axioms.fupdMono E _ _ wand_elim_left).trans <| axioms.fupdFupd E Q⟩

@[rocq_alias inv.elim_fupd0_fupd1]
local instance elim_fupd0_fupd1 {axioms : InvAxioms PROP}
    (p : Bool) (io : InOut) (P Q : PROP) :
    ElimModal True p io false
      (axioms.fupd Mask.M0 P) P (axioms.fupd Mask.M1 Q) (axioms.fupd Mask.M1 Q) := by
  exact ⟨fun _ ↦
    (sep_mono_left intuitionisticallyIf_elim).trans <|
      (sep_comm.mp).trans <| (axioms.fupdFrameLeft Mask.M0 _ _).trans <|
        (axioms.fupdMono Mask.M0 _ _ wand_elim_left).trans <|
          (axioms.fupdMaskMono _).trans <| axioms.fupdFupd Mask.M1 Q⟩

@[rocq_alias inv.exists_split_fupd0]
local instance exists_split_fupd0 {axioms : InvAxioms PROP}
    {α : Type _} (E : Mask) (P : PROP) (Φ : α → PROP) [FromExists P Φ] :
    FromExists (axioms.fupd E P) (fun a ↦ axioms.fupd E (Φ a)) :=
  ⟨exists_elim fun a ↦ axioms.fupdMono E _ _ ((exists_intro a).trans from_exists)⟩

section FirstParadox

variable {axioms : InvAxioms PROP} {paradox : FirstParadoxAxioms axioms}

@[rocq_alias inv.saved]
def saved (gamma : paradox.gname) (P : PROP) : PROP :=
  iprop(∃ i, axioms.inv i iprop(paradox.start gamma ∨ (paradox.finished gamma ∗ □ P)))

@[rocq_alias inv.saved_persistent]
local instance saved_persistent (gamma : paradox.gname) (P : PROP) :
    Persistent (saved gamma P) := by
  dsimp [saved]
  exact exists_persistent _

@[rocq_alias inv.saved_alloc]
theorem saved_alloc (P : paradox.gname → PROP) :
    ⊢ axioms.fupd Mask.M1 iprop(∃ gamma, saved gamma (P gamma)) := by
  iunfold saved
  imod paradox.stsAlloc with ⟨%gamma, Hs⟩
  imod axioms.invAlloc
      iprop(paradox.start gamma ∨ (paradox.finished gamma ∗ □ P gamma)) $$ [Hs]
    with ⟨%i, Hi⟩
  · iframe
  · iapply axioms.fupdIntro
    iexists gamma, i
    iframe

@[rocq_alias inv.saved_cast]
theorem saved_cast (gamma : paradox.gname) (P Q : PROP) :
    saved gamma P ∗ saved gamma Q ∗ □ P ⊢ axioms.fupd Mask.M1 iprop(□ Q) := by
  iunfold saved
  iintro ⟨#HsP, #HsQ, #HP⟩
  icases HsP with ⟨%i, #HiP⟩
  iapply inv_fupd' i
    iprop(paradox.start gamma ∨ (paradox.finished gamma ∗ □ P)) iprop(□ Q)
  iframe HiP
  iintro HaP
  ihave Hfin : axioms.fupd Mask.M0 (paradox.finished gamma) $$ [HaP]
  · icases HaP with (Hs | ⟨Hf, -⟩)
    · iapply paradox.startFinish gamma
      iexact Hs
    · iapply axioms.fupdIntro
      iexact Hf
  imod Hfin with Hf
  ihave ⟨Hf, Hf'⟩ := paradox.finishedDup gamma $$ Hf
  iapply axioms.fupdIntro
  isplitl [Hf']
  · iright
    iframe Hf' HP
  · icases HsQ with ⟨%j, #HiQ⟩
    iapply inv_fupd' j
      iprop(paradox.start gamma ∨ (paradox.finished gamma ∗ □ Q)) iprop(□ Q)
    iframe HiQ
    iintro HaQ
    icases HaQ with (Hs | ⟨-, #HQ⟩)
    · iexfalso
      iapply paradox.finishedNotStart gamma
      iframe Hs Hf
    · iapply axioms.fupdIntro
      isplitl [Hf]
      · iright
        iframe Hf HQ
      · iapply axioms.fupdIntro
        iexact HQ

@[rocq_alias inv.A]
def a (i : paradox.gname) : PROP :=
  iprop(∃ P, □ (P -∗ axioms.fupd Mask.M1 iprop(False)) ∗ saved i P)

@[rocq_alias inv.A_persistent]
local instance a_persistent (i : paradox.gname) : Persistent (a i) := by
  dsimp [a, saved]
  infer_instance

@[rocq_alias inv.A_alloc]
theorem a_alloc :
    ⊢ axioms.fupd Mask.M1 iprop(∃ i : paradox.gname, saved i (a i)) :=
    saved_alloc a

@[rocq_alias inv.saved_NA]
theorem saved_na (i : paradox.gname) :
    saved i (a i) ⊢ iprop(□ (a i -∗ axioms.fupd Mask.M1 iprop(False))) := by
  iunfold a
  iintro #Hi !> #HA
  icases +keep HA with ⟨%P, #HNP, #Hi'⟩
  imod saved_cast i (a i) P $$ [#] with HP
  · iunfold a
    isplit
    · itrivial
    · isplit <;> itrivial
  · iapply HNP $$ HP

@[rocq_alias inv.saved_A]
theorem saved_a (i : paradox.gname) : saved i (a i) ⊢ a i := by
  iintro #Hi
  iunfold a
  iexists a i
  iframe Hi
  iapply saved_na i $$ Hi

@[rocq_alias inv.contradiction]
theorem contradiction (axioms : InvAxioms PROP) (paradox : FirstParadoxAxioms axioms) :
    False := by
  apply axioms.consistency
  imod a_alloc with ⟨%i, #H⟩
  iapply saved_na i $$ H
  iapply saved_a (paradox := paradox) i $$ H

end FirstParadox

section SecondParadox

variable {axioms : InvAxioms PROP} {paradox : SecondParadoxAxioms axioms}

@[rocq_alias inv.B]
def b (axioms : InvAxioms PROP) : PROP := iprop(□ axioms.fupd Mask.M1 iprop(False))

@[rocq_alias inv.P]
def p (gamma : paradox.gname) : PROP := iprop(paradox.start gamma ∨ b axioms)

@[rocq_alias inv.I]
def iPred (i : axioms.name) (gamma : paradox.gname) : PROP := axioms.inv i (p gamma)

@[rocq_alias inv.finished_contradiction]
theorem finished_contradiction (gamma : paradox.gname) (i : axioms.name) :
    paradox.finished gamma ∗ iPred i gamma -∗ b axioms := by
  iunfold iPred, p, b
  iintro ⟨#Hfin, #HI⟩ !>
  iapply inv_fupd' i
    iprop(paradox.start gamma ∨ □ axioms.fupd Mask.M1 iprop(False)) iprop(False)
  iframe HI
  iintro (Hstart | #Hfalse)
  · iexfalso
    iapply paradox.finishedNotStart gamma
    iframe Hfin Hstart
  · iapply axioms.fupdIntro
    iframe Hfalse

@[rocq_alias inv.invariant_contradiction]
theorem invariant_contradiction (gamma : paradox.gname) (i : axioms.name) :
    iPred i gamma -∗ b axioms := by
  iunfold iPred, p, b
  iintro #HI
  imodintro
  iapply inv_fupd' i iprop(paradox.start gamma ∨ □ axioms.fupd Mask.M1 iprop(False)) iprop(False)
  iframe HI
  iintro HP
  ihave Hfalse : axioms.fupd Mask.M0 iprop(□ axioms.fupd Mask.M1 iprop(False)) $$ [HP]
  · icases HP with (Hstart | #Hfalse)
    · imod paradox.startFinish gamma $$ Hstart with #Hfin
      iapply axioms.fupdIntro
      ihave Hb := finished_contradiction gamma i $$ [Hfin HI]
      · iunfold iPred, p, b; iframe Hfin HI
      iunfold b in Hb
      iexact Hb
    · iapply axioms.fupdIntro
      iexact Hfalse
  imod Hfalse with #Hfalse
  iapply axioms.fupdIntro
  iframe Hfalse

@[rocq_alias inv.contradiction']
theorem contradiction' (axioms : InvAxioms PROP) (paradox : SecondParadoxAxioms axioms) :
    False := by
  apply axioms.consistency
  imod paradox.stsAlloc with ⟨%gamma, Hstart⟩
  imod axioms.invAlloc (p gamma) $$ [Hstart]
    with ⟨%i, #HI⟩
  · iunfold p
    ileft
    iexact Hstart
  · ihave Hfalse : b axioms $$ [HI]
    · iapply invariant_contradiction gamma i
      iunfold iPred
      iexact HI
    iunfold b in Hfalse
    icases Hfalse with #Hfalse
    iexact Hfalse

end SecondParadox

end Inv

namespace Linear

variable {PROP : Type _} [BI PROP]

@[rocq_alias linear.mask]
inductive Mask where
  | M0
  | M1

structure LinearAxioms PROP [BI PROP] where
  fupd : Mask → Mask → PROP → PROP
  fupdIntro : ∀ E P, P ⊢ fupd E E P
  fupdMono : ∀ E1 E2 P Q, (P ⊢ Q) → fupd E1 E2 P ⊢ fupd E1 E2 Q
  fupdFupd : ∀ E1 E2 E3 P, fupd E1 E2 (fupd E2 E3 P) ⊢ fupd E1 E3 P
  fupdFrameLeft : ∀ E1 E2 P Q, P ∗ fupd E1 E2 Q ⊢ fupd E1 E2 iprop(P ∗ Q)
  gname : Type u
  cinv : gname → PROP → PROP
  cinvOwn : gname → PROP
  cinvAlloc : ∀ E P,
    iprop(▷ P) -∗ fupd E E iprop(∃ gamma, cinv gamma P ∗ cinvOwn gamma)
  cinvAcc : ∀ P gamma,
    cinv gamma P -∗ cinvOwn gamma -∗
      fupd Mask.M1 Mask.M0 iprop(▷ P ∗ cinvOwn gamma ∗
        (▷ P -∗ fupd Mask.M0 Mask.M1 emp))

#rocq_ignore linear.fupd_mono' "Use explicit `fupdMono` directly."
#rocq_ignore linear.fupd_proper "Use explicit `fupdMono` separately in both entailment directions."

@[rocq_alias linear.fupd_frame_r]
theorem fupd_frame_right {axioms : LinearAxioms PROP} (E1 E2 : Mask) (P Q : PROP) :
    axioms.fupd E1 E2 P ∗ Q ⊢ axioms.fupd E1 E2 iprop(P ∗ Q) :=
  (sep_comm.mp).trans <|
    (axioms.fupdFrameLeft E1 E2 Q P).trans <| axioms.fupdMono E1 E2 _ _ sep_comm.mp

@[rocq_alias linear.elim_fupd_fupd]
local instance elim_fupd_fupd {axioms : LinearAxioms PROP}
    (p : Bool) (io : InOut) (E1 E2 E3 : Mask) (P Q : PROP) :
    ElimModal True p io false (axioms.fupd E1 E2 P) P (axioms.fupd E1 E3 Q) (axioms.fupd E2 E3 Q) := by
  exact ⟨fun _ ↦
    (sep_mono_left intuitionisticallyIf_elim).trans <|
      (sep_comm.mp).trans <| (axioms.fupdFrameLeft E1 E2 _ _).trans <|
        (axioms.fupdMono E1 E2 _ _ wand_elim_left).trans <|
          axioms.fupdFupd E1 E2 E3 Q⟩

@[rocq_alias linear.leak]
theorem leak {axioms : LinearAxioms PROP} (P : PROP) :
    P -∗ axioms.fupd Mask.M1 Mask.M1 iprop(emp) := by
  iintro HP
  imod axioms.cinvAlloc Mask.M1 iprop(True) $$ [//] with ⟨%gamma, Hinv, Htok⟩
  imod axioms.cinvAcc iprop(True) gamma $$ Hinv Htok with ⟨-, Htok, Hclose⟩
  iapply Hclose
  itrivial

end Linear

end Iris
