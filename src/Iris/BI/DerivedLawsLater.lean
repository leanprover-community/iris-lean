/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.BI.Classes
public import Iris.BI.Extensions
public import Iris.BI.BI
public import Iris.BI.DerivedLaws
public import Iris.Std.Classes
public import Iris.Std.Rewrite
public import Iris.Std.TC

@[expose] public section

namespace Iris.BI
open Iris.Std BI

/-! # Later -/

theorem later_congr [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : ▷ P ⊣⊢ ▷ Q :=
  ⟨later_mono h.1, later_mono h.2⟩

theorem later_true [BI PROP] : (▷ True ⊣⊢ (True : PROP)) := ⟨true_intro, later_intro⟩

theorem later_emp [BI PROP] [BIAffine PROP] : (▷ emp ⊣⊢ (emp : PROP)) :=
  ⟨affine, later_intro⟩

theorem later_forall_2 [BI PROP] {α} {Φ : α → PROP} : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a := by
  refine (forall_intro ?_).trans later_sForall_2
  intro P
  refine imp_intro' ?_
  refine and_comm.mp.trans <| imp_elim' <| pure_elim _ .rfl ?_
  rintro ⟨_, Ha⟩
  rewrite [← Ha]
  exact imp_intro' <| and_elim_l.trans <| forall_elim _

theorem later_forall [BI PROP] {Φ : α → PROP} :
    ▷ (∀ a, Φ a) ⊣⊢ (∀ a, ▷ Φ a) :=
  ⟨forall_intro (later_mono <| forall_elim ·), later_forall_2⟩

theorem later_exists_2 [BI PROP] {Φ : α → PROP} :
    (∃ a, ▷ Φ a) ⊢ ▷ (∃ a, Φ a) :=
  exists_elim (later_mono <| exists_intro ·)

theorem later_exists_false [BI PROP] {Φ : α → PROP} :
    (▷ ∃ a, Φ a) ⊢ ▷ False ∨ ∃ a, ▷ Φ a := by
  apply later_sExists_false.trans
  apply or_elim
  · apply or_intro_l
  · refine or_intro_r' <| exists_elim ?_
    intro P
    refine imp_elim <| pure_elim' ?_
    rintro ⟨a, rfl⟩
    exact imp_intro' <| exists_intro' a and_elim_l

theorem later_exists [BI PROP] [Inhabited α] {Φ : α → PROP} :
    (∃ a, ▷ Φ a) ⊣⊢ ▷ (∃ a, Φ a) := by
  refine ⟨later_exists_2, later_exists_false.trans ?_⟩
  exact or_elim (exists_intro' default <| later_mono <| false_elim) .rfl

theorem later_and [BI PROP] {P Q : PROP} : ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q := by
  constructor
  · refine (later_mono and_forall_bool.mp).trans ?_
    refine .trans ?_ and_forall_bool.mpr
    refine (later_forall).mp.trans (forall_mono ?_)
    exact (·.casesOn .rfl .rfl)
  · refine .trans ?_ (later_mono and_forall_bool.mpr)
    refine and_forall_bool.mp.trans ?_
    refine .trans (forall_mono ?_) later_forall.mpr
    exact (·.casesOn .rfl .rfl)

theorem later_or [BI PROP] {P Q : PROP} : ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q := by
  constructor
  · refine (later_mono or_exists_bool.mp).trans ?_
    refine .trans ?_ or_exists_bool.mpr
    refine later_exists.mpr.trans (exists_mono ?_)
    exact (·.casesOn .rfl .rfl)
  · refine .trans ?_ (later_mono or_exists_bool.mpr)
    refine .trans ?_ later_exists.mp
    refine  or_exists_bool.mp.trans (exists_mono ?_)
    exact (·.casesOn .rfl .rfl)

theorem later_impl [BI PROP] {P Q : PROP} : ▷ (P → Q) ⊢ ▷ P → ▷ Q :=
  imp_intro' <| later_and.mpr.trans <| later_mono imp_elim_r

theorem later_wand [BI PROP] {P Q : PROP} : ▷ (P -∗ Q) ⊢ ▷ P -∗ ▷ Q :=
  wand_intro' <| later_sep.mpr.trans <| later_mono wand_elim_r

theorem later_iff [BI PROP] {P Q : PROP} : ▷ (P ↔ Q) ⊢ (▷ P ↔ ▷ Q) :=
  later_and.mp.trans <|and_intro (and_elim_l.trans later_impl) (and_elim_r.trans later_impl)

theorem later_wand_iff [BI PROP] {P Q : PROP} : ▷ (P ∗-∗ Q) ⊢ ▷ P ∗-∗ ▷ Q :=
  later_and.mp.trans <| and_intro (and_elim_l.trans later_wand) (and_elim_r.trans later_wand)

theorem later_affinely_2 [BI PROP] {P : PROP} : <affine> ▷ P ⊢ ▷ <affine> P :=
  .trans (and_mono later_intro .rfl) later_and.mpr

theorem later_intuitionistically_2 [BI PROP] {P : PROP} : □ ▷ P ⊢ ▷ □ P :=
  .trans (affinely_mono later_persistently.mpr) later_affinely_2

theorem later_intuitionisticallyIf_2 [BI PROP] {P : PROP} : □?p ▷ P ⊢ ▷ □?p P :=
  p.casesOn .rfl later_intuitionistically_2

theorem later_absorbingly [BI PROP] {P : PROP} : ▷ <absorb> P ⊣⊢ <absorb> ▷ P :=
  ⟨later_sep.mp.trans <| sep_mono true_intro .rfl, (sep_mono later_intro .rfl).trans later_sep.mpr⟩

theorem later_affinely [BI PROP] [BIAffine PROP] {P : PROP} : <affine> ▷ P ⊣⊢ ▷ <affine> P :=
  ⟨later_affinely_2, later_and.mp.trans <| .trans (and_elim_r) (affine_affinely _).mpr⟩

theorem later_intuitionistically [BI PROP] [BIAffine PROP] {P : PROP} : □ ▷ P ⊣⊢ ▷ □ P := by
  refine ⟨later_intuitionistically_2, ?_⟩
  refine (later_mono persistently_of_intuitionistically).trans ?_
  exact later_persistently.mp.trans intuitionistically_iff_persistently.mpr

theorem later_intuitionisticallyIf [BI PROP] [BIAffine PROP] {P : PROP} : □?p ▷ P ⊣⊢ ▷ □?p P :=
  p.casesOn (.of_eq rfl) later_intuitionistically

instance later_persistent [BI PROP] {P : PROP} [Persistent P] : Persistent iprop(▷ P) where
  persistent := (later_mono persistently_intro).trans later_persistently.mp

instance later_absorbing [BI PROP] {P : PROP} [Absorbing P] : Absorbing iprop(▷ P) where
  absorbing := later_absorbingly.mpr.trans <| later_mono absorbing

theorem entails_impl_true [BI PROP] {P Q : PROP} :
    (P ⊢ Q) ↔ iprop((True : PROP) ⊢ (P → Q)) :=
  ⟨imp_intro' ∘ pure_elim_r ∘ Function.const _, (and_intro .rfl true_intro).trans ∘ imp_elim'⟩

theorem loeb [BI PROP] [BILoeb PROP] {P : PROP} : (▷ P → P) ⊢ P := by
  apply entails_impl_true.mpr
  apply BILoeb.loeb_weak
  apply imp_intro
  apply (and_mono .rfl and_self.mpr).trans
  apply (and_mono .rfl (and_mono later_intro .rfl)).trans
  apply (and_mono later_impl .rfl).trans
  apply and_assoc.mpr.trans
  apply (and_mono imp_elim_l .rfl).trans
  exact imp_elim_r

theorem loeb_weak_of_strong [BI PROP] {P : PROP} (H : ∀ P : PROP, (▷ P → P) ⊢ P)
    (H' : ▷ P ⊢ P) : True ⊢ P := (entails_impl_true.mp H').trans (H P)

theorem loeb_wand_intuitionistically [BI PROP] [BILoeb PROP] {P : PROP} :
    □ (□ ▷ P -∗ P) ⊢ P := by
  refine .trans ?_ intuitionistically_elim
  refine .trans ?_ loeb
  refine imp_intro' ?_
  refine (and_mono (later_mono persistently_of_intuitionistically) .rfl).trans ?_
  refine (and_mono later_persistently.mp .rfl).trans ?_
  refine persistently_and_intuitionistically_sep_l.mp.trans ?_
  refine (sep_mono intuitionistically_idem.mpr .rfl).trans ?_
  exact intuitionistically_sep_2.trans (intuitionistically_mono wand_elim_r)

theorem loeb_wand [BI PROP] [BILoeb PROP] {P : PROP} : □ (▷ P -∗ P) ⊢ P :=
  (intuitionistically_mono (wand_mono intuitionistically_elim .rfl)).trans
    loeb_wand_intuitionistically

open Iris BI OFE Contractive in
instance [BI PROP] [BILaterContractive PROP] : BILoeb PROP where
  loeb_weak {P} HP := by
    let Hc : Contractive (fun Q => iprop((▷ Q) → P)) := ⟨fun H => imp_ne.ne (distLater_dist H) .rfl⟩
    let Flöb : PROP -c> PROP := { f := fun Q => iprop((▷ Q) → P), contractive := Hc }
    suffices HP : iprop(▷ (fixpoint Flöb) ⊢ P) by
      refine entails_impl_true.mp HP |>.trans ?_
      refine equiv_iff.mp (fixpoint_unfold Flöb) |>.mpr |>.trans ?_
      exact later_intro.trans HP
    refine .trans ?_ ((later_mono HP).trans HP)
    suffices Hcut : later (fixpoint Flöb) ⊢ later (later (later (fixpoint Flöb))) → later (later P) by
      exact and_intro (later_intro.trans later_intro) Hcut |>.trans imp_elim_r
    refine .trans (later_mono ?_) later_impl
    refine .trans ?_ later_impl
    refine .trans ?_ later_intro
    refine equiv_iff.mp ?_ |>.mp
    exact fixpoint_unfold Flöb

/-! # LaterN -/

theorem laterN_ne [BI PROP] (n : Nat) : OFE.NonExpansive (BIBase.laterN (PROP:=PROP) n) where
  ne := by
    induction n with
    | zero => exact fun _ _ _ h => h
    | succ n ih => exact fun _ _ _ h => later_ne.ne (ih h)

@[rw_mono_rule]
theorem laterN_mono [BI PROP] (n : Nat) {P Q : PROP} (h : P ⊢ Q) : ▷^[n] P ⊢ ▷^[n] Q := by
  induction n with
  | zero => exact h
  | succ n ih => exact later_mono ih

@[rw_mono_rule]
theorem laterN_congr [BI PROP] {P Q : PROP} (n : Nat) (h : P ⊣⊢ Q) : ▷^[n] P ⊣⊢ ▷^[n] Q :=
  ⟨laterN_mono n h.1, laterN_mono n h.2⟩

theorem laterN_0 [BI PROP] {P : PROP} : ▷^[0] P ⊣⊢ P := .rfl

theorem later_laterN [BI PROP] (n : Nat) {P : PROP} : ▷^[n + 1] P ⊣⊢ ▷ ▷^[n] P := .rfl

theorem laterN_later [BI PROP] (n : Nat) {P : PROP} : ▷^[n + 1] P ⊣⊢ ▷^[n] ▷ P := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact later_congr ih

theorem laterN_add [BI PROP] (n1 n2 : Nat) {P : PROP} : ▷^[n1 + n2] P ⊣⊢ ▷^[n1] ▷^[n2] P := by
  induction n1 with
  | zero => simp; exact .rfl
  | succ n1 ih => simp only [Nat.succ_add]; exact later_congr ih

theorem laterN_le [BI PROP] {n1 n2 : Nat} {P : PROP} (h : n1 ≤ n2) : ▷^[n1] P ⊢ ▷^[n2] P := by
  induction h with
  | refl => exact .rfl
  | step _ ih => exact ih.trans later_intro

theorem laterN_intro [BI PROP] (n : Nat) {P : PROP} : P ⊢ ▷^[n] P := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact ih.trans later_intro

theorem laterN_true [BI PROP] (n : Nat) : ▷^[n] True ⊣⊢@{PROP} True :=
  ⟨true_intro, laterN_intro n⟩

theorem laterN_emp [BI PROP] [BIAffine PROP] (n : Nat) : ▷^[n] emp ⊣⊢@{PROP} emp :=
  (laterN_congr n true_emp.symm).trans $ (laterN_true n).trans true_emp

theorem laterN_forall [BI PROP] (n : Nat) {Φ : α → PROP} : ▷^[n] (∀ a, Φ a) ⊣⊢ (∀ a, ▷^[n] Φ a) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_forall

theorem laterN_exists_2 [BI PROP] (n : Nat) {Φ : α → PROP} : (∃ a, ▷^[n] Φ a) ⊢ ▷^[n] (∃ a, Φ a) :=
  exists_elim fun a => laterN_mono n (exists_intro a)

theorem laterN_exists [BI PROP] [Inhabited α] (n : Nat) {Φ : α → PROP} :
    ▷^[n] (∃ a, Φ a) ⊣⊢ (∃ a, ▷^[n] Φ a) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_exists.symm

theorem laterN_and [BI PROP] (n : Nat) {P Q : PROP} : ▷^[n] (P ∧ Q) ⊣⊢ ▷^[n] P ∧ ▷^[n] Q := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_and

theorem laterN_or [BI PROP] (n : Nat) {P Q : PROP} : ▷^[n] (P ∨ Q) ⊣⊢ ▷^[n] P ∨ ▷^[n] Q := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_or

theorem laterN_impl [BI PROP] (n : Nat) {P Q : PROP} : ▷^[n] (P → Q) ⊢ ▷^[n] P → ▷^[n] Q :=
  imp_intro' <| (laterN_and n).2.trans <| laterN_mono n imp_elim_r

theorem laterN_sep [BI PROP] (n : Nat) {P Q : PROP} : ▷^[n] (P ∗ Q) ⊣⊢ ▷^[n] P ∗ ▷^[n] Q := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_sep

theorem laterN_wand [BI PROP] (n : Nat) {P Q : PROP} : ▷^[n] (P -∗ Q) ⊢ ▷^[n] P -∗ ▷^[n] Q :=
  wand_intro' <| (laterN_sep n).2.trans <| laterN_mono n wand_elim_r

theorem laterN_iff [BI PROP] (n : Nat) {P Q : PROP} : ▷^[n] (P ↔ Q) ⊢ (▷^[n] P ↔ ▷^[n] Q) :=
  (laterN_and n).1.trans <|
    and_intro (and_elim_l.trans (laterN_impl n)) (and_elim_r.trans (laterN_impl n))

theorem laterN_persistently [BI PROP] (n : Nat) {P : PROP} : ▷^[n] <pers> P ⊣⊢ <pers> ▷^[n] P := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans later_persistently

theorem laterN_affinely_2 [BI PROP] (n : Nat) {P : PROP} : <affine> ▷^[n] P ⊢ ▷^[n] <affine> P :=
  (and_mono (laterN_intro n) .rfl).trans (laterN_and n).2

theorem laterN_intuitionistically_2 [BI PROP] (n : Nat) {P : PROP} : □ ▷^[n] P ⊢ ▷^[n] □ P :=
  (affinely_mono (laterN_persistently n).2).trans (laterN_affinely_2 n)

theorem laterN_intuitionisticallyIf_2 [BI PROP] (n : Nat) {p : Bool} {P : PROP} :
    □?p ▷^[n] P ⊢ ▷^[n] □?p P :=
  match p with
  | false => .rfl
  | true => laterN_intuitionistically_2 n

theorem laterN_absorbingly [BI PROP] (n : Nat) {P : PROP} : ▷^[n] <absorb> P ⊣⊢ <absorb> ▷^[n] P :=
  (laterN_sep n).trans (sep_congr (laterN_true n) .rfl)

instance laterN_persistent [BI PROP] (n : Nat) (P : PROP) [Persistent P] :
    Persistent iprop(▷^[n] P) := by
  induction n with
  | zero => assumption
  | succ n _ => exact later_persistent

instance laterN_absorbing [BI PROP] (n : Nat) (P : PROP) [Absorbing P] :
    Absorbing iprop(▷^[n] P) := by
  induction n with
  | zero => assumption
  | succ n _ => exact later_absorbing

/-! # Except0 -/

theorem except0_ne [BI PROP] : OFE.NonExpansive (BIBase.except0 (PROP:=PROP)) where
  ne _ _ _ h := or_ne.ne .rfl h

@[rw_mono_rule]
theorem except0_mono [BI PROP] {P Q : PROP} (h : P ⊢ Q) : ◇ P ⊢ ◇ Q :=
  or_mono .rfl h

@[rw_mono_rule]
theorem except0_congr [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : ◇ P ⊣⊢ ◇ Q :=
  ⟨except0_mono h.1, except0_mono h.2⟩

theorem except0_intro [BI PROP] {P : PROP} : P ⊢ ◇ P := or_intro_r

theorem except0_idemp [BI PROP] {P : PROP} : ◇ ◇ P ⊣⊢ ◇ P :=
  ⟨or_elim or_intro_l .rfl, except0_intro⟩

theorem except0_true [BI PROP] : ◇ True ⊣⊢ (True : PROP) :=
  ⟨true_intro, except0_intro⟩

theorem except0_emp [BI PROP] [BIAffine PROP] : ◇ emp ⊣⊢ (emp : PROP) :=
  (except0_congr true_emp.symm).trans <| except0_true.trans true_emp

theorem except0_or [BI PROP] {P Q : PROP} : ◇ (P ∨ Q) ⊣⊢ ◇ P ∨ ◇ Q :=
  ⟨or_elim (or_intro_l.trans or_intro_l)
    (or_elim (or_intro_l.trans (or_mono_l or_intro_r)) (or_intro_r.trans (or_mono_r or_intro_r))),
   or_elim (or_mono .rfl or_intro_l) (or_mono .rfl or_intro_r)⟩

theorem except0_and [BI PROP] {P Q : PROP} : ◇ (P ∧ Q) ⊣⊢ ◇ P ∧ ◇ Q :=
  or_and_l

theorem except0_sep [BI PROP] {P Q : PROP} : ◇ (P ∗ Q) ⊣⊢ ◇ P ∗ ◇ Q := by
  constructor
  · apply or_elim
    · apply Entails.trans _ (sep_mono or_intro_l or_intro_l)
      apply Entails.trans _ (later_sep.1)
      apply later_mono
      apply false_elim
    · exact sep_mono or_intro_r or_intro_r
  · apply Entails.trans sep_or_r.1 _
    apply or_elim
    · apply or_intro_l'
      apply sep_elim_l
    · apply sep_comm.1.trans _
      apply Entails.trans sep_or_r.1
      apply or_elim
      · apply or_intro_l'
        apply sep_elim_l
      · apply or_intro_r'
        apply sep_comm.1

theorem except0_forall [BI PROP] {Φ : α → PROP} : ◇ (∀ a, Φ a) ⊣⊢ ∀ a, ◇ Φ a := by
  refine ⟨forall_intro (except0_mono <| forall_elim ·), ?_⟩
  refine (and_intro ((forall_mono λ _ =>
           (or_elim (later_mono false_elim) later_intro)).trans later_forall.2) .rfl).trans ?_
  refine and_mono_l later_false_em |>.trans ?_
  refine and_or_r.1.trans ?_
  refine or_elim ?_ ?_
  · exact and_elim_l.trans or_intro_l
  · refine or_intro_r' ?_
    refine forall_intro λ a => ?_
    refine imp_elim' <| forall_elim a |>.trans ?_
    refine or_elim (imp_intro <| imp_elim_r.trans <| forall_elim a) (imp_intro and_elim_l)

theorem except0_exists_2 [BI PROP] {Φ : α → PROP} : (∃ a, ◇ Φ a) ⊢ ◇ ∃ a, Φ a :=
  exists_elim fun a => except0_mono (exists_intro a)

theorem except0_exists [BI PROP] [Inhabited α] {Φ : α → PROP} :
    ◇ (∃ a, Φ a) ⊣⊢ ∃ a, ◇ Φ a :=
  ⟨or_elim ((exists_intro (Ψ:=λ _ =>_) default).trans <| exists_mono fun _ => or_intro_l)
           (exists_mono fun _ => except0_intro),
   except0_exists_2⟩

theorem except0_later [BI PROP] {P : PROP} : ◇ ▷ P ⊢ ▷ P :=
  (or_elim (later_mono false_elim) .rfl)

theorem except0_laterN [BI PROP] (n : Nat) {P : PROP} : ◇ ▷^[n] P ⊢ ▷^[n] ◇ P :=
  match n with
  | 0 => .rfl
  | _ + 1 => except0_later.trans <| (later_mono (except0_intro.trans (except0_laterN _)))

theorem except0_into_later [BI PROP] {P : PROP} : ◇ P ⊢ ▷ P :=
  (except0_mono later_intro).trans except0_later

theorem except0_persistently [BI PROP] {P : PROP} : ◇ <pers> P ⊣⊢ <pers> ◇ P := by
  apply BiEntails.trans _ persistently_or.symm
  apply or_congr_l
  apply BiEntails.trans _ later_persistently
  apply later_congr persistently_pure.symm

theorem except0_affinely_2 [BI PROP] {P : PROP} : <affine> ◇ P ⊢ ◇ <affine> P :=
  (and_mono except0_intro .rfl).trans except0_and.2

theorem except0_intuitionistically_2 [BI PROP] {P : PROP} : □ ◇ P ⊢ ◇ □ P :=
  (affinely_mono except0_persistently.2).trans except0_affinely_2

theorem except0_intuitionisticallyIf_2 [BI PROP] {p : Bool} {P : PROP} : □?p ◇ P ⊢ ◇ □?p P :=
  match p with
  | false => .rfl
  | true => except0_intuitionistically_2

theorem except0_absorbingly [BI PROP] {P : PROP} : ◇ <absorb> P ⊣⊢ <absorb> ◇ P :=
  except0_sep.trans <| sep_congr except0_true .rfl

theorem except0_frame_l [BI PROP] {P Q : PROP} : P ∗ ◇ Q ⊢ ◇ (P ∗ Q) :=
  (sep_mono except0_intro .rfl).trans except0_sep.2

theorem except0_frame_r [BI PROP] {P Q : PROP} : ◇ P ∗ Q ⊢ ◇ (P ∗ Q) :=
  (sep_mono .rfl except0_intro).trans except0_sep.2

theorem later_affinely_1 [BI PROP] {P : PROP} [Timeless (PROP := PROP) emp] :
    ▷ <affine> P ⊢ ◇ <affine> ▷ P :=
  later_and.1.trans <| (and_mono (Timeless.timeless (P:=emp)) .rfl).trans <| (and_mono_r except0_intro).trans except0_and.2

instance except0_persistent [BI PROP] (P : PROP) [Persistent P] : Persistent iprop(◇ P) :=
  inferInstanceAs (Persistent iprop(_ ∨ _))

instance except0_absorbing [BI PROP] (P : PROP) [Absorbing P] : Absorbing iprop(◇ P) :=
  inferInstanceAs (Absorbing iprop(_ ∨ _))
