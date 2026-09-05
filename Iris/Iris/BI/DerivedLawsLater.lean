/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.BI.Classes
public import Iris.BI.Extensions
public import Iris.BI.BI
public import Iris.BI.DerivedLaws
public import Iris.BI.BigOp.BigOp
public import Iris.Std.Classes
public import Iris.Std.Rewrite
public import Iris.Std.TC

@[expose] public section

namespace Iris.BI
open Iris.Std BI

variable {PROP : Type _} [BI PROP]

/-! # Later -/

theorem later_congr {P Q : PROP} (h : P ⊣⊢ Q) : ▷ P ⊣⊢ ▷ Q :=
  ⟨later_mono h.1, later_mono h.2⟩

#rocq_ignore bi.later_mono' "Use later_mono."
#rocq_ignore bi.later_flip_mono' "Use later_mono."
#rocq_ignore bi.later_proper "Derivable from later_ne with NonExpansive.eqv"

@[rocq_alias bi.later_True]
theorem later_true : (▷ True ⊣⊢ (True : PROP)) := ⟨true_intro, later_intro⟩

@[rocq_alias bi.later_emp]
theorem later_emp [BIAffine PROP] : ▷ emp ⊣⊢ (emp : PROP) :=
  ⟨affine, later_intro⟩

@[rocq_alias bi.later_emp_2]
theorem later_emp_2 : emp ⊢@{PROP} ▷ emp := later_intro

@[rocq_alias bi.later_forall_2]
theorem later_forall_2 {α} {Φ : α → PROP} : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a := by
  refine (forall_intro ?_).trans later_sForall_2
  intro P
  refine imp_intro_swap ?_
  refine and_comm.mp.trans <| imp_elim_swap <| pure_elim _ .rfl ?_
  rintro ⟨_, Ha⟩
  rewrite [← Ha]
  exact imp_intro_swap <| and_elim_l.trans <| forall_elim _

@[rocq_alias bi.later_forall]
theorem later_forall {Φ : α → PROP} :
    ▷ (∀ a, Φ a) ⊣⊢ (∀ a, ▷ Φ a) :=
  ⟨forall_intro (later_mono <| forall_elim ·), later_forall_2⟩

@[rocq_alias bi.later_exist_2]
theorem later_exists_mp {Φ : α → PROP} :
    (∃ a, ▷ Φ a) ⊢ ▷ (∃ a, Φ a) :=
  exists_elim (later_mono <| exists_intro ·)

@[rocq_alias bi.later_exist_false]
theorem later_exists_false {Φ : α → PROP} :
    (▷ ∃ a, Φ a) ⊢ ▷ False ∨ ∃ a, ▷ Φ a := by
  apply later_sExists_false.trans
  apply or_elim
  · apply or_intro_l
  · refine or_intro_right_trans <| exists_elim ?_
    intro P
    refine imp_elim <| pure_elim' ?_
    rintro ⟨a, rfl⟩
    exact imp_intro_swap <| and_elim_l.trans (exists_intro (Ψ := fun a => iprop(▷ Φ a)) a)

@[rocq_alias bi.later_exist_except_0]
theorem later_exists_except0 {Φ : α → PROP} :
    (▷ ∃ a, Φ a) ⊢ ◇ (∃ a, ▷ Φ a) := later_exists_false

@[rocq_alias bi.later_exist]
theorem later_exists [Inhabited α] {Φ : α → PROP} :
    (∃ a, ▷ Φ a) ⊣⊢ ▷ (∃ a, Φ a) := by
  refine ⟨later_exists_mp, later_exists_false.trans ?_⟩
  exact or_elim ((later_mono false_elim).trans (exists_intro (Ψ := fun a => iprop(▷ Φ a)) default)) .rfl

@[rocq_alias bi.later_and]
theorem later_and {P Q : PROP} : ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q := by
  constructor
  · refine (later_mono and_forall_ite.mp).trans ?_
    refine .trans ?_ and_forall_ite.mpr
    refine (later_forall).mp.trans (forall_mono ?_)
    exact (·.casesOn .rfl .rfl)
  · refine .trans ?_ (later_mono and_forall_ite.mpr)
    refine and_forall_ite.mp.trans ?_
    refine .trans (forall_mono ?_) later_forall.mpr
    exact (·.casesOn .rfl .rfl)

@[rocq_alias bi.later_or]
theorem later_or {P Q : PROP} : ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q := by
  constructor
  · refine (later_mono or_exists_ite.mp).trans ?_
    refine .trans ?_ or_exists_ite.mpr
    refine later_exists.mpr.trans (exists_mono ?_)
    exact (·.casesOn .rfl .rfl)
  · refine .trans ?_ (later_mono or_exists_ite.mpr)
    refine .trans ?_ later_exists.mp
    refine  or_exists_ite.mp.trans (exists_mono ?_)
    exact (·.casesOn .rfl .rfl)

@[rocq_alias bi.later_sep]
theorem later_sep_alias {P Q : PROP} : ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q := later_sep

@[rocq_alias bi.later_persistently]
theorem later_persistently_alias {P : PROP} : ▷ <pers> P ⊣⊢ <pers> ▷ P := later_persistently

@[rocq_alias bi.later_impl]
theorem later_imp {P Q : PROP} : ▷ (P → Q) ⊢ ▷ P → ▷ Q :=
  imp_intro_swap <| later_and.mpr.trans <| later_mono imp_elim_right

@[rocq_alias bi.later_wand]
theorem later_wand {P Q : PROP} : ▷ (P -∗ Q) ⊢ ▷ P -∗ ▷ Q :=
  wand_intro_left <| later_sep.mpr.trans <| later_mono wand_elim_right

@[rocq_alias bi.later_iff]
theorem later_iff {P Q : PROP} : ▷ (P ↔ Q) ⊢ (▷ P ↔ ▷ Q) :=
  later_and.mp.trans <| and_intro (and_elim_l.trans later_imp) (and_elim_r.trans later_imp)

@[rocq_alias bi.later_wand_iff]
theorem later_wand_iff {P Q : PROP} : ▷ (P ∗-∗ Q) ⊢ ▷ P ∗-∗ ▷ Q :=
  later_and.mp.trans <| and_intro (and_elim_l.trans later_wand) (and_elim_r.trans later_wand)

@[rocq_alias bi.later_affinely_2]
theorem later_affinely_mpr {P : PROP} : <affine> ▷ P ⊢ ▷ <affine> P :=
  (and_mono_left later_intro).trans later_and.mpr

@[rocq_alias bi.later_intuitionistically_2]
theorem later_intuitionistically_2 {P : PROP} : □ ▷ P ⊢ ▷ □ P :=
  (affinely_mono later_persistently.mpr).trans later_affinely_mpr

@[rocq_alias bi.later_intuitionistically_if_2]
theorem later_intuitionisticallyIf_2 {P : PROP} : □?p ▷ P ⊢ ▷ □?p P :=
  p.casesOn .rfl later_intuitionistically_2

@[rocq_alias bi.later_absorbingly]
theorem later_absorbingly {P : PROP} : ▷ <absorb> P ⊣⊢ <absorb> ▷ P :=
  ⟨later_sep.mp.trans <| sep_mono_left true_intro, (sep_mono_left later_intro).trans later_sep.mpr⟩

@[rocq_alias bi.later_affinely]
theorem later_affinely [BIAffine PROP] {P : PROP} : <affine> ▷ P ⊣⊢ ▷ <affine> P := by
  refine ⟨later_affinely_mpr, ?_⟩
  calc
    _ ⊢ ▷ emp ∧ ▷ P := later_and.mp
    _ ⊢ ▷ P          := and_elim_r
    _ ⊢ <affine> ▷ P := (affine_affinely _).mpr

@[rocq_alias bi.later_intuitionistically]
theorem later_intuitionistically [BIAffine PROP] {P : PROP} : □ ▷ P ⊣⊢ ▷ □ P := by
  refine ⟨later_intuitionistically_2, ?_⟩
  refine (later_mono persistently_of_intuitionistically).trans ?_
  exact later_persistently.mp.trans intuitionistically_iff_persistently.mpr

@[rocq_alias bi.later_intuitionistically_if]
theorem later_intuitionisticallyIf [BIAffine PROP] {P : PROP} : □?p ▷ P ⊣⊢ ▷ □?p P :=
  p.casesOn (.of_eq rfl) later_intuitionistically

@[rocq_alias bi.later_persistent]
instance later_persistent {P : PROP} [Persistent P] : Persistent iprop(▷ P) where
  persistent := (later_mono persistently_intro).trans later_persistently.mp

@[rocq_alias bi.later_absorbing]
instance later_absorbing {P : PROP} [Absorbing P] : Absorbing iprop(▷ P) where
  absorbing := later_absorbingly.mpr.trans <| later_mono absorbing

#rocq_ignore bi.laterN_iter "laterN in Lean is defined using Nat.repeat directly"

theorem later_imp_and {P S : PROP} : ▷ (S → P) ∧ S ⊢ ▷ P :=
  ((and_mono_right later_intro).trans later_and.mpr).trans <| later_mono <| and_comm.mp.trans imp_elim_right

/-! ## Later as a monoid homomorphism

These instances ported from Rocq `bi_later_monoid_*` in
`iris/bi/derived_laws_later.v`. -/

@[rocq_alias bi.bi_later_monoid_and_homomorphism]
instance bi_later_monoid_and_homomorphism :
    Iris.Algebra.MonoidHomomorphism (and (PROP := PROP)) and iprop(True) iprop(True) (· = ·) later :=
  MonoidHomomorphism.ofEq BI.later_ne
    later_and.to_eq later_true.to_eq

@[rocq_alias bi.bi_later_monoid_or_homomorphism]
instance bi_later_monoid_or_homomorphism :
    Iris.Algebra.WeakMonoidHomomorphism (or (PROP := PROP)) or iprop(False) iprop(False) (· = ·) later :=
  WeakMonoidHomomorphism.ofEq BI.later_ne later_or.to_eq

@[rocq_alias bi.bi_later_monoid_sep_weak_homomorphism]
instance bi_later_monoid_sep_weak_homomorphism :
    Iris.Algebra.WeakMonoidHomomorphism (sep (PROP := PROP)) sep emp emp (· = ·) later :=
  WeakMonoidHomomorphism.ofEq BI.later_ne later_sep.to_eq

@[rocq_alias bi.bi_later_monoid_sep_homomorphism]
instance bi_later_monoid_sep_homomorphism [BIAffine PROP] :
    Iris.Algebra.MonoidHomomorphism (sep (PROP := PROP)) sep emp emp (· = ·) later :=
  MonoidHomomorphism.ofEq BI.later_ne
    later_sep.to_eq later_emp.to_eq

@[rocq_alias bi.bi_later_monoid_sep_entails_weak_homomorphism]
instance bi_later_monoid_sep_entails_weak_homomorphism :
    Iris.Algebra.WeakMonoidHomomorphism (sep (PROP := PROP)) sep emp emp (flip Entails) later where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := BI.later_ne
  map_op := later_sep.mpr

@[rocq_alias bi.bi_later_monoid_sep_entails_homomorphism]
instance bi_later_monoid_sep_entails_homomorphism :
    Iris.Algebra.MonoidHomomorphism (sep (PROP := PROP)) sep emp emp (flip Entails) later where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := BI.later_ne
  map_op := later_sep.mpr
  map_unit := later_intro

@[rocq_alias bi.löb]
theorem loeb [BILoeb PROP] {P : PROP} : (▷ P → P) ⊢ P := by
  refine entails_impl_true.mpr <| loeb_weak <| imp_intro ?_
  calc
    _ ⊢ ▷ ((▷ P → P) → P) ∧ (▷ P → P) ∧ (▷ P → P)         := and_mono_right and_self.mpr
    _ ⊢ ▷ ((▷ P → P) → P) ∧ ▷ (▷ P → P) ∧ (▷ P → P)      := and_mono_right (and_mono_left later_intro)
    _ ⊢ (▷ (▷ P → P) → ▷ P) ∧ ▷ (▷ P → P) ∧ (▷ P → P)   := and_mono_left later_imp
    _ ⊢ ((▷ (▷ P → P) → ▷ P) ∧ ▷ (▷ P → P)) ∧ (▷ P → P) := and_assoc.mpr
    _ ⊢ ▷ P ∧ (▷ P → P)                                     := and_mono_left imp_elim_left
    _ ⊢ P                                                     := imp_elim_right

@[rocq_alias bi.löb_alt_strong]
theorem loeb_weak_of_strong {P : PROP} (H : ∀ P : PROP, (▷ P → P) ⊢ P)
    (H' : ▷ P ⊢ P) : True ⊢ P := (entails_impl_true.mp H').trans (H P)

@[rocq_alias bi.löb_wand_intuitionistically]
theorem loeb_wand_intuitionistically [BILoeb PROP] {P : PROP} :
    □ (□ ▷ P -∗ P) ⊢ P := by
  calc
    _ ⊢ ▷ □ P → □ P := imp_intro_swap ?_
    _ ⊢ □ P          := loeb
    _ ⊢ P            := intuitionistically_elim
  calc
    _ ⊢ ▷ <pers> P ∧ □ (□ ▷ P -∗ P) := and_mono_left <| later_mono persistently_of_intuitionistically
    _ ⊢ <pers> ▷ P ∧ □ (□ ▷ P -∗ P) := and_mono_left later_persistently.mp
    _ ⊢ □ ▷ P ∗ □ (□ ▷ P -∗ P)      := persistently_and_intuitionistically_sep_left.mp
    _ ⊢ □ □ ▷ P ∗ □ (□ ▷ P -∗ P)    := sep_mono_left intuitionistically_idem.mpr
    _ ⊢ □ (□ ▷ P ∗ (□ ▷ P -∗ P))    := intuitionistically_sep_mpr
    _ ⊢ □ P                           := intuitionistically_mono wand_elim_right

@[rocq_alias bi.löb_wand]
theorem loeb_wand [BILoeb PROP] (P : PROP) : □ (▷ P -∗ P) ⊢ P :=
  (intuitionistically_mono (wand_mono_left intuitionistically_elim)).trans
    loeb_wand_intuitionistically

open Iris BI OFE Contractive in
@[rocq_alias bi.later_contractive_bi_löb]
instance later_contractive_bi_loeb [BILaterContractive PROP] : BILoeb PROP where
  loeb_weak {P} HP := by
    let Hc : Contractive (fun Q => iprop((▷ Q) → P)) := ⟨fun H => imp_ne.ne (distLater_dist H) .rfl⟩
    let Flöb : PROP -c> PROP := { f := fun Q => iprop((▷ Q) → P), contractive := Hc }
    suffices HP : iprop(▷ (fixpoint Flöb) ⊢ P) by
      refine entails_impl_true.mp HP |>.trans ?_
      refine (fixpoint_unfold Flöb).to_bi |>.mpr |>.trans ?_
      exact later_intro.trans HP
    refine .trans ?_ ((later_mono HP).trans HP)
    suffices Hcut : later (fixpoint Flöb) ⊢ later (later (later (fixpoint Flöb))) → later (later P) by
      exact and_intro (later_intro.trans later_intro) Hcut |>.trans imp_elim_right
    refine .trans (later_mono ?_) later_imp
    refine .trans ?_ later_imp
    refine .trans ?_ later_intro
    refine BIBase.BiEntails.of_eq ?_ |>.mp
    exact fixpoint_unfold Flöb

@[rocq_alias bi.not_not_later_False]
theorem not_not_later_False [BILoeb PROP] : ⊢@{PROP} ¬ ¬ ▷ False := entails_imp loeb

@[rocq_alias bi.bi_affine_alt_later_emp]
theorem bi_affine_alt_later_emp [BILoeb PROP] : BIAffine PROP ↔ (▷ emp ⊢@{PROP} emp) := by
  constructor
  · exact fun _ => later_emp.mp
  · exact fun h => ⟨fun Q => ⟨(imp_intro_swap <| (and_mono_left h).trans and_elim_l).trans loeb⟩⟩

@[rocq_alias bi.löb_alt_wand]
theorem loeb_alt_wand [BIAffine PROP] :
    BILoeb PROP ↔ ∀ P : PROP, □ (▷ P -∗ P) ⊢ P := by
  refine ⟨fun _ => loeb_wand, fun h => ⟨fun hP => ?_⟩⟩
  refine loeb_weak_of_strong (fun P => ?_) hP
  refine imp_iff_exists_persistently.mp.trans ?_
  refine exists_elim fun S => ?_
  apply imp_elim_swap
  refine intuitionistically_into_persistently.mpr.trans ?_
  apply imp_intro
  calc
    _ ⊢ □ (▷ (S → P) -∗ S → P) ∧ S := and_mono_left ?_
    _ ⊢ S ∧ □ (▷ (S → P) -∗ S → P) := and_comm.mp
    _ ⊢ S ∧ (S → P)                 := and_mono_right <| h _
    _ ⊢ P                           := imp_elim_right
  apply intuitionistically_intro_intuitionistically
  apply wand_intro
  apply imp_intro
  calc
    _ ⊢ (<pers> (▷ P ∧ S -∗ P) ∧ ▷ (S → P)) ∧ S := and_mono_left persistently_and_intuitionistically_sep_left.mpr
    _ ⊢ <pers> (▷ P ∧ S -∗ P) ∧ ▷ (S → P) ∧ S   := and_assoc.mp
    _ ⊢ □ (▷ P ∧ S -∗ P) ∗ (▷ (S → P) ∧ S)      := persistently_and_intuitionistically_sep_left.mp
    _ ⊢ (▷ P ∧ S -∗ P) ∗ ▷ P ∧ S                := sep_mono intuitionistically_elim <| and_intro later_imp_and and_elim_r
    _ ⊢ P                                         := wand_elim_left

/-! # LaterN -/

@[rocq_alias bi.laterN_ne]
theorem laterN_ne (n : Nat) : OFE.NonExpansive (BIBase.laterN (PROP:=PROP) n) where
  ne := by
    induction n with
    | zero => exact fun _ _ _ h => h
    | succ n ih => exact fun _ _ _ h => later_ne.ne (ih h)

@[rw_mono_rule, rocq_alias bi.laterN_mono]
theorem laterN_mono (n : Nat) {P Q : PROP} (h : P ⊢ Q) : ▷^[n] P ⊢ ▷^[n] Q := by
  induction n with
  | zero => exact h
  | succ n ih => exact later_mono ih
#rocq_ignore bi.laterN_mono' "Use laterN_mono."
#rocq_ignore bi.laterN_flip_mono' "Use laterN_mono."
#rocq_ignore bi.laterN_proper "Derivable from laterN_ne with NonExpansive.eqv"

@[rw_mono_rule]
theorem laterN_congr {P Q : PROP} (n : Nat) (h : P ⊣⊢ Q) : ▷^[n] P ⊣⊢ ▷^[n] Q :=
  ⟨laterN_mono n h.1, laterN_mono n h.2⟩

@[rocq_alias bi.laterN_0]
theorem laterN_0 {P : PROP} : ▷^[0] P ⊣⊢ P := .rfl

@[rocq_alias bi.laterN_succ_l]
theorem laterN_succ_left (n : Nat) {P : PROP} : ▷^[n + 1] P ⊣⊢ ▷ ▷^[n] P := .rfl

@[rocq_alias bi.laterN_succ_r]
theorem laterN_succ_right (n : Nat) {P : PROP} : ▷^[n + 1] P ⊣⊢ ▷^[n] ▷ P := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact later_congr ih

@[rocq_alias bi.laterN_add]
theorem laterN_add (n1 n2 : Nat) {P : PROP} : ▷^[n1 + n2] P ⊣⊢ ▷^[n1] ▷^[n2] P := by
  induction n1 with
  | zero => simp; exact .rfl
  | succ n1 ih => simp only [Nat.succ_add]; exact later_congr ih

@[rocq_alias bi.laterN_le]
theorem laterN_le {n1 n2 : Nat} {P : PROP} (h : n1 ≤ n2) : ▷^[n1] P ⊢ ▷^[n2] P := by
  induction h with
  | refl => exact .rfl
  | step _ ih => exact ih.trans later_intro

@[rocq_alias bi.laterN_intro]
theorem laterN_intro (n : Nat) {P : PROP} : P ⊢ ▷^[n] P := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact ih.trans later_intro

@[rocq_alias bi.laterN_True]
theorem laterN_true (n : Nat) : ▷^[n] True ⊣⊢@{PROP} True :=
  ⟨true_intro, laterN_intro n⟩

@[rocq_alias bi.laterN_emp]
theorem laterN_emp [BIAffine PROP] (n : Nat) : ▷^[n] emp ⊣⊢@{PROP} emp := calc
  _ ⊣⊢ ▷^[n] True := laterN_congr n true_emp.symm
  _ ⊣⊢ True        := laterN_true n
  _ ⊣⊢ emp         := true_emp

@[rocq_alias bi.laterN_forall]
theorem laterN_forall (n : Nat) {Φ : α → PROP} : ▷^[n] (∀ a, Φ a) ⊣⊢ (∀ a, ▷^[n] Φ a) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_forall

@[rocq_alias bi.laterN_exist_2]
theorem laterN_exists_mpr (n : Nat) {Φ : α → PROP} : (∃ a, ▷^[n] Φ a) ⊢ ▷^[n] (∃ a, Φ a) :=
  exists_elim fun a => laterN_mono n (exists_intro a)

@[rocq_alias bi.laterN_exist]
theorem laterN_exists [Inhabited α] (n : Nat) {Φ : α → PROP} :
    ▷^[n] (∃ a, Φ a) ⊣⊢ (∃ a, ▷^[n] Φ a) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_exists.symm

@[rocq_alias bi.laterN_and]
theorem laterN_and (n : Nat) {P Q : PROP} : ▷^[n] (P ∧ Q) ⊣⊢ ▷^[n] P ∧ ▷^[n] Q := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_and

@[rocq_alias bi.laterN_or]
theorem laterN_or (n : Nat) {P Q : PROP} : ▷^[n] (P ∨ Q) ⊣⊢ ▷^[n] P ∨ ▷^[n] Q := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_or

@[rocq_alias bi.laterN_impl]
theorem laterN_imp (n : Nat) {P Q : PROP} : ▷^[n] (P → Q) ⊢ ▷^[n] P → ▷^[n] Q :=
  imp_intro_swap <| (laterN_and n).2.trans <| laterN_mono n imp_elim_right

@[rocq_alias bi.laterN_sep]
theorem laterN_sep (n : Nat) {P Q : PROP} : ▷^[n] (P ∗ Q) ⊣⊢ ▷^[n] P ∗ ▷^[n] Q := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans $ later_sep

@[rocq_alias bi.laterN_wand]
theorem laterN_wand (n : Nat) {P Q : PROP} : ▷^[n] (P -∗ Q) ⊢ ▷^[n] P -∗ ▷^[n] Q :=
  wand_intro_left <| (laterN_sep n).2.trans <| laterN_mono n wand_elim_right

@[rocq_alias bi.laterN_iff]
theorem laterN_iff (n : Nat) {P Q : PROP} : ▷^[n] (P ↔ Q) ⊢ (▷^[n] P ↔ ▷^[n] Q) :=
  (laterN_and n).1.trans <|
    and_intro (and_elim_l.trans (laterN_imp n)) (and_elim_r.trans (laterN_imp n))

@[rocq_alias bi.laterN_persistently]
theorem laterN_persistently (n : Nat) {P : PROP} : ▷^[n] <pers> P ⊣⊢ <pers> ▷^[n] P := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (later_congr ih).trans later_persistently

@[rocq_alias bi.laterN_affinely_2]
theorem laterN_affinely (n : Nat) {P : PROP} : <affine> ▷^[n] P ⊢ ▷^[n] <affine> P :=
  (and_mono (laterN_intro n) .rfl).trans (laterN_and n).2

@[rocq_alias bi.laterN_intuitionistically_2]
theorem laterN_intuitionistically (n : Nat) {P : PROP} : □ ▷^[n] P ⊢ ▷^[n] □ P :=
  (affinely_mono (laterN_persistently n).2).trans (laterN_affinely n)

@[rocq_alias bi.laterN_intuitionistically_if_2]
theorem laterN_intuitionisticallyIf (n : Nat) {p : Bool} {P : PROP} :
    □?p ▷^[n] P ⊢ ▷^[n] □?p P :=
  match p with
  | false => .rfl
  | true => laterN_intuitionistically n

@[rocq_alias bi.laterN_absorbingly]
theorem laterN_absorbingly (n : Nat) {P : PROP} : ▷^[n] <absorb> P ⊣⊢ <absorb> ▷^[n] P :=
  (laterN_sep n).trans (sep_congr (laterN_true n) .rfl)

@[rocq_alias bi.laterN_persistent]
instance laterN_persistent (n : Nat) (P : PROP) [Persistent P] :
    Persistent iprop(▷^[n] P) := by
  induction n with
  | zero => assumption
  | succ n _ =>
    dsimp only [BIBase.laterN, Nat.repeat] at *
    exact later_persistent

@[rocq_alias bi.laterN_absorbing]
instance laterN_absorbing (n : Nat) (P : PROP) [Absorbing P] :
    Absorbing iprop(▷^[n] P) := by
  induction n with
  | zero => assumption
  | succ n _ =>
    dsimp only [BIBase.laterN, Nat.repeat] at *
    exact later_absorbing

/-! ## LaterN as a monoid homomorphism -/

@[rocq_alias bi.bi_laterN_and_homomorphism]
instance bi_laterN_and_homomorphism (n : Nat) :
    Algebra.MonoidHomomorphism (and (PROP := PROP)) and iprop(True) iprop(True) (· = ·)
      (iprop(▷^[n] · )) :=
  MonoidHomomorphism.ofEq (laterN_ne n)
    (equiv_iff.mpr (laterN_and n)) (equiv_iff.mpr (laterN_true n))

@[rocq_alias bi.bi_laterN_or_homomorphism]
instance bi_laterN_or_homomorphism (n : Nat) :
    Algebra.WeakMonoidHomomorphism (or (PROP := PROP)) or iprop(False) iprop(False) (· = ·)
      (iprop(▷^[n] · )) :=
  WeakMonoidHomomorphism.ofEq (laterN_ne n) (equiv_iff.mpr (laterN_or n))

@[rocq_alias bi.bi_laterN_sep_weak_homomorphism]
instance bi_laterN_sep_weak_homomorphism (n : Nat) :
    Algebra.WeakMonoidHomomorphism (sep (PROP := PROP)) sep emp emp (· = ·)
      (iprop(▷^[n] · )) :=
  WeakMonoidHomomorphism.ofEq (laterN_ne n) (equiv_iff.mpr (laterN_sep n))

@[rocq_alias bi.bi_laterN_sep_homomorphism]
instance bi_laterN_sep_homomorphism [BIAffine PROP] (n : Nat) :
    Algebra.MonoidHomomorphism (sep (PROP := PROP)) sep emp emp (· = ·)
      (iprop(▷^[n] · )) :=
  MonoidHomomorphism.ofEq (laterN_ne n)
    (equiv_iff.mpr (laterN_sep n)) (equiv_iff.mpr (laterN_emp n))

@[rocq_alias bi.bi_laterN_sep_entails_weak_homomorphism]
instance bi_laterN_sep_entails_weak_homomorphism (n : Nat) :
    Algebra.WeakMonoidHomomorphism (sep (PROP := PROP)) sep emp emp (flip Entails)
      (iprop(▷^[n] · )) where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := laterN_ne n
  map_op := (laterN_sep n).mpr

@[rocq_alias bi.bi_laterN_sep_entails_homomorphism]
instance bi_laterN_sep_entails_homomorphism (n : Nat) :
    Algebra.MonoidHomomorphism (sep (PROP := PROP)) sep emp emp (flip Entails)
      (iprop(▷^[n] · )) where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := laterN_ne n
  map_op := (laterN_sep n).mpr
  map_unit := laterN_intro n

/-! # Except0 -/

@[rocq_alias bi.except_0_ne]
theorem except0_ne : OFE.NonExpansive (BIBase.except0 (PROP:=PROP)) where
  ne _ _ _ h := or_ne.ne .rfl h

@[rw_mono_rule, rocq_alias bi.except_0_mono]
theorem except0_mono {P Q : PROP} (h : P ⊢ Q) : ◇ P ⊢ ◇ Q :=
  or_mono_right h
#rocq_ignore bi.except_0_mono' "Use except0_mono."
#rocq_ignore bi.except_0_flip_mono' "Use except0_mono"
#rocq_ignore bi.except_0_proper "Derivable from except0_ne with NonExpansive.eqv"

@[rw_mono_rule]
theorem except0_congr {P Q : PROP} (h : P ⊣⊢ Q) : ◇ P ⊣⊢ ◇ Q :=
  ⟨except0_mono h.1, except0_mono h.2⟩

@[rocq_alias bi.except_0_intro]
theorem except0_intro {P : PROP} : P ⊢ ◇ P := or_intro_r

@[rocq_alias bi.except_0_idemp]
theorem except0_idem {P : PROP} : ◇ ◇ P ⊣⊢ ◇ P :=
  ⟨or_elim or_intro_l .rfl, except0_intro⟩

@[rocq_alias bi.except_0_True]
theorem except0_true : ◇ True ⊣⊢ (True : PROP) :=
  ⟨true_intro, except0_intro⟩

@[rocq_alias bi.except_0_emp]
theorem except0_emp [BIAffine PROP] : ◇ emp ⊣⊢ (emp : PROP) := calc
  _ ⊣⊢ ◇ True := except0_congr true_emp.symm
  _ ⊣⊢ True    := except0_true
  _ ⊣⊢ emp     := true_emp

@[rocq_alias bi.except_0_or]
theorem except0_or {P Q : PROP} : ◇ (P ∨ Q) ⊣⊢ ◇ P ∨ ◇ Q :=
  ⟨or_elim (or_intro_l.trans or_intro_l)
    (or_elim (or_intro_l.trans (or_mono_left or_intro_r)) (or_intro_r.trans (or_mono_right or_intro_r))),
   or_elim (or_mono_right or_intro_l) (or_mono_right or_intro_r)⟩

@[rocq_alias bi.except_0_and]
theorem except0_and {P Q : PROP} : ◇ (P ∧ Q) ⊣⊢ ◇ P ∧ ◇ Q :=
  or_and_left

@[rocq_alias bi.except_0_sep]
theorem except0_sep {P Q : PROP} : ◇ (P ∗ Q) ⊣⊢ ◇ P ∗ ◇ Q := by
  constructor
  · apply or_elim
    · apply Entails.trans _ (sep_mono or_intro_l or_intro_l)
      apply Entails.trans _ (later_sep.1)
      apply later_mono
      apply false_elim
    · exact sep_mono or_intro_r or_intro_r
  · apply Entails.trans sep_or_right.1 _
    apply or_elim
    · apply or_intro_left_trans
      apply sep_elim_left
    · apply sep_comm.1.trans _
      apply Entails.trans sep_or_right.1
      apply or_elim
      · apply or_intro_left_trans
        apply sep_elim_left
      · apply or_intro_right_trans
        apply sep_comm.1

@[rocq_alias bi.except_0_forall]
theorem except0_forall {Φ : α → PROP} : ◇ (∀ a, Φ a) ⊣⊢ ∀ a, ◇ Φ a := by
  refine ⟨forall_intro (except0_mono <| forall_elim ·), ?_⟩
  refine (and_intro ((forall_mono λ _ =>
           (or_elim (later_mono false_elim) later_intro)).trans later_forall.2) .rfl).trans ?_
  refine and_mono_left later_false_em |>.trans ?_
  refine and_or_right.1.trans ?_
  refine or_elim ?_ ?_
  · exact and_elim_l.trans or_intro_l
  · refine or_intro_right_trans ?_
    refine forall_intro λ a => ?_
    refine imp_elim_swap <| forall_elim a |>.trans ?_
    refine or_elim (imp_intro <| imp_elim_right.trans <| forall_elim a) (imp_intro and_elim_l)

@[rocq_alias bi.except_0_exist_2]
theorem except0_exists_mpr {Φ : α → PROP} : (∃ a, ◇ Φ a) ⊢ ◇ ∃ a, Φ a :=
  exists_elim fun a => except0_mono (exists_intro a)

@[rocq_alias bi.except_0_exist]
theorem except0_exists [Inhabited α] {Φ : α → PROP} :
    ◇ (∃ a, Φ a) ⊣⊢ ∃ a, ◇ Φ a :=
  ⟨or_elim ((exists_intro (Ψ:=λ _ =>_) default).trans <| exists_mono fun _ => or_intro_l)
           (exists_mono fun _ => except0_intro),
   except0_exists_mpr⟩

@[rocq_alias bi.except_0_later]
theorem except0_later {P : PROP} : ◇ ▷ P ⊢ ▷ P :=
  (or_elim (later_mono false_elim) .rfl)

@[rocq_alias bi.except_0_laterN]
theorem except0_laterN (n : Nat) {P : PROP} : ◇ ▷^[n] P ⊢ ▷^[n] ◇ P :=
  match n with
  | 0 => .rfl
  | _ + 1 => except0_later.trans <| (later_mono (except0_intro.trans (except0_laterN _)))

@[rocq_alias bi.except_0_into_later]
theorem except0_into_later {P : PROP} : ◇ P ⊢ ▷ P :=
  (except0_mono later_intro).trans except0_later

@[rocq_alias bi.except_0_persistently_1]
theorem except0_persistently_mp {P : PROP} : ◇ <pers> P ⊢ <pers> ◇ P :=
  (or_mono_left <|
    (later_congr persistently_pure.symm).mp.trans later_persistently.mp).trans
      persistently_or_mpr

@[rocq_alias bi.except_0_persistently]
theorem except0_persistently [BIPersistentlyExist PROP] {P : PROP} :
    ◇ <pers> P ⊣⊢ <pers> ◇ P := by
  apply BiEntails.trans _ persistently_or.symm
  apply or_congr_left
  apply BiEntails.trans _ later_persistently
  apply later_congr persistently_pure.symm

@[rocq_alias bi.except_0_affinely_2]
theorem except0_affinely {P : PROP} : <affine> ◇ P ⊢ ◇ <affine> P :=
  (and_mono_left except0_intro).trans except0_and.2

@[rocq_alias bi.except_0_intuitionistically_2]
theorem except0_intuitionistically [BIPersistentlyExist PROP] {P : PROP} :
    □ ◇ P ⊢ ◇ □ P :=
  (affinely_mono except0_persistently.2).trans except0_affinely

@[rocq_alias bi.except_0_intuitionistically_if_2]
theorem except0_intuitionisticallyIf [BIPersistentlyExist PROP] {p : Bool} {P : PROP} :
    □?p ◇ P ⊢ ◇ □?p P :=
  match p with
  | false => .rfl
  | true => except0_intuitionistically

@[rocq_alias bi.except_0_absorbingly]
theorem except0_absorbingly {P : PROP} : ◇ <absorb> P ⊣⊢ <absorb> ◇ P :=
  except0_sep.trans <| sep_congr except0_true .rfl

@[rocq_alias bi.except_0_frame_l]
theorem except0_frame_left {P Q : PROP} : P ∗ ◇ Q ⊢ ◇ (P ∗ Q) :=
  (sep_mono_left except0_intro).trans except0_sep.2

@[rocq_alias bi.except_0_frame_r]
theorem except0_frame_right {P Q : PROP} : ◇ P ∗ Q ⊢ ◇ (P ∗ Q) :=
  (sep_mono_right except0_intro).trans except0_sep.2

@[rocq_alias bi.later_affinely_1]
theorem later_affinely_mp {P : PROP} [Timeless (PROP := PROP) emp] :
    ▷ <affine> P ⊢ ◇ <affine> ▷ P := calc
  _ ⊢ ▷ emp ∧ ▷ P    := later_and.mp
  _ ⊢ ◇ emp ∧ ▷ P    := and_mono_left Timeless.timeless
  _ ⊢ ◇ emp ∧ ◇ ▷ P := and_mono_right except0_intro
  _ ⊢ ◇ (emp ∧ ▷ P)  := except0_and.mpr

@[rocq_alias bi.except_0_persistent]
instance except0_persistent (P : PROP) [Persistent P] : Persistent iprop(◇ P) :=
  inferInstanceAs (Persistent iprop(_ ∨ _))

@[rocq_alias bi.except_0_absorbing]
instance except0_absorbing (P : PROP) [Absorbing P] : Absorbing iprop(◇ P) :=
  inferInstanceAs (Absorbing iprop(_ ∨ _))

/-! ## Except-0 as a monoid homomorphism -/

@[rocq_alias bi.bi_except_0_and_homomorphism]
instance bi_except0_and_homomorphism :
    Algebra.MonoidHomomorphism (and (PROP := PROP)) and iprop(True) iprop(True) (· = ·)
      (iprop(◇ ·)) :=
  MonoidHomomorphism.ofEq except0_ne
    (equiv_iff.mpr except0_and) (equiv_iff.mpr except0_true)

@[rocq_alias bi.bi_except_0_or_homomorphism]
instance bi_except0_or_homomorphism :
    Algebra.WeakMonoidHomomorphism (or (PROP := PROP)) or iprop(False) iprop(False) (· = ·)
      (iprop(◇ ·)) :=
  WeakMonoidHomomorphism.ofEq except0_ne (equiv_iff.mpr except0_or)

@[rocq_alias bi.bi_except_0_sep_weak_homomorphism]
instance bi_except0_sep_weak_homomorphism :
    Algebra.WeakMonoidHomomorphism (sep (PROP := PROP)) sep emp emp (· = ·)
      (iprop(◇ ·)) :=
  WeakMonoidHomomorphism.ofEq except0_ne (equiv_iff.mpr except0_sep)

@[rocq_alias bi.bi_except_0_sep_homomorphism]
instance bi_except0_sep_homomorphism [BIAffine PROP] :
    Algebra.MonoidHomomorphism (sep (PROP := PROP)) sep emp emp (· = ·)
      (iprop(◇ ·)) :=
  MonoidHomomorphism.ofEq except0_ne
    (equiv_iff.mpr except0_sep) (equiv_iff.mpr except0_emp)

@[rocq_alias bi.bi_except_0_sep_entails_weak_homomorphism]
instance bi_except0_sep_entails_weak_homomorphism :
    Algebra.WeakMonoidHomomorphism (sep (PROP := PROP)) sep emp emp (flip Entails)
      (iprop(◇ ·)) where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := except0_ne
  map_op := except0_sep.mpr

@[rocq_alias bi.bi_except_0_sep_entails_homomorphism]
instance bi_except0_sep_entails_homomorphism :
    Algebra.MonoidHomomorphism (sep (PROP := PROP)) sep emp emp (flip Entails)
      (iprop(◇ ·)) where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := except0_ne
  map_op := except0_sep.mpr
  map_unit := except0_intro

/-! # Only-0 and Timeless -/

@[rw_mono_rule, rocq_alias bi.only_0_mono]
theorem only0_mono {P Q : PROP} (h : P ⊢ Q) : <only0> P ⊢ <only0> Q := imp_mono_right h

#rocq_ignore bi.only_0_mono' "No Proper type class in Lean"
#rocq_ignore bi.only_0_flip_mono' "No Proper type class in Lean"
#rocq_ignore bi.only_0_proper "No Proper type class in Lean"

@[rw_mono_rule]
theorem only0_congr {P Q : PROP} (h : P ⊣⊢ Q) : <only0> P ⊣⊢ <only0> Q :=
  ⟨only0_mono h.mp, only0_mono h.mpr⟩

@[rocq_alias bi.only_0_intro]
theorem only0_intro {P : PROP} : P ⊢ <only0> P := imp_intro and_elim_l

@[rocq_alias bi.only_0_idemp]
theorem only0_idem {P : PROP} : <only0> <only0> P ⊣⊢ <only0> P :=
  impl_curry.trans (imp_congr_left and_self)

@[rocq_alias bi.except_0_and_only_0]
theorem except0_and_only0 {P Q : PROP} : <only0> P ∧ ◇ Q ⊢ P ∨ Q :=
  and_or_left.mp.trans <|
    or_elim (imp_elim_left.trans or_intro_l) (and_elim_r.trans or_intro_r)

@[rocq_alias bi.except_0_and_only_0_self]
theorem except0_and_only0_self {P : PROP} : <only0> P ∧ ◇ P ⊣⊢ P := by
  constructor
  · exact except0_and_only0.trans or_self.mp
  · exact and_intro only0_intro except0_intro

@[rocq_alias bi.later_except_0_only_0]
theorem later_except0_only0 {P : PROP} : ▷ P ⊢ ◇ <only0> P := later_false_em

@[rocq_alias bi.only_0_and]
theorem only0_and {P Q : PROP} : <only0> (P ∧ Q) ⊣⊢ <only0> P ∧ <only0> Q := by
  refine ⟨and_intro (only0_mono and_elim_l) (only0_mono and_elim_r), imp_intro (and_intro ?_ ?_)⟩
  · exact (and_mono_left and_elim_l).trans imp_elim_left
  · exact (and_mono_left and_elim_r).trans imp_elim_left

@[rocq_alias bi.only_0_wand]
theorem only0_wand {P Q : PROP} : <only0> (P -∗ Q) ⊢ <only0> P -∗ <only0> Q := by
  refine wand_intro <| imp_intro ?_
  calc
    _ ⊢ ▷ False ∧ (▷ False → P -∗ Q) ∗ (▷ False → P) := and_comm.mp
    _ ⊢ (▷ False ∧ (▷ False → P -∗ Q)) ∗ ▷ False ∧ (▷ False → P) := persistent_and_sep_distrib
    _ ⊢ (P -∗ Q) ∗ P := sep_mono imp_elim_right imp_elim_right
    _ ⊢ Q := wand_elim_left

theorem only0_wand_mpr {P Q : PROP} : (<only0> P -∗ <only0> Q) ⊢ <only0> (P -∗ Q) := by
  refine imp_intro <| wand_intro
    ((and_intro ?_ ((sep_mono_left and_elim_r).trans sep_elim_left)).trans imp_elim_left)
  calc
    _ ⊢ (<only0> P -∗ <only0> Q) ∗ P         := sep_mono_left and_elim_l
    _ ⊢ (<only0> P -∗ <only0> Q) ∗ <only0> P := sep_mono_right only0_intro
    _ ⊢ <only0> Q                            := wand_elim_left

@[rocq_alias bi.only_0_wand_iff]
theorem only0_wandIff {P Q : PROP} : <only0> (P ∗-∗ Q) ⊣⊢ (<only0> P ∗-∗ <only0> Q) := by
  constructor
  · exact only0_and.mp.trans (and_mono only0_wand only0_wand)
  · exact (and_mono only0_wand_mpr only0_wand_mpr).trans only0_and.mpr

@[rocq_alias bi.only_0_forall]
theorem only0_forall {Φ : α → PROP} : <only0> (∀ a, Φ a) ⊣⊢ ∀ a, <only0> Φ a := by
  constructor
  · exact forall_intro fun x => only0_mono (forall_elim x)
  · exact imp_intro <| forall_intro fun x => (and_mono_left (forall_elim x)).trans imp_elim_left

@[rocq_alias bi.only_0_impl_r]
theorem only0_imp_r {P Q : PROP} : <only0> (P → Q) ⊣⊢ (P → <only0> Q) :=
  impl_curry.trans <| (imp_congr_left and_comm).trans impl_curry.symm

@[rocq_alias bi.only_0_impl]
theorem only0_imp {P Q : PROP} : <only0> (P → Q) ⊣⊢ (<only0> P → <only0> Q) := by
  constructor
  · exact imp_intro <| only0_and.mpr.trans (only0_mono imp_elim_left)
  · exact (imp_mono_left only0_intro).trans only0_imp_r.mpr

@[rocq_alias bi.only_0_iff]
theorem only0_iff {P Q : PROP} : <only0> (P ↔ Q) ⊣⊢ (<only0> P ↔ <only0> Q) :=
  only0_and.trans (and_congr only0_imp only0_imp)

@[rocq_alias bi.only_0_wand_r]
theorem only0_wand_r {P Q : PROP} : <only0> (P -∗ Q) ⊣⊢ (P -∗ <only0> Q) := by
  refine ⟨wand_intro <| imp_intro ?_, imp_intro <| wand_intro ?_⟩
  · calc iprop((<only0> (P -∗ Q) ∗ P) ∧ ▷ False)
      _ ⊢ ▷ False ∧ (<only0> (P -∗ Q) ∗ P)              := and_comm.mp
      _ ⊢ (▷ False ∧ <only0> (P -∗ Q)) ∗ (▷ False ∧ P) := persistent_and_sep_distrib
      _ ⊢ (P -∗ Q) ∗ P                                   := sep_mono imp_elim_right and_elim_r
      _ ⊢ Q                                              := wand_elim_left
  · exact
      (and_intro ((sep_mono_left and_elim_r).trans sep_elim_left)
      ((sep_mono_left and_elim_l).trans wand_elim_left)).trans imp_elim_right

@[rocq_alias bi.only_0_persistently_2]
theorem only0_persistently_mpr {P : PROP} : <pers> <only0> P ⊢ <only0> <pers> P := by
  refine imp_intro ?_
  calc iprop(<pers> <only0> P ∧ ▷ False)
    _ ⊢ <pers> <only0> P ∧ <pers> ▷ False := and_mono_right persistently_intro
    _ ⊢ <pers> (<only0> P ∧ ▷ False)      := persistently_and.mpr
    _ ⊢ <pers> P                           := persistently_mono imp_elim_left

@[rocq_alias bi.only_0_absorbing]
instance only0_absorbing (P : PROP) [Absorbing P] : Absorbing iprop(<only0> P) :=
  inferInstanceAs (Absorbing iprop(▷ False → P))

@[rocq_alias bi.timeless_alt]
theorem timeless_alt [BILoeb PROP] {P : PROP} : Timeless P ↔ (<only0> P ⊢ P) := by
  refine ⟨fun _ => ?_, fun h => ⟨later_false_em.trans (or_mono_right h)⟩⟩
  refine Entails.trans (imp_intro ?_) loeb
  calc iprop(<only0> P ∧ ▷ P)
    _ ⊢ <only0> P ∧ ◇ P := and_mono_right Timeless.timeless
    _ ⊢ P                := except0_and_only0_self.mp

@[rocq_alias bi.timeless_only_0]
theorem timeless_only0 [BILoeb PROP] {P : PROP} [instTimeless : Timeless P] : <only0> P ⊣⊢ P := by
  constructor
  · exact timeless_alt.mp instTimeless
  · exact only0_intro

@[rocq_alias bi.only_0_elim_timeless]
theorem only0_elim_timeless [BILoeb PROP] {P : PROP} [Timeless P] : <only0> P ⊢ P :=
  timeless_only0.mp

#rocq_ignore bi.Timeless_proper "Derivable from the BI structure; Timeless is preserved under ⊣⊢."

@[rocq_alias bi.pure_timeless]
instance pure_timeless (φ : Prop) : Timeless (PROP := PROP) (BIBase.pure φ) where
  timeless :=
    calc iprop(▷ ⌜φ⌝)
      _ ⊢@{PROP} ▷ ∃ (_a : φ), True :=
        later_mono (pure_elim' (true_intro.trans <| exists_intro (Ψ := fun _ => iprop(⌜True⌝)) ·))
      _ ⊢ ▷ False ∨ ∃ (_a : φ), ▷ True :=
        later_exists_false
      _ ⊢ ◇ ⌜φ⌝ :=
        or_mono_right (exists_elim ((later_true.1.trans true_intro).trans <| pure_intro ·))

@[rocq_alias bi.exist_timeless]
instance exists_timeless [BI PROP] {α : Type _} (Ψ : α → PROP) [∀ x, Timeless (Ψ x)] :
    Timeless (PROP := PROP) (BIBase.exists Ψ) where
  timeless := by
    refine later_exists_false.trans ?_
    refine or_elim or_intro_l ?_
    refine exists_elim fun x => ?_
    refine Timeless.timeless.trans ?_
    exact except0_mono (exists_intro x)

@[rocq_alias bi.emp_timeless]
instance emp_timeless [BI PROP] [BIAffine PROP] : Timeless (PROP := PROP) emp where
  timeless := later_emp.mp.trans except0_intro

@[rocq_alias bi.and_timeless]
instance and_timeless [BI PROP] {P Q : PROP} [Timeless P] [Timeless Q] :
    Timeless (PROP := PROP) (BIBase.and P Q) where
  timeless := calc iprop(▷ (P ∧ Q))
      _ ⊢ ▷ P ∧ ▷ Q := later_and.mp
      _ ⊢ ◇ P ∧ ◇ Q := and_mono Timeless.timeless Timeless.timeless
      _ ⊢ ◇ (P ∧ Q)  := except0_and.mpr

@[rocq_alias bi.or_timeless]
instance or_timeless [BI PROP] {P Q : PROP} [Timeless P] [Timeless Q] :
    Timeless (PROP := PROP) (BIBase.or P Q) where
  timeless := calc iprop(▷ (P ∨ Q))
      _ ⊢ ▷ P ∨ ▷ Q := later_or.mp
      _ ⊢ ◇ P ∨ ◇ Q := or_mono Timeless.timeless Timeless.timeless
      _ ⊢ ◇ (P ∨ Q)  := except0_or.mpr

@[rocq_alias bi.impl_timeless]
instance impl_timeless [BI PROP] [BILoeb PROP] {P Q : PROP} [Timeless Q] :
    Timeless (PROP := PROP) (BIBase.imp P Q) :=
  timeless_alt.mpr <| only0_imp.mp.trans (imp_mono only0_intro only0_elim_timeless)

@[rocq_alias bi.sep_timeless]
instance sep_timeless [BI PROP] {P Q : PROP} [Timeless P] [Timeless Q] :
    Timeless (PROP := PROP) (BIBase.sep P Q) where
  timeless :=
    calc iprop(▷ (P ∗ Q))
      _ ⊢ ▷ P ∗ ▷ Q := later_sep.mp
      _ ⊢ ◇ P ∗ ◇ Q := sep_mono Timeless.timeless Timeless.timeless
      _ ⊢ ◇ (P ∗ Q) := except0_sep.mpr

@[rocq_alias bi.wand_timeless]
instance wand_timeless [BI PROP] [BILoeb PROP] {P Q : PROP} [Timeless Q] :
    Timeless (PROP := PROP) (BIBase.wand P Q) := timeless_alt.mpr <| only0_wand.trans (wand_mono only0_intro only0_elim_timeless)

instance wandIff_timeless [BI PROP] [BILoeb PROP] {P Q : PROP} [Timeless P] [Timeless Q] :
    Timeless (PROP := PROP) (wandIff P Q) :=
  inferInstanceAs (Timeless (PROP := PROP) iprop((P -∗ Q) ∧ (Q -∗ P)))

@[rocq_alias bi.forall_timeless]
instance forall_timeless [BI PROP] {α : Type _} (Ψ : α → PROP) [∀ x, Timeless (Ψ x)] :
    Timeless (PROP := PROP) (BIBase.forall Ψ) where
  timeless := by
    refine later_forall.mp.trans ?_
    refine (forall_mono fun x => Timeless.timeless).trans ?_
    exact except0_forall.mpr

@[rocq_alias bi.persistently_timeless]
instance persistently_timeless [BI PROP] [BIPersistentlyExist PROP] {P : PROP} [Timeless P] :
    Timeless (PROP := PROP) iprop(<pers> P) where
  timeless :=
    calc iprop(▷ <pers> P)
      _ ⊢ <pers> ▷ P := later_persistently.mp
      _ ⊢ <pers> ◇ P := persistently_mono Timeless.timeless
      _ ⊢ ◇ <pers> P := except0_persistently.mpr

@[rocq_alias bi.affinely_timeless]
instance affinely_timeless [BI PROP] [Timeless (PROP := PROP) emp] {P : PROP} [Timeless P] :
    Timeless (PROP := PROP) iprop(<affine> P) := and_timeless

@[rocq_alias bi.absorbingly_timeless]
instance absorbingly_timeless [BI PROP] {P : PROP} [Timeless P] :
    Timeless (PROP := PROP) iprop(<absorb> P) where
  timeless :=
    calc iprop(▷ <absorb> P)
      _ ⊢ <absorb> ▷ P := later_absorbingly.mp
      _ ⊢ <absorb> ◇ P := absorbingly_mono Timeless.timeless
      _ ⊢ ◇ <absorb> P := except0_absorbingly.mpr

@[rocq_alias bi.intuitionistically_timeless]
instance intuitionistically_timeless [BI PROP] [BIPersistentlyExist PROP]
    [Timeless (PROP := PROP) emp] {P : PROP} [Timeless P] : Timeless (PROP := PROP) iprop(□ P) :=
  affinely_timeless

@[rocq_alias bi.from_option_timeless]
instance from_option_timeless [BI PROP] {α : Type _} {Ψ : α → PROP} {P : PROP}
    [Timeless P] [∀ x, Timeless (Ψ x)] (mx : Option α) :
    Timeless (Option.elim mx P Ψ) :=
  match mx with
  | none => inferInstanceAs (Timeless P)
  | some x => inferInstanceAs (Timeless (Ψ x))

@[rocq_alias bi.timeless_laterN]
theorem timeless_laterN {P : PROP} [Timeless P] (n : Nat) :
    (▷^[n] P) ⊢ (▷^[n] False ∨ P) := by
  induction n with
  | zero => exact or_intro_r
  | succ n IH =>
    calc
      _ ⊢ ▷ (▷^[n] False ∨ P)                   := later_mono IH
      _ ⊢ ▷ ▷^[n] False ∨ ▷ P                  := later_or.mp
      _ ⊢ ▷ ▷^[n] False ∨ ◇ P                  := or_mono_right Timeless.timeless
      _ ⊢ ▷ ▷^[n] False ∨ ▷ ▷^[n] False ∨ P   :=
          or_mono_right <| or_mono_left <| later_mono <| laterN_intro n
      _ ⊢ (▷ ▷^[n] False ∨ ▷ ▷^[n] False) ∨ P := or_assoc.mpr
      _ ⊢ ▷^[n + 1] False ∨ P                    := or_mono_left or_self.mp

@[rocq_alias bi.only_0_timeless]
instance only0_timeless {P : PROP} : Timeless iprop(<only0> P) where
  timeless := later_except0_only0.trans (except0_mono only0_idem.mp)

@[rocq_alias bi.only_0_exist]
theorem only0_exists [BILoeb PROP] {α : Type _} {Φ : α → PROP} :
    <only0> (∃ a, Φ a) ⊣⊢ ∃ a, <only0> Φ a := by
  constructor
  · exact (only0_mono <| exists_mono fun _ => only0_intro).trans (timeless_alt.mp inferInstance)
  · exact exists_elim fun a => only0_mono (exists_intro a)

@[rocq_alias bi.only_0_or]
theorem only0_or [BILoeb PROP] {P Q : PROP} : <only0> (P ∨ Q) ⊣⊢ <only0> P ∨ <only0> Q := by
  constructor
  · exact (only0_mono <| or_mono only0_intro only0_intro).trans (timeless_alt.mp inferInstance)
  · exact or_elim (only0_mono or_intro_l) (only0_mono or_intro_r)

@[rocq_alias bi.only_0_pure]
theorem only0_pure [BILoeb PROP] {φ : Prop} : <only0> ⌜φ⌝ ⊣⊢@{PROP} ⌜φ⌝ := timeless_only0

@[rocq_alias bi.only_0_emp]
theorem only0_emp [BILoeb PROP] [Timeless (PROP := PROP) emp] :
    <only0> emp ⊣⊢ (emp : PROP) := timeless_only0

@[rocq_alias bi.only_0_sep]
theorem only0_sep [BILoeb PROP] {P Q : PROP} : <only0> (P ∗ Q) ⊣⊢ <only0> P ∗ <only0> Q := by
  refine ⟨?_, imp_intro ?_⟩
  · exact (only0_mono <| sep_mono only0_intro only0_intro).trans
      (timeless_alt.mp inferInstance)
  · calc iprop((<only0> P ∗ <only0> Q) ∧ ▷ False)
      _ ⊢ ▷ False ∧ (<only0> P ∗ <only0> Q) := and_comm.mp
      _ ⊢ (▷ False ∧ <only0> P) ∗ (▷ False ∧ <only0> Q) := persistent_and_sep_distrib
      _ ⊢ P ∗ Q := sep_mono imp_elim_right imp_elim_right

@[rocq_alias bi.only_0_absorbingly]
theorem only0_absorbingly [BILoeb PROP] {P : PROP} :
    <only0> <absorb> P ⊣⊢ <absorb> <only0> P :=
  only0_sep.trans (sep_congr_left only0_pure)

@[rocq_alias bi.only_0_affinely]
theorem only0_affinely [BILoeb PROP] [Timeless (PROP := PROP) emp] {P : PROP} :
    <only0> <affine> P ⊣⊢ <affine> <only0> P :=
  only0_and.trans (and_congr_left only0_emp)

@[rocq_alias bi.only_0_intuitionistically_2]
theorem only0_intuitionistically_mpr [BILoeb PROP] [Timeless (PROP := PROP) emp] {P : PROP} :
    □ <only0> P ⊢ <only0> □ P :=
  (affinely_mono only0_persistently_mpr).trans only0_affinely.mpr

@[rocq_alias bi.only_0_later]
theorem only0_later {P : PROP} : <only0> ▷ P ⊣⊢ True := by
  constructor
  · exact true_intro
  · exact imp_intro <| and_elim_r.trans (later_mono false_elim)

@[rocq_alias bi.only_0_except_0]
theorem only0_except0 [BILoeb PROP] {P : PROP} : <only0> ◇ P ⊣⊢ True := calc
  _ ⊣⊢ <only0> ▷ False ∨ <only0> P := only0_or
  _ ⊣⊢ True ∨ <only0> P             := or_congr_left only0_later
  _ ⊣⊢ True                         := true_or
