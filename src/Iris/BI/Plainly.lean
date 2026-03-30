/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Sbi
public import Iris.BI.Classes
public import Iris.BI.BI
public import Iris.BI.DerivedLaws
public import Iris.Algebra

@[expose] public section

namespace Iris
open BI

namespace BI
open Iris.Std

class Plain [BI PROP] [BIBase.Plainly PROP] (P : PROP) where
  plain : P ⊢ ■ P

section PlainlyLaws

variable [Sbi PROP]
variable {P Q R : PROP}

instance (P : PROP) : Plain iprop(■ P) := ⟨plainly_idemp_2⟩

theorem affinely_plainly_elim : <affine> ■ P ⊢ P :=
  (affinely_mono plainly_elim_persistently).trans persistently_and_emp_elim

theorem persistently_elim_plainly : <pers> ■ P ⊣⊢ ■ P :=
  ⟨absorbingly_of_persistently.trans <| sep_symm.trans plainly_absorb,
   plainly_idemp_2.trans plainly_elim_persistently⟩

nonrec theorem plainly_forall_2 {A : Type _} {Ψ : A → PROP} : (∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a) :=
  plainly_forall_2 _

theorem plainly_persistently_elim : ■ <pers> P ⊣⊢ ■ P := by
  refine ⟨?_, plainly_idemp_2.trans <| plainly_mono plainly_elim_persistently⟩
  calc iprop(■ <pers> P)
    _ ⊢ ■ emp ∧ ■ <pers> P := true_and.2.trans <| and_mono plainly_emp_intro .rfl
    _ ⊢ ∀ (b : Bool), if b then ■ emp else ■ <pers> P := and_forall_bool.1
    _ ⊢ ∀ (b : Bool), ■ (if b then emp else <pers> P) := forall_mono (·.casesOn .rfl .rfl)
    _ ⊢ ■ ∀ (b : Bool), if b then emp else <pers> P := plainly_forall_2
    _ ⊢ ■ (emp ∧ <pers> P) := plainly_mono and_forall_bool.2
    _ ⊢ ■ P := plainly_mono persistently_and_emp_elim

theorem absorbingly_elim_plainly : <absorb> ■ P ⊣⊢ ■ P :=
  calc iprop(<absorb> ■ P)
    _ ⊣⊢ <absorb> <pers> ■ P :=
        ⟨absorbingly_mono persistently_elim_plainly.2, absorbingly_mono persistently_elim_plainly.1⟩
    _ ⊣⊢ <pers> ■ P := absorbingly_persistently
    _ ⊣⊢ ■ P := persistently_elim_plainly

theorem plainly_and_sep_elim : ■ P ∧ Q ⊢ (emp ∧ P) ∗ Q :=
  (and_mono plainly_elim_persistently .rfl).trans persistently_and_sep_elim_emp

theorem plainly_and_sep_assoc : ■ P ∧ (Q ∗ R) ⊣⊢ (■ P ∧ Q) ∗ R :=
  calc iprop(■ P ∧ (Q ∗ R))
    _ ⊣⊢ <pers> ■ P ∧ (Q ∗ R) := and_congr_l persistently_elim_plainly.symm
    _ ⊣⊢ (<pers> ■ P ∧ Q) ∗ R := persistently_and_sep_assoc
    _ ⊣⊢ (■ P ∧ Q) ∗ R := sep_congr_l (and_congr_l persistently_elim_plainly)

theorem plainly_and_emp_elim : emp ∧ ■ P ⊢ P :=
  (and_mono .rfl plainly_elim_persistently).trans persistently_and_emp_elim

theorem plainly_into_absorbingly : ■ P ⊢ <absorb> P :=
  plainly_elim_persistently.trans absorbingly_of_persistently

theorem plainly_elim [Absorbing P] : ■ P ⊢ P :=
  plainly_elim_persistently.trans persistently_elim

theorem plainly_idemp : ■ ■ P ⊣⊢ ■ P :=
  ⟨plainly_into_absorbingly.trans absorbingly_elim_plainly.1, plainly_idemp_2⟩

theorem plainly_intro' (H : ■ P ⊢ Q) : ■ P ⊢ ■ Q :=
  plainly_idemp.2.trans <| plainly_mono <| H

theorem plainly_pure {φ} : ■ ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  refine ⟨plainly_elim_persistently.trans persistently_elim, ?_⟩
  refine pure_elim' fun φ => ?_
  exact (forall_intro (Ψ := fun _ => iprop(■ True)) Empty.rec).trans <|
    plainly_forall_2.trans (plainly_mono <| true_intro.trans <| pure_intro φ)

theorem plainly_forall {A : Type _} {Ψ : A → PROP} : ■ (∀ a, Ψ a) ⊣⊢ ∀ a, ■ (Ψ a) :=
  ⟨forall_intro (plainly_mono <| forall_elim ·), plainly_forall_2⟩

theorem plainly_exists_2 {α : Sort _} {Ψ : α → PROP} : (∃ a, ■ (Ψ a)) ⊢ ■ (∃ a, Ψ a) :=
  exists_elim (plainly_mono <| exists_intro ·)

theorem plainly_exists_1 [SbiEmpValidExist PROP] {A : Type _} {Ψ : A → PROP} :
    ■ (∃ a, Ψ a) ⊢ ∃ a, ■ (Ψ a) :=
  plainly_exist_1 _

theorem plainly_exists [SbiEmpValidExist PROP] {A : Type _} {Ψ : A → PROP} : ■ (∃ a, Ψ a) ⊣⊢ ∃ a, ■ (Ψ a) :=
  ⟨plainly_exists_1, plainly_exists_2⟩

theorem plainly_and : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q := by
  constructor
  · refine (plainly_mono and_forall_bool.mp).trans (.trans ?_ and_forall_bool.mpr)
    exact plainly_forall.mp.trans (forall_mono (·.casesOn .rfl .rfl))
  · refine (and_forall_bool.mp).trans (.trans ?_ (plainly_mono <| and_forall_bool.mpr))
    refine .trans (forall_mono ?_) plainly_forall.mpr
    exact (·.casesOn .rfl .rfl)

theorem plainly_or_2 : ■ P ∨ ■ Q ⊢ ■ (P ∨ Q) := by
  refine or_exists_bool.mp.trans (.trans ?_ (plainly_mono <| or_exists_bool.mpr))
  refine .trans (exists_mono ?_) plainly_exists_2
  exact (·.casesOn .rfl .rfl)

theorem plainly_or [SbiEmpValidExist PROP] : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q := by
  refine ⟨?_, plainly_or_2⟩
  refine (plainly_mono or_exists_bool.mp).trans (.trans ?_ or_exists_bool.mpr)
  exact plainly_exists_1.trans <| exists_mono (·.casesOn .rfl .rfl)

theorem plainly_impl : ■ (P → Q) ⊢ ■ P → ■ Q := by
  refine imp_intro' <| plainly_and.mpr.trans ?_
  exact plainly_mono imp_elim_r

theorem plainly_emp_2 : (emp : PROP) ⊢ ■ emp := plainly_emp_intro

theorem plainly_sep_dup : ■ P ⊣⊢ ■ P ∗ ■ P := by
  refine ⟨?_, plainly_absorb⟩
  calc iprop(■ P)
    _ ⊢ ■ P ∧ ■ P := and_self.2
    _ ⊢ ■ P ∧ (emp ∗ ■ P) := and_mono .rfl emp_sep.2
    _ ⊢ (■ P ∧ emp) ∗ ■ P := plainly_and_sep_assoc.1
    _ ⊢ ■ P ∗ ■ P := sep_mono and_elim_l .rfl

theorem plainly_and_sep_l_1 : ■ P ∧ Q ⊢ ■ P ∗ Q :=
  calc iprop(■ P ∧ Q)
    _ ⊢ ■ P ∧ (emp ∗ Q) := and_mono .rfl emp_sep.2
    _ ⊢ (■ P ∧ emp) ∗ Q := plainly_and_sep_assoc.1
    _ ⊢ ■ P ∗ Q := sep_mono and_elim_l .rfl

theorem plainly_and_sep_r_1 : P ∧ ■ Q ⊢ P ∗ ■ Q :=
  and_comm.1.trans <| plainly_and_sep_l_1.trans sep_symm

theorem plainly_true_emp : ■ True ⊣⊢ ■ (emp : PROP) :=
  ⟨plainly_emp_intro, plainly_mono true_intro⟩

theorem plainly_and_sep : ■ (P ∧ Q) ⊢ ■ (P ∗ Q) :=
  calc iprop(■ (P ∧ Q))
    _ ⊢ ■ ■ P ∧ ■ Q := plainly_and.mp.trans <| and_mono plainly_idemp_2 .rfl
    _ ⊢ ■ (■ P ∧ Q) := plainly_and.mpr
    _ ⊢ ■ (■ P ∧ (emp ∗ Q)) := plainly_mono <| and_mono .rfl emp_sep.mpr
    _ ⊢ ■ ((■ P ∧ emp) ∗ Q) := plainly_mono plainly_and_sep_assoc.1
    _ ⊢ ■ ((emp ∧ ■ P) ∗ Q) := plainly_mono <| sep_mono and_comm.mp .rfl
    _ ⊢ ■ (P ∗ Q) := plainly_mono <| sep_mono plainly_and_emp_elim .rfl

theorem plainly_affinely_elim : ■ <affine> P ⊣⊢ ■ P :=
  ⟨plainly_and.mp.trans and_elim_r, (and_intro plainly_emp_intro .rfl).trans plainly_and.mpr⟩

theorem intuitionistically_plainly_elim : □ ■ P ⊢ □ P :=
  intuitionistically_affinely.mpr.trans <| intuitionistically_mono affinely_plainly_elim

theorem intuitionistically_plainly : □ ■ P ⊢ ■ □ P := by
  refine (affinely_elim.trans ?_).trans plainly_affinely_elim.mpr
  exact persistently_elim_plainly.mp.trans plainly_persistently_elim.mpr

theorem and_sep_plainly : ■ P ∧ ■ Q ⊣⊢ ■ P ∗ ■ Q :=
  ⟨plainly_and_sep_l_1, and_intro plainly_absorb (sep_symm.trans plainly_absorb)⟩

theorem plainly_sep_2 : ■ P ∗ ■ Q ⊢ ■ (P ∗ Q) :=
  and_sep_plainly.mpr.trans <| plainly_and.mpr.trans plainly_and_sep

theorem plainly_sep [BIPositive PROP] : ■ (P ∗ Q) ⊣⊢ ■ P ∗ ■ Q := by
  refine ⟨?_, plainly_sep_2⟩
  refine plainly_affinely_elim.mpr.trans ?_
  refine (plainly_mono <| affinely_sep.mp).trans ?_
  refine .trans ?_ and_sep_plainly.mp
  refine and_intro (plainly_mono ?_) (plainly_mono ?_)
  · exact ((sep_mono .rfl affinely_elim_emp).trans sep_emp.mp).trans affinely_elim
  · exact ((sep_mono affinely_elim_emp .rfl).trans emp_sep.mp).trans affinely_elim

theorem plainly_wand : ■ (P -∗ Q) ⊢ ■ P -∗ ■ Q :=
  wand_intro <| plainly_sep_2.trans (plainly_mono wand_elim_l)

theorem plainly_entails_l (H : P ⊢ ■ Q) : P ⊢ ■ Q ∗ P :=
  (and_intro H .rfl).trans plainly_and_sep_l_1

theorem plainly_entails_r (H : P ⊢ ■ Q) : P ⊢ P ∗ ■ Q :=
  (and_intro .rfl H).trans plainly_and_sep_r_1

theorem plainly_impl_wand_2 : ■ (P -∗ Q) ⊢ ■ (P → Q) := by
  refine plainly_intro' (imp_intro ?_)
  calc iprop(■ (P -∗ Q) ∧ P)
    _ ⊢ ■ (P -∗ Q) ∧ (emp ∗ P) := and_mono .rfl emp_sep.mpr
    _ ⊢ (■ (P -∗ Q) ∧ emp) ∗ P := plainly_and_sep_assoc.mp
    _ ⊢ (P -∗ Q) ∗ P := sep_mono (and_comm.mp.trans plainly_and_emp_elim) .rfl
    _ ⊢ Q := wand_elim_l

theorem impl_wand_plainly_2 : (■ P -∗ Q) ⊢ (■ P → Q) :=
  imp_intro' <| plainly_and_sep_l_1.trans wand_elim_r

theorem impl_wand_affinely_plainly : (■ P → Q) ⊣⊢ (<affine> ■ P -∗ Q) := by
  constructor
  · refine (imp_mono_l persistently_elim_plainly.mp).trans ?_
    refine intuitionistically_wand.mpr.trans ?_
    exact wand_mono_l <| affinely_mono persistently_elim_plainly.mpr
  · refine .trans ?_ (imp_mono_l persistently_elim_plainly.mpr)
    refine .trans ?_ intuitionistically_wand.mp
    exact wand_mono_l affinely_of_intuitionistically

theorem persistently_wand_affinely_plainly :
    (<affine> ■ P -∗ <pers> Q) ⊢ <pers> (<affine> ■ P -∗ Q) :=
  calc iprop(<affine> ■ P -∗ <pers> Q)
    _ ⊢ ■ P → <pers> Q := impl_wand_affinely_plainly.mpr
    _ ⊢ <pers> (■ P → Q) := persistently_impl_plainly
    _ ⊢ <pers> (<affine> ■ P -∗ Q) := persistently_mono impl_wand_affinely_plainly.mp

theorem plainly_wand_affinely_plainly : (<affine> ■ P -∗ ■ Q) ⊢ ■ (<affine> ■ P -∗ Q) :=
  calc iprop(<affine> ■ P -∗ ■ Q)
    _ ⊢ ■ P → ■ Q := impl_wand_affinely_plainly.mpr
    _ ⊢ ■ (■ P → Q) := plainly_impl_plainly
    _ ⊢ ■ (<affine> ■ P -∗ Q) := plainly_mono impl_wand_affinely_plainly.mp

section AffineBI

variable [BIAffine PROP]

theorem plainly_emp : ■ emp ⊣⊢ (emp : PROP) :=
  ⟨plainly_elim, plainly_emp_2⟩

theorem plainly_and_sep_l : ■ P ∧ Q ⊣⊢ ■ P ∗ Q :=
  ⟨plainly_and_sep_l_1, sep_and⟩

theorem plainly_and_sep_r : P ∧ ■ Q ⊣⊢ P ∗ ■ Q := by
  constructor
  · exact and_comm.mp.trans <| plainly_and_sep_l.mp.trans sep_symm
  · exact sep_symm.trans <| plainly_and_sep_l.mpr.trans and_comm.mpr

theorem plainly_impl_wand : ■ (P → Q) ⊣⊢ ■ (P -∗ Q) := by
  refine ⟨?_, plainly_impl_wand_2⟩
  refine plainly_intro' <| wand_intro' ?_
  refine plainly_and_sep_r.mpr.trans ?_
  exact (and_mono .rfl plainly_elim).trans imp_elim_r

theorem impl_wand_plainly : (■ P → Q) ⊣⊢ (■ P -∗ Q) :=
  ⟨imp_wand_1, impl_wand_plainly_2⟩

end AffineBI

instance plainly_absorbing (P : PROP) : Absorbing iprop(■ P) where
  absorbing := absorbingly_elim_plainly.1

@[rocq_alias plainly_si_pure]
theorem plainly_siPure {Pi : SiProp} :
    iprop(■ (<si_pure> Pi : PROP) ⊣⊢ <si_pure> Pi) :=
  ⟨siPure_mono siEmpValid_siPure.mp, siPure_mono siEmpValid_siPure.mpr⟩

end PlainlyLaws

end Iris.BI
