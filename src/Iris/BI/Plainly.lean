/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI.Classes
import Iris.BI.BI
import Iris.BI.DerivedLaws
import Iris.Algebra

namespace Iris
open BI

class Plainly (PROP : Type _) where
  plainly : PROP → PROP
export Plainly(plainly)

syntax "■ " term:40 : term

macro_rules
  | `(iprop(■ $P))  => ``(Plainly.plainly iprop($P))

delab_rule Plainly.plainly
  | `($_ $P) => do ``(iprop(■ $(← Iris.BI.unpackIprop P)))

def Plainly.plainlyIf [Iris.BI.BIBase PROP] [Plainly PROP] (p : Bool) (P : PROP) : PROP :=
  iprop(if p then ■ P else P)

syntax:max "■?" term:max ppHardSpace term:40 : term

macro_rules
  | `(iprop(■? $p $P))  => ``(Plainly.plainlyIf $p iprop($P))

delab_rule Plainly.plainlyIf
  | `($_ $p $P) => do ``(iprop(■? $p $(← Iris.BI.unpackIprop P)))


-- FIXME: These names are inconsistent
class BIPlainly (PROP : Type _) [Iris.BI PROP] extends Plainly PROP where
  [ne : Iris.OFE.NonExpansive (Plainly.plainly (PROP := PROP))]
  mono {P Q : PROP} : (P ⊢ Q) → ■ P ⊢ ■ Q
  elim_persistently {P : PROP} : ■ P ⊢ <pers> P
  idem {P : PROP} : ■ P ⊢ ■ ■ P
  plainly_sForall_2 {Φ : PROP → Prop} : (∀ p, ⌜Φ p⌝ → ■ p) ⊢ ■ sForall Φ
  plainly_impl_plainly {P Q : PROP} : (■ P → ■ Q) ⊢ ■ (■ P → Q)
  emp_intro {P : PROP} : P ⊢ ■ emp
  plainly_absorb {P Q : PROP} : ■ P ∗ Q ⊢ ■ P
  later_plainly {P : PROP} : ▷ ■ P ⊣⊢ ■ ▷ P

class BIPersistentlyImplPlainly (PROP : Type _) [Iris.BI PROP] [BIPlainly PROP] where
  pers_impl_plainly (P Q : PROP) : (■ P → <pers> Q) ⊢ <pers> (■ P → Q)

class BIPlainlyExists (PROP : Type _) [Iris.BI PROP] [BIPlainly PROP] where
  plainly_sExists_1 {Φ : PROP → Prop} : ■ sExists Φ ⊢ ∃ p, ⌜Φ p⌝ ∧ ■ p

namespace BI
open Iris.Std

export BIPlainly (plainly_sForall_2 plainly_impl_plainly plainly_absorb later_plainly)
export BIPersistentlyImplPlainly (pers_impl_plainly)
export BIPlainlyExists (plainly_sExists_1)

class Plain [BI PROP] [Plainly PROP] [BIPlainly PROP] (P : PROP) where
  plain : P ⊢ ■ P

instance [BI PROP] [BIPlainly PROP] (P : PROP) : Plain iprop(■ P) :=
  ⟨BIPlainly.idem⟩

section PlainlyLaws
open BIPlainly

variable [BI PROP] [BIPlainly PROP]
variable {P Q R : PROP}

theorem affinely_plainly_elim : <affine> ■ P ⊢ P :=
  (affinely_mono elim_persistently).trans persistently_and_emp_elim

theorem persistently_elim_plainly : <pers> ■ P ⊣⊢ ■ P :=
  ⟨absorbingly_of_persistently.trans <| sep_symm.trans plainly_absorb,
   idem.trans elim_persistently⟩

theorem plainly_forall_2 {Ψ : α → PROP} : (∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a) := by
  refine (forall_intro ?_).trans plainly_sForall_2
  intro P
  refine imp_intro' ?_
  refine and_comm.mp.trans <| imp_elim' <| pure_elim _ .rfl ?_
  rintro ⟨_, Ha⟩
  rewrite [← Ha]
  exact imp_intro' <| and_elim_l.trans <| forall_elim _

theorem plainly_persistently_elim : ■ <pers> P ⊣⊢ ■ P := by
  constructor
  · refine (true_and.2.trans <| and_mono emp_intro .rfl).trans ?_
    refine .trans ?_ (mono <| and_forall_bool.2.trans persistently_and_emp_elim)
    refine and_forall_bool.1.trans ?_
    refine .trans ?_ plainly_forall_2
    refine forall_mono ?_
    exact (·.casesOn .rfl .rfl)
  · exact idem.trans <| mono elim_persistently

theorem absorbingly_elim_plainly : <absorb> ■ P ⊣⊢ ■ P := by
  constructor
  · refine (absorbingly_mono <| persistently_elim_plainly.2).trans ?_
    refine .trans ?_ persistently_elim_plainly.1
    exact absorbingly_persistently.1.trans .rfl
  · refine .trans ?_ (absorbingly_mono persistently_elim_plainly.1)
    refine persistently_elim_plainly.2.trans ?_
    exact .trans .rfl absorbingly_persistently.2

theorem plainly_and_sep_elim : ■ P ∧ Q ⊢ (emp ∧ P) ∗ Q :=
  (and_mono elim_persistently .rfl).trans persistently_and_sep_elim_emp

theorem plainly_and_sep_assoc : ■ P ∧ (Q ∗ R) ⊣⊢ (■ P ∧ Q) ∗ R := by
  constructor
  · refine (and_mono persistently_elim_plainly.2 BIBase.Entails.rfl).trans ?_
    refine .trans ?_ (sep_mono (and_mono persistently_elim_plainly.1 .rfl) .rfl)
    exact persistently_and_sep_assoc.1
  · refine .trans ?_ (and_mono persistently_elim_plainly.1 .rfl)
    refine (sep_mono (and_mono persistently_elim_plainly.2 .rfl) .rfl).trans ?_
    exact persistently_and_sep_assoc.2

theorem plainly_and_emp_elim : emp ∧ ■ P ⊢ P :=
  (and_mono .rfl elim_persistently).trans persistently_and_emp_elim

theorem plainly_into_absorbingly : ■ P ⊢ <absorb> P :=
  elim_persistently.trans absorbingly_of_persistently

theorem plainly_elim [Absorbing P] : ■ P ⊢ P :=
  elim_persistently.trans persistently_elim

theorem plainly_idemp : ■ ■ P ⊣⊢ ■ P :=
  ⟨plainly_into_absorbingly.trans absorbingly_elim_plainly.1, idem⟩

theorem plainly_intro' (H : ■ P ⊢ Q) : ■ P ⊢ ■ Q :=
  plainly_idemp.2.trans <| mono <| H

theorem plainly_pure {φ} : ■ ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  refine ⟨elim_persistently.trans persistently_elim, ?_⟩
  refine pure_elim' fun φ => ?_
  apply Entails.trans (Q := «forall» (fun x : Empty => iprop(■ True)))
  · exact forall_intro Empty.rec
  · exact plainly_forall_2.trans (mono <| pure_intro φ)

theorem plainly_forall {Ψ : α → PROP} : ■ (∀ a, Ψ a) ⊣⊢ ∀ a, ■ (Ψ a) :=
  ⟨forall_intro (mono <| forall_elim ·), plainly_forall_2⟩

theorem plainly_exists_2 {α : Sort _} {Ψ : α → PROP} : (∃ a, ■ (Ψ a)) ⊢ ■ (∃ a, Ψ a) :=
  exists_elim (mono <| exists_intro ·)

theorem plainly_exists_1 [BIPlainlyExists PROP] {Ψ : α → PROP} :
    ■ (∃ a, Ψ a) ⊢ ∃ a, ■ (Ψ a) := by
  refine plainly_sExists_1.trans ?_
  refine exists_elim fun p => imp_elim <| pure_elim' ?_
  rintro ⟨a, rfl⟩
  exact imp_intro' <| exists_intro' a and_elim_l

theorem plainly_exists [BIPlainlyExists PROP] {Ψ : α → PROP} : ■ (∃ a, Ψ a) ⊣⊢ ∃ a, ■ (Ψ a) :=
  ⟨plainly_exists_1, plainly_exists_2⟩

theorem plainly_and : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q := by
  constructor
  · refine (mono and_forall_bool.mp).trans (.trans ?_ and_forall_bool.mpr)
    exact plainly_forall.mp.trans (forall_mono (·.casesOn .rfl .rfl))
  · refine (and_forall_bool.mp).trans (.trans ?_ (mono <| and_forall_bool.mpr))
    refine .trans (forall_mono ?_) plainly_forall.mpr
    exact (·.casesOn .rfl .rfl)

theorem plainly_or_2 : ■ P ∨ ■ Q ⊢ ■ (P ∨ Q) := by
  refine or_exists_bool.mp.trans (.trans ?_ (mono <| or_exists_bool.mpr))
  refine .trans (exists_mono ?_) plainly_exists_2
  exact (·.casesOn .rfl .rfl)

theorem plainly_or [BIPlainlyExists PROP] : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q := by
  refine ⟨?_, plainly_or_2⟩
  refine (mono or_exists_bool.mp).trans (.trans ?_ or_exists_bool.mpr)
  exact plainly_exists_1.trans <| exists_mono (·.casesOn .rfl .rfl)

theorem plainly_impl : ■ (P → Q) ⊢ ■ P → ■ Q := by
  refine imp_intro' <| plainly_and.mpr.trans ?_
  exact mono imp_elim_r

theorem plainly_emp_2 : (emp : PROP) ⊢ ■ emp := emp_intro

theorem plainly_sep_dup : ■ P ⊣⊢ ■ P ∗ ■ P := by
  refine ⟨?_, plainly_absorb⟩
  refine and_self.2.trans ?_
  refine ((and_mono .rfl emp_sep.2).trans plainly_and_sep_assoc.1).trans ?_
  exact (sep_mono and_elim_l .rfl).trans .rfl

theorem plainly_and_sep_l_1 : ■ P ∧ Q ⊢ ■ P ∗ Q := by
  refine ((and_mono BIBase.Entails.rfl emp_sep.2).trans plainly_and_sep_assoc.1).trans ?_
  exact (sep_mono and_elim_l .rfl).trans .rfl

theorem plainly_and_sep_r_1 : P ∧ ■ Q ⊢ P ∗ ■ Q :=
  and_comm.1.trans <| plainly_and_sep_l_1.trans sep_symm

theorem plainly_true_emp : ■ True ⊣⊢ ■ (emp : PROP) :=
  ⟨emp_intro, mono true_intro⟩

theorem plainly_and_sep : ■ (P ∧ Q) ⊢ ■ (P ∗ Q) := by
  refine (plainly_and.mp.trans <| (and_mono idem .rfl).trans plainly_and.mpr).trans ?_
  refine (mono <| and_mono .rfl emp_sep.mpr).trans ?_
  refine (mono <| plainly_and_sep_assoc.1).trans ?_
  refine (mono <| sep_mono and_comm.mp .rfl).trans ?_
  exact (mono <| sep_mono plainly_and_emp_elim .rfl).trans .rfl

theorem plainly_affinely_elim : ■ <affine> P ⊣⊢ ■ P := by
  constructor
  · refine plainly_and.mp.trans ?_
    refine (and_mono plainly_true_emp.mpr .rfl).trans ?_
    exact (and_mono plainly_pure.mp .rfl).trans and_elim_r
  · refine .trans ?_ plainly_and.mpr
    refine .trans ?_ (and_mono plainly_true_emp.mp .rfl)
    refine .trans ?_ (and_mono plainly_pure.mpr .rfl)
    exact and_intro true_intro .rfl

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
  refine (mono <| affinely_sep.mp).trans ?_
  refine .trans ?_ and_sep_plainly.mp
  refine and_intro (mono ?_) (mono ?_)
  · exact ((sep_mono .rfl affinely_elim_emp).trans sep_emp.mp).trans affinely_elim
  · exact ((sep_mono affinely_elim_emp .rfl).trans emp_sep.mp).trans affinely_elim

theorem plainly_wand : ■ (P -∗ Q) ⊢ ■ P -∗ ■ Q :=
  wand_intro <| plainly_sep_2.trans (mono wand_elim_l)

theorem plainly_entails_l (H : P ⊢ ■ Q) : P ⊢ ■ Q ∗ P :=
  (and_intro H .rfl).trans plainly_and_sep_l_1

theorem plainly_entails_r (H : P ⊢ ■ Q) : P ⊢ P ∗ ■ Q :=
  (and_intro .rfl H).trans plainly_and_sep_r_1

theorem plainly_impl_wand_2 : ■ (P -∗ Q) ⊢ ■ (P → Q) := by
  refine plainly_intro' (imp_intro ?_)
  refine (and_mono .rfl emp_sep.mpr).trans ?_
  refine plainly_and_sep_assoc.mp.trans ?_
  refine (sep_mono (and_comm.mp.trans plainly_and_emp_elim) .rfl).trans ?_
  exact wand_elim_l

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

theorem persistently_wand_affinely_plainly [BIPersistentlyImplPlainly PROP] :
    (<affine> ■ P -∗ <pers> Q) ⊢ <pers> (<affine> ■ P -∗ Q) := by
  refine impl_wand_affinely_plainly.mpr.trans  ?_
  refine .trans ?_ (persistently_mono impl_wand_affinely_plainly.mp)
  exact pers_impl_plainly _ _

theorem plainly_wand_affinely_plainly : (<affine> ■ P -∗ ■ Q) ⊢ ■ (<affine> ■ P -∗ Q) := by
  refine impl_wand_affinely_plainly.mpr.trans ?_
  refine .trans ?_ (mono impl_wand_affinely_plainly.mp)
  exact plainly_impl_plainly

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

end PlainlyLaws

end Iris.BI
