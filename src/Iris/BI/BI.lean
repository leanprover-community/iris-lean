/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.BIBase

namespace Iris.BI
open Iris.Std
open Lean

/-- Require that a separation logic with carrier type `car` fulfills all necessary axioms. -/
class BI (car : Type) extends BIBase car where
  entailsPreOrder : PreOrder entails

  equiv_entails {P Q : car} : (P = Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P)

  pure_intro {φ : Prop} {P : car} : φ → P ⊢ ⌜φ⌝
  pure_elim' {φ : Prop} {P : car} : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P

  and_elim_l {P Q : car} : P ∧ Q ⊢ P
  and_elim_r {P Q : car} : P ∧ Q ⊢ Q
  and_intro {P Q R : car} : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R

  or_intro_l {P Q : car} : P ⊢ P ∨ Q
  or_intro_r {P Q : car} : Q ⊢ P ∨ Q
  or_elim {P Q R : car} : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R

  impl_intro_r {P Q R : car} : (P ∧ Q ⊢ R) → P ⊢ Q → R
  impl_elim_l' {P Q R : car} : (P ⊢ Q → R) → P ∧ Q ⊢ R

  forall_intro {P : car} {Ψ : α → car} : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a
  forall_elim {Ψ : α → car} (a : α) : (∀ a, Ψ a) ⊢ Ψ a

  exist_intro {Ψ : α → car} (a : α) : Ψ a ⊢ ∃ a, Ψ a
  exist_elim {Φ : α → car} {Q : car} : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q

  sep_mono {P P' Q Q' : car} : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'
  emp_sep_1 {P : car} : P ⊢ emp ∗ P
  emp_sep_2 {P : car} : emp ∗ P ⊢ P
  sep_comm' {P Q : car} : P ∗ Q ⊢ Q ∗ P
  sep_assoc' {P Q R : car} : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)

  wand_intro_r {P Q R : car} : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R
  wand_elim_l' {P Q R : car} : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R

  persistently_mono {P Q : car} : (P ⊢ Q) → <pers> P ⊢ <pers> Q
  persistently_idemp_2 {P : car} : <pers> P ⊢ <pers> <pers> P
  persistently_emp_2 : (emp : car) ⊢ <pers> emp
  persistently_and_2 {P Q : car} : (<pers> P) ∧ (<pers> Q) ⊢ <pers> (P ∧ Q)
  persistently_exist_1 {Ψ : α → car} : <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a)
  persistently_absorbing {P Q : car} : <pers> P ∗ Q ⊢ <pers> P
  persistently_and_sep_elim {P Q : car} : <pers> P ∧ Q ⊢ P ∗ Q

attribute [instance] BI.entailsPreOrder

attribute [rwMonoRule] BI.sep_mono
attribute [rwMonoRule] BI.persistently_mono

end Iris.BI
