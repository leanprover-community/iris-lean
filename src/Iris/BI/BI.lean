/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.BIBase

namespace Iris
open Iris.Std
open Lean

/-- Require that a separation logic with carrier type `PROP` fulfills all necessary axioms. -/
class BI (PROP : Type) extends BI.BIBase PROP where
  entailsPreOrder : PreOrder entails

  equiv_entails {P Q : PROP} : (P = Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P)

  pure_intro {φ : Prop} {P : PROP} : φ → P ⊢ ⌜φ⌝
  pure_elim' {φ : Prop} {P : PROP} : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P

  and_elim_l {P Q : PROP} : P ∧ Q ⊢ P
  and_elim_r {P Q : PROP} : P ∧ Q ⊢ Q
  and_intro {P Q R : PROP} : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R

  or_intro_l {P Q : PROP} : P ⊢ P ∨ Q
  or_intro_r {P Q : PROP} : Q ⊢ P ∨ Q
  or_elim {P Q R : PROP} : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R

  impl_intro_r {P Q R : PROP} : (P ∧ Q ⊢ R) → P ⊢ Q → R
  impl_elim_l' {P Q R : PROP} : (P ⊢ Q → R) → P ∧ Q ⊢ R

  forall_intro {P : PROP} {Ψ : α → PROP} : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a
  forall_elim {Ψ : α → PROP} (a : α) : (∀ a, Ψ a) ⊢ Ψ a

  exist_intro {Ψ : α → PROP} (a : α) : Ψ a ⊢ ∃ a, Ψ a
  exist_elim {Φ : α → PROP} {Q : PROP} : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q

  sep_mono {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'
  emp_sep_1 {P : PROP} : P ⊢ emp ∗ P
  emp_sep_2 {P : PROP} : emp ∗ P ⊢ P
  sep_comm' {P Q : PROP} : P ∗ Q ⊢ Q ∗ P
  sep_assoc' {P Q R : PROP} : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)

  wand_intro_r {P Q R : PROP} : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R
  wand_elim_l' {P Q R : PROP} : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R

  persistently_mono {P Q : PROP} : (P ⊢ Q) → <pers> P ⊢ <pers> Q
  persistently_idemp_2 {P : PROP} : <pers> P ⊢ <pers> <pers> P
  persistently_emp_2 : (emp : PROP) ⊢ <pers> emp
  persistently_and_2 {P Q : PROP} : (<pers> P) ∧ (<pers> Q) ⊢ <pers> (P ∧ Q)
  persistently_exist_1 {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a)
  persistently_absorbing {P Q : PROP} : <pers> P ∗ Q ⊢ <pers> P
  persistently_and_sep_elim {P Q : PROP} : <pers> P ∧ Q ⊢ P ∗ Q

namespace BI

attribute [instance] BI.entailsPreOrder

export BIBase (
  entails emp pure and or impl «forall» exist sep wand persistently
  bi_iff bi_wand_iff bi_affinely bi_absorbingly bi_intuitionistically
  bi_persistently_if bi_affinely_if bi_absorbingly_if bi_intuitionistically_if)

attribute [rw_mono_rule] BI.sep_mono
attribute [rw_mono_rule] BI.persistently_mono
