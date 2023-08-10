/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI.BIBase

namespace Iris
open Iris.Std
open Lean

/-- Require that a separation logic with carrier type `PROP` fulfills all necessary axioms. -/
class BI (PROP : Type) extends BI.BIBase PROP where
  entails_preorder : Preorder Entails

  pure_intro {φ : Prop} {P : PROP} : φ → P ⊢ ⌜φ⌝
  pure_elim' {φ : Prop} {P : PROP} : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P

  and_elim_l {P Q : PROP} : P ∧ Q ⊢ P
  and_elim_r {P Q : PROP} : P ∧ Q ⊢ Q
  and_intro {P Q R : PROP} : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R

  or_intro_l {P Q : PROP} : P ⊢ P ∨ Q
  or_intro_r {P Q : PROP} : Q ⊢ P ∨ Q
  or_elim {P Q R : PROP} : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R

  imp_intro {P Q R : PROP} : (P ∧ Q ⊢ R) → P ⊢ Q → R
  imp_elim {P Q R : PROP} : (P ⊢ Q → R) → P ∧ Q ⊢ R

  forall_intro {P : PROP} {Ψ : α → PROP} : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a
  forall_elim {Ψ : α → PROP} (a : α) : (∀ a, Ψ a) ⊢ Ψ a

  exists_intro {Ψ : α → PROP} (a : α) : Ψ a ⊢ ∃ a, Ψ a
  exists_elim {Φ : α → PROP} {Q : PROP} : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q

  sep_mono {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'
  emp_sep_1 {P : PROP} : emp ∗ P ⊢ P
  emp_sep_2 {P : PROP} : P ⊢ emp ∗ P
  sep_symm {P Q : PROP} : P ∗ Q ⊢ Q ∗ P
  sep_assoc_l {P Q R : PROP} : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)

  wand_intro {P Q R : PROP} : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R
  wand_elim {P Q R : PROP} : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R

  persistently_mono {P Q : PROP} : (P ⊢ Q) → <pers> P ⊢ <pers> Q
  persistently_idem_2 {P : PROP} : <pers> P ⊢ <pers> <pers> P
  persistently_emp_2 : (emp : PROP) ⊢ <pers> emp
  persistently_and_2 {P Q : PROP} : (<pers> P) ∧ (<pers> Q) ⊢ <pers> (P ∧ Q)
  persistently_exists_1 {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a)
  persistently_absorb_l {P Q : PROP} : <pers> P ∗ Q ⊢ <pers> P
  persistently_and_l {P Q : PROP} : <pers> P ∧ Q ⊢ P ∗ Q

namespace BI

attribute [instance] BI.entails_preorder

theorem BIBase.Entails.trans [BI PROP] {P Q R : PROP} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  Transitive.trans h1 h2

@[simp] theorem BIBase.Entails.rfl [BI PROP] {P : PROP} : P ⊢ P := refl

theorem BIBase.Entails.of_eq [BI PROP] {P Q : PROP} (h : P = Q) : P ⊢ Q := h ▸ .rfl

@[simp] theorem BIBase.BiEntails.rfl [BI PROP] {P : PROP} : P ⊣⊢ P := ⟨.rfl, .rfl⟩

theorem BIBase.BiEntails.of_eq [BI PROP] {P Q : PROP} (h : P = Q) : P ⊣⊢ Q := h ▸ .rfl

theorem BIBase.BiEntails.symm [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : Q ⊣⊢ P := ⟨h.2, h.1⟩

theorem BIBase.BiEntails.trans [BI PROP] {P Q R : PROP} (h1 : P ⊣⊢ Q) (h2 : Q ⊣⊢ R) : P ⊣⊢ R :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

export BIBase (
  Entails emp pure and or imp «forall» «exists» sep wand persistently
  BiEntails iff wandIff affinely absorbingly intuitionistically
  persistentlyIf affinelyIf absorbinglyIf intuitionisticallyIf
  bigAnd bigOr bigSep Entails.trans BiEntails.trans)

attribute [rw_mono_rule] BI.sep_mono
attribute [rw_mono_rule] BI.persistently_mono
