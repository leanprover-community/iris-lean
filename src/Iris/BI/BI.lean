/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
module

public import Iris.Algebra.OFE
public import Iris.BI.BIBase

@[expose] public section

namespace Iris
open Iris.Std OFE
open Lean

def liftRel (R : α → β → Prop) (A : α → Prop) (B : β → Prop) : Prop :=
  (∀ a, A a → ∃ b, B b ∧ R a b) ∧ (∀ b, B b → ∃ a, A a ∧ R a b)

theorem liftRel_eq : liftRel (@Eq α) A B ↔ A = B := by
  simp [liftRel, forall_and, iff_def, funext_iff]

/-- Require that a separation logic with carrier type `PROP` fulfills all necessary axioms. -/
class BI (PROP : Type _) extends COFE PROP, BI.BIBase PROP where
  Equiv P Q := P ⊣⊢ Q

  entails_preorder : Preorder Entails
  equiv_iff {P Q : PROP} : (P ≡ Q) ↔ P ⊣⊢ Q := by simp

  and_ne : OFE.NonExpansive₂ and
  or_ne : OFE.NonExpansive₂ or
  imp_ne : OFE.NonExpansive₂ imp
  sForall_ne {P₁ P₂} : liftRel (· ≡{n}≡ ·) P₁ P₂ → sForall P₁ ≡{n}≡ sForall P₂
  sExists_ne {P₁ P₂} : liftRel (· ≡{n}≡ ·) P₁ P₂ → sExists P₁ ≡{n}≡ sExists P₂
  sep_ne : OFE.NonExpansive₂ sep
  wand_ne : OFE.NonExpansive₂ wand
  persistently_ne : OFE.NonExpansive persistently
  later_ne : OFE.NonExpansive later

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

  sForall_intro {P : PROP} {Ψ : PROP → Prop} : (∀ p, Ψ p → P ⊢ p) → P ⊢ sForall Ψ
  sForall_elim {Ψ : PROP → Prop} {p : PROP} : Ψ p → sForall Ψ ⊢ p

  sExists_intro {Ψ : PROP → Prop} {p : PROP} : Ψ p → p ⊢ sExists Ψ
  sExists_elim {Φ : PROP → Prop} {Q : PROP} : (∀ p, Φ p → p ⊢ Q) → sExists Φ ⊢ Q

  sep_mono {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'
  emp_sep {P : PROP} : emp ∗ P ⊣⊢ P
  sep_symm {P Q : PROP} : P ∗ Q ⊢ Q ∗ P
  sep_assoc_l {P Q R : PROP} : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)

  wand_intro {P Q R : PROP} : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R
  wand_elim {P Q R : PROP} : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R

  persistently_mono {P Q : PROP} : (P ⊢ Q) → <pers> P ⊢ <pers> Q
  persistently_idem_2 {P : PROP} : <pers> P ⊢ <pers> <pers> P
  persistently_emp_2 : (emp : PROP) ⊢ <pers> emp
  persistently_and_2 {P Q : PROP} : (<pers> P) ∧ (<pers> Q) ⊢ <pers> (P ∧ Q)
  persistently_sExists_1 {Ψ : PROP → Prop} : <pers> (sExists Ψ) ⊢ ∃ p, ⌜Ψ p⌝ ∧ <pers> p
  persistently_absorb_l {P Q : PROP} : <pers> P ∗ Q ⊢ <pers> P
  persistently_and_l {P Q : PROP} : <pers> P ∧ Q ⊢ P ∗ Q

  later_mono {P Q : PROP} : (P ⊢ Q) → ▷ P ⊢ ▷ Q
  later_intro {P : PROP} : P ⊢ ▷ P

  later_sForall_2 {Φ : PROP → Prop} : (∀ p, ⌜Φ p⌝ → ▷ p) ⊢ ▷ sForall Φ
  later_sExists_false {Φ : PROP → Prop} : (▷ sExists Φ) ⊢ ▷ False ∨ ∃ p, ⌜Φ p⌝ ∧ ▷ p
  later_sep {P Q : PROP} : ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q
  later_persistently {P : PROP} : ▷ <pers> P ⊣⊢ <pers> ▷ P
  later_false_em {P : PROP} : ▷ P ⊢ ▷ False ∨ (▷ False → P)

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

theorem BIBase.BiEntails.ofMono [BI PROP1] [BI PROP2] {mod : PROP1 → PROP2}
    (mono : ∀{P Q}, iprop(P ⊢ Q) → iprop(mod P ⊢ mod Q)) :
    ∀ {P Q : PROP1}, P ⊣⊢ Q → mod P ⊣⊢ mod Q :=
  fun h => ⟨mono h.1, mono h.2⟩

export BIBase (
  Entails emp pure and or imp sForall sExists «forall» «exists» sep wand
  persistently BiEntails iff wandIff affinely absorbingly
  intuitionistically later persistentlyIf affinelyIf absorbinglyIf
  intuitionisticallyIf bigAnd bigOr bigSep Entails.trans BiEntails.trans)

attribute [rw_mono_rule] BI.sep_mono
attribute [rw_mono_rule] BI.persistently_mono
