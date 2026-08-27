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
@[rocq_alias bi, rocq_alias BiMixin,
  rocq_alias BiPersistentlyMixin, rocq_alias BiLaterMixin]
class BI (PROP : Type _) extends COFE PROP, BI.BIBase PROP where
  entails_refl {P : PROP} : P ⊢ P
  entails_trans {P Q R : PROP} : (P ⊢ Q) → (Q ⊢ R) → P ⊢ R
  equiv_iff {P Q : PROP} : (P = Q) ↔ P ⊣⊢ Q := by rw [OFE.eq_dist]; simp
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

instance [BIBase PROP] : LE PROP where
  le := BIBase.Entails

@[rocq_alias bi.entails_po]
instance entails_preorder [BI PROP] : Std.IsPreorder PROP where
  le_refl _ := BI.entails_refl
  le_trans _ _ _ := BI.entails_trans

instance [BI PROP] : Std.Refl <| BIBase.Entails (PROP := PROP) where
  refl _ := BI.entails_refl

theorem BIBase.Entails.trans [BI PROP] {P Q R : PROP} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  BI.entails_trans h1 h2

@[simp,refl] theorem BIBase.Entails.rfl [BI PROP] {P : PROP} : P ⊢ P := BI.entails_refl
@[simp,refl] theorem BIBase.Entails.refl [BI PROP] (P : PROP) : P ⊢ P := BI.entails_refl

theorem BIBase.Entails.of_eq [BI PROP] {P Q : PROP} (h : P = Q) : P ⊢ Q := h ▸ .rfl

@[simp] theorem BIBase.BiEntails.rfl [BI PROP] {P : PROP} : P ⊣⊢ P := ⟨.rfl, .rfl⟩
@[simp] theorem BIBase.BiEntails.refl [BI PROP] (P : PROP) : P ⊣⊢ P := ⟨.rfl, .rfl⟩

theorem BIBase.BiEntails.of_eq [BI PROP] {P Q : PROP} (h : P = Q) : P ⊣⊢ Q := h ▸ .rfl
theorem _root_.Eq.to_bi [BI PROP] {P Q : PROP} (h : P = Q) : P ⊣⊢ Q := h ▸ .rfl

theorem BIBase.BiEntails.to_eq [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : P = Q := equiv_iff.mpr h

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
  intuitionisticallyIf bigAnd bigOr bigSep Entails.trans BiEntails.trans BiEntails.of_eq BiEntails.to_eq)

attribute [rocq_alias bi.equiv_entails] BI.equiv_iff
attribute [rocq_alias bi.and_ne] BI.and_ne
attribute [rocq_alias bi.or_ne] BI.or_ne
attribute [rocq_alias bi.impl_ne] BI.imp_ne
attribute [rocq_alias bi.sep_ne] BI.sep_ne
attribute [rocq_alias bi.wand_ne] BI.wand_ne
attribute [rocq_alias bi.persistently_ne] BI.persistently_ne
attribute [rocq_alias bi.later_ne] BI.later_ne

attribute [rocq_alias bi.pure_intro] BI.pure_intro
attribute [rocq_alias bi.pure_elim'] BI.pure_elim'

attribute [rocq_alias bi.and_elim_l] BI.and_elim_l
attribute [rocq_alias bi.and_elim_r] BI.and_elim_r
attribute [rocq_alias bi.and_intro] BI.and_intro

attribute [rocq_alias bi.or_intro_l] BI.or_intro_l
attribute [rocq_alias bi.or_intro_r] BI.or_intro_r
attribute [rocq_alias bi.or_elim] BI.or_elim

attribute [rocq_alias bi.impl_intro_r] BI.imp_intro
attribute [rocq_alias bi.impl_elim_l'] BI.imp_elim

attribute [rw_mono_rule, rocq_alias bi.sep_mono] BI.sep_mono
attribute [rocq_alias bi.emp_sep_1, rocq_alias bi.emp_sep_2] BI.emp_sep
attribute [rocq_alias bi.sep_comm'] BI.sep_symm
attribute [rocq_alias bi.sep_assoc'] BI.sep_assoc_l

attribute [rocq_alias bi.wand_intro_r] BI.wand_intro
attribute [rocq_alias bi.wand_elim_l'] BI.wand_elim

attribute [rw_mono_rule, rocq_alias bi.persistently_mono] BI.persistently_mono
attribute [rocq_alias bi.persistently_idemp_2] BI.persistently_idem_2
attribute [rocq_alias bi.persistently_and_2] BI.persistently_and_2
attribute [rocq_alias bi.persistently_emp_2] BI.persistently_emp_2
attribute [rocq_alias bi.persistently_exist_1] BI.persistently_sExists_1
attribute [rocq_alias interface.bi.persistently_absorbing] BI.persistently_absorb_l
attribute [rocq_alias bi.persistently_and_sep_elim] BI.persistently_and_l

attribute [rocq_alias bi.later_mono] BI.later_mono
attribute [rocq_alias bi.later_intro] BI.later_intro

attribute [rocq_alias bi.later_sep_1, rocq_alias bi.later_sep_2] BI.later_sep
attribute [rocq_alias bi.later_persistently_1,
           rocq_alias bi.later_persistently_2] BI.later_persistently
attribute [rocq_alias bi.later_false_em] BI.later_false_em

attribute [rocq_alias bi_cofe] BI.toCOFE

#rocq_ignore bi_ofeO "No coercion required in Lean, use BI.toCOFE.toOFE instead"
#rocq_ignore bi.pure_ne "No Proper type class in Lean"
#rocq_ignore bi_rewrite_relation "Rocq-specific setoid-rewriting infrastructure"
#rocq_ignore bi_later_mixin_id "BiLaterMixin with trivial later has trivial proofs regarding later"

section PersistentlyDiscrete

variable {PROP : Type _} [BIBase PROP] [COFE PROP]
  (entails_refl : ∀ {P : PROP}, P ⊢ P)
  (entails_trans : ∀ {P Q R : PROP}, (P ⊢ Q) → (Q ⊢ R) → P ⊢ R)
  (equiv_iff : ∀ {P Q : PROP}, (P = Q) ↔ P ⊣⊢ Q)
  (pure_intro : ∀ {φ : Prop} {P : PROP}, φ → P ⊢ ⌜φ⌝)
  (pure_elim' : ∀ {φ : Prop} {P : PROP}, (φ → True ⊢ P) → ⌜φ⌝ ⊢ P)
  (and_elim_l : ∀ {P Q : PROP}, P ∧ Q ⊢ P)
  (and_elim_r : ∀ {P Q : PROP}, P ∧ Q ⊢ Q)
  (and_intro : ∀ {P Q R : PROP}, (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R)
  (or_intro_l : ∀ {P Q : PROP}, P ⊢ P ∨ Q)
  (or_intro_r : ∀ {P Q : PROP}, Q ⊢ P ∨ Q)
  (or_elim : ∀ {P Q R : PROP}, (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R)
  (imp_intro : ∀ {P Q R : PROP}, (P ∧ Q ⊢ R) → P ⊢ Q → R)
  (imp_elim : ∀ {P Q R : PROP}, (P ⊢ Q → R) → P ∧ Q ⊢ R)
  (sForall_intro : ∀ {P : PROP} {Ψ : PROP → Prop}, (∀ p, Ψ p → P ⊢ p) → P ⊢ sForall Ψ)
  (sForall_elim : ∀ {Ψ : PROP → Prop} {p : PROP}, Ψ p → sForall Ψ ⊢ p)
  (sExists_intro : ∀ {Ψ : PROP → Prop} {p : PROP}, Ψ p → p ⊢ sExists Ψ)
  (sExists_elim : ∀ {Φ : PROP → Prop} {Q : PROP}, (∀ p, Φ p → p ⊢ Q) → sExists Φ ⊢ Q)
  (sep_mono : ∀ {P P' Q Q' : PROP}, (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q')
  (emp_sep : ∀ {P : PROP}, emp ∗ P ⊣⊢ P)
  (sep_symm : ∀ {P Q : PROP}, P ∗ Q ⊢ Q ∗ P)
  (sep_assoc_l : ∀ {P Q R : PROP}, (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R))
  (wand_intro : ∀ {P Q R : PROP}, (P ∗ Q ⊢ R) → P ⊢ Q -∗ R)
  (wand_elim : ∀ {P Q R : PROP}, (P ⊢ Q -∗ R) → P ∗ Q ⊢ R)
  (later_mono : ∀ {P Q : PROP}, (P ⊢ Q) → ▷ P ⊢ ▷ Q)
  (later_intro : ∀ {P : PROP}, P ⊢ ▷ P)
  (later_sForall_2 : ∀ {Φ : PROP → Prop}, (∀ p, ⌜Φ p⌝ → ▷ p) ⊢ ▷ sForall Φ)
  (later_sExists_false : ∀ {Φ : PROP → Prop},
    (▷ sExists Φ) ⊢ ▷ False ∨ ∃ p, ⌜Φ p⌝ ∧ ▷ p)
  (later_sep : ∀ {P Q : PROP}, ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q)
  (later_persistently : ∀ {P : PROP}, ▷ <pers> P ⊣⊢ <pers> ▷ P)
  (later_false_em : ∀ {P : PROP}, ▷ P ⊢ ▷ False ∨ (▷ False → P))
  (discrete : ∀ {n} {P Q : PROP}, P ≡{n}≡ Q → P = Q)
  (existential : ∀ {Ψ : PROP → Prop}, (emp ⊢ sExists Ψ) → ∃ p, Ψ p ∧ (emp ⊢ p))
  (persistently_eq : ∀ P : PROP, iprop(<pers> P) = iprop(⌜emp ⊢ P⌝))

@[reducible, rocq_alias bi_persistently_mixin_discrete]
def ofPersistentlyDiscrete : BI PROP where
  entails_refl := entails_refl
  entails_trans := entails_trans
  equiv_iff := equiv_iff
  and_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [discrete h₁, discrete h₂])⟩
  or_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [discrete h₁, discrete h₂])⟩
  imp_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [discrete h₁, discrete h₂])⟩
  sForall_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, discrete hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, discrete ha.2⟩⟩
  sExists_ne h := .of_eq <| congrArg _ <| liftRel_eq.mp
    ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, discrete hb.2⟩,
     fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, discrete ha.2⟩⟩
  sep_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [discrete h₁, discrete h₂])⟩
  wand_ne := ⟨fun {_ _ _} h₁ {_ _} h₂ => .of_eq (by rw [discrete h₁, discrete h₂])⟩
  later_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (discrete h))⟩
  pure_intro := pure_intro
  pure_elim' := pure_elim'
  and_elim_l := and_elim_l
  and_elim_r := and_elim_r
  and_intro := and_intro
  or_intro_l := or_intro_l
  or_intro_r := or_intro_r
  or_elim := or_elim
  imp_intro := imp_intro
  imp_elim := imp_elim
  sForall_intro := sForall_intro
  sForall_elim := sForall_elim
  sExists_intro := sExists_intro
  sExists_elim := sExists_elim
  sep_mono := sep_mono
  emp_sep := emp_sep
  sep_symm := sep_symm
  sep_assoc_l := sep_assoc_l
  wand_intro := wand_intro
  wand_elim := wand_elim
  later_mono := later_mono
  later_intro := later_intro
  later_sForall_2 := later_sForall_2
  later_sExists_false := later_sExists_false
  later_sep := later_sep
  later_persistently := later_persistently
  later_false_em := later_false_em
  persistently_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (discrete h))⟩
  persistently_mono h := by
    rw [persistently_eq, persistently_eq]
    exact pure_elim' fun hp => pure_intro (entails_trans hp h)
  persistently_idem_2 := by
    intro P
    rw [persistently_eq, persistently_eq]
    exact pure_elim' fun hp => pure_intro (pure_intro hp)
  persistently_emp_2 := by
    rw [persistently_eq]
    exact pure_intro entails_refl
  persistently_and_2 := by
    intro P Q
    rw [persistently_eq, persistently_eq, persistently_eq]
    refine imp_elim (pure_elim' fun hp => imp_intro ?_)
    exact entails_trans and_elim_r (pure_elim' fun hq => pure_intro (and_intro hp hq))
  persistently_sExists_1 := by
    intro Ψ
    rw [persistently_eq]
    refine pure_elim' fun h => ?_
    obtain ⟨p, hΨp, hp⟩ := existential h
    refine entails_trans ?_ (sExists_intro ⟨p, rfl⟩)
    refine and_intro (pure_intro hΨp) ?_
    rw [persistently_eq]
    exact pure_intro hp
  persistently_absorb_l := by
    intro P Q
    rw [persistently_eq]
    exact wand_elim (pure_elim' fun hp => wand_intro (pure_intro hp))
  persistently_and_l := by
    intro P Q
    rw [persistently_eq]
    refine imp_elim (pure_elim' fun hp => imp_intro ?_)
    exact entails_trans and_elim_r (entails_trans emp_sep.mpr (sep_mono hp entails_refl))

end PersistentlyDiscrete
