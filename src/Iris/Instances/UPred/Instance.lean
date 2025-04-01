/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI
import Iris.Algebra.OFE
import Iris.Algebra.CMRA
import Iris.Algebra.uPred

section UPredInstance

open Iris BI

namespace uPred

variable {M : Type} [UCMRA M]

section bidefs

variable (P Q : uPred M)
variable {A : Type} (Ψ : A -> uPred M)
variable {O : Type} [OFE O] (o1 o2 : O)
variable (m : M)

def entails : Prop := ∀ n x, ✓{n} x → P n x → Q n x

def pure (p : Prop) : uPred M where
  uPred_holds _ _ := p
  uPred_mono := by simp only; intros; trivial

def and : uPred M where
  uPred_holds n x := P n x ∧ Q n x
  uPred_mono := by
    simp; exact fun HP HQ Hle Hn => ⟨ P.uPred_mono HP Hle Hn, Q.uPred_mono HQ Hle Hn ⟩

def or : uPred M where
  uPred_holds n x := P n x ∨ Q n x
  uPred_mono := by
    simp
    intros _ _ _ _ H
    cases H <;> rename_i H
    · exact fun Hle Hn => Or.inl (P.uPred_mono H Hle Hn)
    · exact fun Hle Hn => Or.inr (Q.uPred_mono H Hle Hn)

def impl : uPred M where
  uPred_holds n x := ∀ n' x', x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x'
  uPred_mono := by
    simp
    intros n₁ n₂ x₁ x₂ H Hle Hn n x Hxle Hnle Hv HP
    rcases Hle with ⟨m₁, Hle⟩
    rcases Hxle with ⟨m₂, Hxle⟩
    let Hx :=
      calc x ≡{n}≡ x₂ • m₂          := OFE.Equiv.dist Hxle
           _ ≡{n}≡ (x₁ • m₁) • m₂   := CMRA.op_left_dist _ (OFE.Dist.le Hle Hnle)
    apply (uPred_ne _ _ Hx).mpr
    apply H
    · exact CMRA.inc_unit
    · exact Nat.le_trans Hnle Hn
    · exact (OFE.Dist.validN Hx).mp Hv
    · exact (uPred_ne P n Hx).mp HP

def sForall : uPred M where
  uPred_holds n x := ∀ a, Ψ a n x
  uPred_mono := sorry

def sExists : uPred M where
  uPred_holds n x := ∃ a, Ψ a n x
  uPred_mono := sorry

def internal_eq : uPred M where
  uPred_holds n _ := o1 ≡{n}≡ o2
  uPred_mono := sorry

def sep : uPred M where
  uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 • x2 ∧ P n x1 ∧ Q n x2
  uPred_mono := by
    simp
    intros n₁ n₂ m₁ m₂ x₁ x₂ Hx HP HQ Hm Hn
    rcases Hm with ⟨m, Hm⟩
    exists x₁
    exists (x₂ • m)
    apply And.intro
    · calc m₂ ≡{n₂}≡ m₁ • m := Hm
           _  ≡{n₂}≡ (x₁ • x₂) • m := CMRA.op_left_dist _ (OFE.Dist.le Hx Hn)
           _  ≡{n₂}≡ x₁ • (x₂ • m) := OFE.Equiv.dist (OFE.Equiv.symm CMRA.assoc)
    apply And.intro
    · apply P.uPred_mono HP (CMRA.incN_refl x₁) Hn
    · apply Q.uPred_mono HQ (CMRA.incN_op_left n₂ x₂ m) Hn

def wand : uPred M where
  uPred_holds n x := ∀ n' x', n' ≤ n → ✓{n'} (x • x') → P n' x' → Q n' (x • x')
  uPred_mono := by
    simp
    intros n₁ n₂ m₁ m₂ H Hm Hn n' x Hn' Hv HP
    apply Q.uPred_mono _ (CMRA.op_monoN_left _ (CMRA.incN_of_incN_le Hn' Hm)) (Nat.le_refl _)
    apply H
    · exact Nat.le_trans Hn' Hn
    · exact CMRA.unit_validN n'
    · exact HP

def plainly : uPred M where
  uPred_holds n _ := P n UCMRA.unit
  uPred_mono := by
    simp; exact fun H Hx Hn => P.uPred_mono H (CMRA.incN_refl UCMRA.unit) Hn

def persistently : uPred M where
  uPred_holds n x := P n (CMRA.core x)
  uPred_mono := by
    simp; exact fun H Hx Hn => P.uPred_mono H (CMRA.core_incN_core Hx) Hn

def later : uPred M where
  uPred_holds n x := match n with | 0 => True | Nat.succ n' => P n' x
  uPred_mono := by
    intros n₁ n₂; cases n₁ <;> cases n₂ <;> simp
    exact fun H Hx Hn => P.uPred_mono H (CMRA.incN_of_incN_succ Hx) Hn

def ownM : uPred M where
  uPred_holds n x := m ≼{n} x
  uPred_mono := by
    simp
    intros n₁ n₂ x₁ x₂ Hm₁ Hm₂ Hn
    rcases Hm₁ with ⟨m₁, Hm₁⟩
    rcases Hm₂ with ⟨m₂, Hm₂⟩
    exists (m₁ • m₂)
    calc x₂ ≡{n₂}≡ x₁ • m₂ := Hm₂
         _  ≡{n₂}≡ (m • m₁) • m₂ := CMRA.op_left_dist _ (OFE.Dist.le Hm₁ Hn)
         _  ≡{n₂}≡ m • (m₁ • m₂) := OFE.Equiv.dist (OFE.Equiv.symm CMRA.assoc)

def cmra_valid : uPred M where
  uPred_holds n x := ✓{n} m
  uPred_mono := sorry

def bupd : uPred M where
  uPred_holds n x := ∀ k yf, k ≤ n → ✓{k} (x • yf) → ∃ x', ✓{k} (x' • yf) ∧ Q k x'
  uPred_mono := sorry

end bidefs

instance : BIBase (uPred M) where
  Entails      := entails
  emp          := sorry
  pure         := pure
  and          := and
  or           := or
  imp          := impl
  sForall Ψ    := sorry -- Why do they define sForall and «forall» like this?
  sExists Ψ    := sorry -- ??
  sep          := sep
  wand         := wand
  persistently := persistently
  later        := later


instance : Std.Preorder (Entails (PROP := uPred M)) where
  refl := sorry
  trans := sorry

instance : BI (uPred M) where
  entails_preorder       := by infer_instance
  equiv_iff              := sorry
  and_ne                 := sorry
  or_ne                  := sorry
  imp_ne                 := sorry
  sep_ne                 := sorry
  wand_ne                := sorry
  persistently_ne        := sorry
  later_ne               := sorry
  sForall_ne             := sorry
  sExists_ne             := sorry
  pure_intro             := sorry
  pure_elim'             := sorry
  and_elim_l             := sorry
  and_elim_r             := sorry
  and_intro              := sorry
  or_intro_l             := sorry
  or_intro_r             := sorry
  or_elim                := sorry
  imp_intro              := sorry
  imp_elim               := sorry
  sForall_intro          := sorry
  sForall_elim           := sorry
  sExists_intro          := sorry
  sExists_elim           := sorry
  sep_mono               := sorry
  emp_sep                := sorry
  sep_symm               := sorry
  sep_assoc_l            := sorry
  wand_intro             := sorry
  wand_elim              := sorry
  persistently_mono      := sorry
  persistently_idem_2    := sorry
  persistently_emp_2     := sorry
  persistently_and_2     := sorry
  persistently_sExists_1 := sorry
  persistently_absorb_l  := sorry
  persistently_and_l     := sorry
  later_mono             := sorry
  later_intro            := sorry
  later_sForall_2        := sorry
  later_sExists_false    := sorry
  later_sep              := sorry
  later_persistently     := sorry
  later_false_em         := sorry

end uPred
