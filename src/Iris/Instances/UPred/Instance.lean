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
  uPred_mono := sorry

def and : uPred M where
  uPred_holds n x := P n x ∧ Q n x
  uPred_mono := sorry

def or : uPred M where
  uPred_holds n x := P n x ∨ Q n x
  uPred_mono := sorry

def impl : uPred M where
  uPred_holds n x := ∀ n' x', x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x'
  uPred_mono := sorry

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
  uPred_mono := sorry

def wand : uPred M where
  uPred_holds n x := ∀ n' x', n' ≤ n → ✓{n'} (x • x') → P n' x' → Q n' (x • x')
  uPred_mono := sorry

def plainly : uPred M where
  uPred_holds n _ := P n UCMRA.unit
  uPred_mono := sorry

def persistently : uPred M where
  uPred_holds n x := P n (CMRA.core x)
  uPred_mono := sorry

def later : uPred M where
  uPred_holds n x := match n with | 0 => True | Nat.succ n' => P n' x
  uPred_mono := sorry

def ownM : uPred M where
  uPred_holds n x := m ≼{n} x
  uPred_mono := sorry

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
