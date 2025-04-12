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
variable {A : Type}
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
    · calc x₁ ≡ x₁ • UCMRA.unit := (CMRA.unit_right_id _).symm
           _  ≼ x₁ • (m₁ • m₂)   := CMRA.op_mono_right _ (CMRA.inc_unit (m₁ • m₂))
           _  ≡ (x₁ • m₁) • m₂   := CMRA.assoc
    · exact Nat.le_trans Hnle Hn
    · exact (OFE.Dist.validN Hx).mp Hv
    · exact (uPred_ne P n Hx).mp HP

def sForall (Ψ : uPred M → Prop) : uPred M where
  uPred_holds n x := ∀ p, Ψ p → p n x
  uPred_mono := by
    simp
    intro _ _ _ _ HΨ Hv Hn p Hp
    exact p.uPred_mono (HΨ _ Hp) Hv Hn

def sExists (Ψ : uPred M → Prop) : uPred M where
  uPred_holds n x := ∃ p, Ψ p ∧ p n x
  uPred_mono := by
    simp
    intros n1 n2 x1 x2 p HΨ Hp Hv Hn
    exists p
    apply And.intro HΨ
    exact p.uPred_mono Hp Hv Hn

def internal_eq : uPred M where
  uPred_holds n _ := o1 ≡{n}≡ o2
  uPred_mono := fun H1 _ H2 => OFE.Dist.le H1 H2

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
    · apply CMRA.validN_of_incN _ Hv
      rcases Hm with ⟨ y, Hx ⟩
      exists y
      apply (OFE.Dist.le _ Hn')
      calc m₂ • x ≡{n₂}≡ (m₁ • y) • x := CMRA.op_left_dist _ Hx
           _      ≡{n₂}≡ m₁ • (y • x) := OFE.Equiv.dist (CMRA.assoc).symm
           _      ≡{n₂}≡ m₁ • (x • y) := CMRA.op_right_dist _ (OFE.Equiv.dist CMRA.comm)
           _      ≡{n₂}≡ (m₁ • x) • y := OFE.Equiv.dist CMRA.assoc
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

/-
def cmra_valid : uPred M where
  uPred_holds n x := ✓{n} m
  uPred_mono := sorry

def bupd : uPred M where
  uPred_holds n x := ∀ k yf, k ≤ n → ✓{k} (x • yf) → ∃ x', ✓{k} (x' • yf) ∧ Q k x'
  uPred_mono := sorry
-/

def emp : uPred M where
  uPred_holds _ _ := True
  uPred_mono := by simp

end bidefs

instance : BIBase (uPred M) where
  Entails      := entails
  emp          := emp
  pure         := pure
  and          := and
  or           := or
  imp          := impl
  sForall      := sForall
  sExists      := sExists
  sep          := sep
  wand         := wand
  persistently := persistently
  later        := later

instance : Std.Preorder (Entails (PROP := uPred M)) where
  refl := by
    intro P _ _ _ H
    apply H
  trans := by
    intro _ _ _ H1 H2
    intro n x Hv H
    apply H2 _ _ Hv
    apply H1 _ _ Hv
    apply H


instance later_contractive : OFE.Contractive later (α := uPred M) := by
  constructor
  intro n x y Hl
  cases n
  · intro _; simp_all [later]
  rename_i n
  intro n' x' Hn' Hx'
  cases n'
  · simp [later]
  exact Hl _ Hn' _ _ (Nat.le_refl _) (CMRA.validN_succ Hx')

-- TODO: Tidy

-- set_option pp.notation false

instance : BI (uPred M) where
  entails_preorder := by infer_instance
  equiv_iff {P Q} := by
    apply Iff.intro <;> intro HE
    · constructor <;> intro n x Hv H <;> apply (uPred_holds_ne _ _ _ _ _ _ (Nat.le_refl n) Hv H)
      · exact fun n' x a => HE.symm n' x
      · exact fun n' x a => HE n' x
    · intros n m Hv
      exact ⟨ fun H => HE.1 _ _ Hv H, fun H => HE.2 _ _ Hv H ⟩
  and_ne := by
    constructor
    intro _ _ _ H _ _ H' _ _ Hn' Hv'
    apply Iff.intro <;> intro H <;> rcases H with ⟨ H1, H2 ⟩
    · constructor
      · exact (H _ _ Hn' Hv').mp H1
      · exact (H' _ _ Hn' Hv').mp H2
    · constructor
      · exact (H.symm _ _ Hn' Hv').mp H1
      · exact (H'.symm _ _ Hn' Hv').mp H2
  or_ne := by
    constructor
    intros _ _ _ H _ _ H' _ _ Hn' Hv
    apply Iff.intro <;> intro H'' <;>  rcases H'' with H'' | H''
    · left; apply (H _ _ Hn' Hv).mp H''
    · right; apply (H' _ _ Hn' Hv).mp H''
    · left; apply (H.symm _ _ Hn' Hv).mp H''
    · right; apply (H'.symm _ _ Hn' Hv).mp H''
  imp_ne := by
    constructor
    intros _ _ _ H _ _ H' _ _ Hn' Hv
    apply Iff.intro <;> intro Hi n' x' Hle Hn'' Hx' H''
    · apply (H' _ _ (Nat.le_trans Hn'' Hn') Hx').mp
      apply (Hi _ _ Hle Hn'' Hx')
      apply (H _ _ (Nat.le_trans Hn'' Hn') Hx').mpr H''
    · apply (H' _ _ (Nat.le_trans Hn'' Hn') Hx').mpr
      apply (Hi _ _ Hle Hn'' Hx')
      apply (H _ _ (Nat.le_trans Hn'' Hn') Hx').mp H''
  sep_ne := by
    constructor
    intros _ _ _ H _ _ H' x n' Hn' Hv
    apply Iff.intro <;> intro Hi <;> rcases Hi with ⟨ z1, z2, H1, H2, H3 ⟩
    · have H1' : n' ≡{x}≡ z2 • z1 := by apply OFE.dist_eqv.trans H1 CMRA.op_commN
      exists z1; exists z2;
      apply And.intro H1
      apply And.intro
      · apply (H _ _ Hn' _).mp H2
        apply (CMRA.validN_op_right (CMRA.validN_ne H1' Hv))
      · apply (H' _ _ Hn' _).mp H3
        apply (CMRA.validN_op_right (CMRA.validN_ne H1 Hv))
    · have H1' : n' ≡{x}≡ z2 • z1 := by apply OFE.dist_eqv.trans H1 CMRA.op_commN
      exists z1; exists z2
      apply And.intro H1
      apply And.intro
      · apply (H _ _ Hn' _).mpr H2
        apply (CMRA.validN_op_right (CMRA.validN_ne H1' Hv))
      · apply (H' _ _ Hn' _).mpr H3
        apply (CMRA.validN_op_right (CMRA.validN_ne H1 Hv))
  wand_ne := by
    constructor
    intros _ _ _ H _ _ H' _ _ Hn' Hv
    apply Iff.intro <;> intro HE n x Hn Hv H''
    · apply (H' _ _ (Nat.le_trans Hn Hn') Hv).mp
      apply (HE _ _ Hn Hv _)
      apply (H _ _ (Nat.le_trans Hn Hn') (CMRA.validN_op_right Hv)).mpr
      apply H''
    · apply (H' _ _ (Nat.le_trans Hn Hn') Hv).mpr
      apply (HE _ _ Hn Hv _)
      apply (H _ _ (Nat.le_trans Hn Hn') (CMRA.validN_op_right Hv)).mp
      apply H''
  persistently_ne        := by
    constructor
    intros _ _ _ H _ _ Hn Hx
    simp [BI.persistently, persistently]
    constructor
    · intro H'; apply (H _ _ Hn (CMRA.validN_core Hx)).mp H'
    · intro H'; apply (H _ _ Hn (CMRA.validN_core Hx)).mpr H'
  later_ne := by apply OFE.instNonExpansiveOfContractive later
  sForall_ne := by
    intro n P1 P2 HR
    rcases HR with ⟨ HR1, HR2 ⟩
    simp [BI.sForall, sForall]
    intro n' x' Hn' Hx'
    simp
    apply Iff.intro
    · intro H p Hp
      rcases (HR2 p Hp) with ⟨ p', Hp', Hp'eq ⟩
      exact (@Hp'eq n' _ Hn' Hx').mp (H _ Hp')
    · intro H p Hp
      rcases (HR1 p Hp) with ⟨ p', Hp', Hp'eq ⟩
      exact (@Hp'eq n' _ Hn' Hx').mpr (H _ Hp')
  sExists_ne := by
    intro n P1 P2 HR
    rcases HR with ⟨ HR1, HR2 ⟩
    simp [BI.sExists, sExists]
    intro n' x' Hn' Hx'
    simp
    apply Iff.intro
    · rintro ⟨ p, Hp, H ⟩
      rcases (HR1 p Hp) with ⟨ p', Hp', Hp'eq ⟩
      exists p'
      exact And.intro Hp' ((@Hp'eq n' _ Hn' Hx').mp H)
    · rintro ⟨ p, Hp, H ⟩
      rcases (HR2 p Hp) with ⟨ p', Hp', Hp'eq ⟩
      exists p'
      exact And.intro Hp' ((@Hp'eq n' _ Hn' Hx').mpr H)
  pure_intro := by intros _ _ P _ _ _ _; exact P
  pure_elim' := by intros _ _ I n x a P; exact I P n x a trivial
  and_elim_l := by intros _ _ _ _ _ I; cases I; trivial
  and_elim_r := by intros _ _ _ _ _ I; cases I; trivial
  and_intro := by
    intros _ _ _ H1 H2 _ _ Hv H
    constructor
    · apply H1 _ _ Hv H
    · apply H2 _ _ Hv H
  or_intro_l := by intros _ _ _ _ Hv H; left; exact H
  or_intro_r := by intros _ _ _ _ Hv H; right; exact H
  or_elim := by
    intros _ _ _ H1 H2 _ _ Hv H
    rcases H with H | H
    · apply H1 _ _ Hv H
    · apply H2 _ _ Hv H
  imp_intro := by
    intros _ _ _ I _ _ Hv H _ _ Hin Hle Hv' HQ
    apply (I _ _ Hv')
    constructor
    · exact (uPred.uPred_mono _ H (CMRA.Included.incN Hin) Hle)
    · exact HQ
  imp_elim := by
    intros _ _ _ H' _ _ Hv H
    rcases H with ⟨ HP, HQ ⟩
    apply (H' _ _ Hv HP _ _ _ (Nat.le_refl _) Hv HQ)
    apply CMRA.inc_refl
  sForall_intro := by
    intros p Ψ H n x Hv Hp
    simp [BI.sForall, sForall]
    intros p' HΨ
    exact H _ HΨ _ _ Hv Hp
  sForall_elim := by
    intros _ p HΨ
    exact fun _ _ _ H => H p HΨ
  sExists_intro := by
    intros Ψ p H n x Hv Hp
    exists p
  sExists_elim := by
    intros Ψ p H n x Hv
    simp [BI.sExists, sExists]
    intro x' HΨ H'
    exact H x' HΨ n x Hv H'
  sep_mono := by
    intro _ _ _ _ H1 H2 n x Hv H
    rcases H with ⟨x1, x2, HE, Hx1, Hx2⟩
    exists x1
    exists x2
    apply And.intro
    · apply HE
    apply And.intro
    · apply (H1 _ _ _ Hx1)
      apply CMRA.validN_op_left (CMRA.validN_ne HE Hv)
    · apply (H2 _ _ _ Hx2)
      apply CMRA.validN_op_right (CMRA.validN_ne HE Hv)
  emp_sep := by
    intro P
    simp [BI.sep, sep, BI.emp, emp]
    constructor
    · intro _ _ _ H
      simp at H
      rcases H with ⟨ x1, x2, HE1, HE2 ⟩
      apply P.uPred_mono HE2 _ (Nat.le_refl _)
      exists x1
      apply OFE.Dist.trans HE1 CMRA.op_commN
    · intro _ x _ H
      simp
      exists UCMRA.unit
      exists x
      apply And.intro _ H
      apply OFE.equiv_dist.mp UCMRA.unit_left_id.symm
  sep_symm := by
    intros _ _ _ _ Hv H
    rcases H with ⟨ x1, x2, HE, _, _ ⟩
    exists x2; exists x1
    apply And.intro
    · apply OFE.dist_eqv.trans HE (OFE.equiv_dist.mp _ _)
      apply CMRA.comm
    apply And.intro
    · trivial
    · trivial
  sep_assoc_l := by
    intros _ _ _ n x Hv H
    rcases H with ⟨x1, x2, Hx, H, _⟩
    rcases H with ⟨y1, y2, Hy, _, _⟩
    exists y1
    exists (y2 • x2)
    apply And.intro
    · calc x ≡{n}≡ x1 • x2 := Hx
           _ ≡{n}≡ (y1 • y2) • x2 := OFE.Dist.op_l Hy
           _ ≡{n}≡ y1 • (y2 • x2) := OFE.equiv_dist.mp CMRA.assoc.symm _
    apply And.intro
    · trivial
    exists y2
    exists x2
    apply And.intro
    · apply OFE.Dist.of_eq rfl
    apply And.intro
    · trivial
    · trivial
  wand_intro := by
    intros _ _ _ H n x Hv HP n' x' Hn Hv' HQ
    apply (H _ _ Hv')
    exists x
    exists x'
    apply And.intro
    · apply OFE.Dist.of_eq rfl
    apply And.intro
    · apply (uPred.uPred_mono _ HP _ Hn)
      apply CMRA.incN_refl
    · apply HQ
  wand_elim := by
    intros _ _ _ H n x Hv H
    rcases H with ⟨y1, y2, Hy, HP, HQ⟩
    let Hwand := @H n y1 (CMRA.validN_op_left (CMRA.validN_ne Hy Hv)) HP
    let H' := Hwand _ y2 (Nat.le_refl _) (CMRA.validN_ne Hy Hv) HQ
    apply uPred.uPred_mono _ H' _ (Nat.le_refl _)
    exact CMRA.dst_incN Hy
  persistently_mono := by
    simp [BI.persistently, persistently]
    intros _ _ H n x Hv H'
    apply (H _ _ (CMRA.validN_core Hv))
    apply H'
  persistently_idem_2 := by
    intros _ _ x n H
    simp_all [BI.persistently, persistently]
    apply (uPred.uPred_mono _ H _ (Nat.le_refl _))
    apply CMRA.incN_proper2
    · exact OFE.Equiv.rfl
    apply (CMRA.core_idemp x).symm
    exact CMRA.incN_refl (CMRA.core x)
  persistently_emp_2 := by simp [BI.persistently, persistently, BI.emp, emp]
  persistently_and_2 := by simp [BI.persistently, BI.and, persistently, and]
  persistently_sExists_1 := by
    -- simp [BI.persistently, BI.and, persistently, and, BI.sExists, sExists, BI.pure, pure, «exists»]
    intro Ψ n x v H
    rcases H with ⟨ p, HΨ, H ⟩
    simp [«exists», BI.sExists, sExists]
    exists iprop(<pers> p) -- iprop(⌜Ψ p⌝ ∧ <pers> p)
    simp [BI.persistently, persistently]
    apply And.intro _ H
    exists p
    simp [BI.and, and, BI.pure, pure]
    apply funext; intro n
    apply funext; intro x'
    apply propext
    simp [HΨ]
  persistently_absorb_l  := by
    simp [BI.persistently, BI.and, persistently, and, BI.sep, sep]
    intros P Q _ x _ H
    rcases H with ⟨ x1, x2, H1, H2, H3 ⟩
    simp
    apply P.uPred_mono H2 _ (Nat.le_refl _)
    apply CMRA.core_incN_core
    exists x2
  persistently_and_l     := by
    simp [BI.persistently, BI.and, persistently, and, BI.sep, sep]
    intros P Q _ x _ H
    simp
    exists (CMRA.core x)
    exists x
    apply And.intro _ H
    apply OFE.equiv_dist.mp
    apply (CMRA.core_op _).symm
  later_mono := by
    intros P Q H n x Hv
    simp [BI.later, later ]
    cases n <;> simp
    intro Hp
    apply H _ _ _ Hp
    exact CMRA.validN_succ Hv
  later_intro := by
    intros P n _ _ Hp
    simp [BI.later, later]
    cases n <;> simp
    apply uPred.uPred_mono _ Hp (CMRA.incN_refl _) (Nat.le_add_right _ _)
  later_sForall_2 := by
    intro Ψ n x Hx
    simp [BI.later, later, BI.pure, pure, BI.sForall, sForall, BI.imp, impl, «forall»]
    cases n <;> simp
    rename_i n
    intro H p Hp
    have H' := H p (n + 1) x
    apply H' (CMRA.inc_refl x) (Nat.le_refl _) Hx Hp
  later_sExists_false := by
    intro Ψ
    intro n x Hx H
    cases n
    · left; simp_all [BI.later, later]
    · right
      simp [BI.later, later, BI.sExists, sExists] at H
      rcases H with ⟨ p', Hp', H ⟩
      exists (BI.later p')
      simp [BI.later]
      apply And.intro _ H
      exists p'
      simp [BI.later, later, BI.pure, pure, BI.and, and]
      apply funext; intro n
      apply funext; intro x
      apply propext
      simp [Hp']
  later_sep := by
    intros P Q
    simp [BI.later, later, BI.sep, sep]
    constructor
    · intros n x Hv H
      cases n <;> simp_all
      · exists UCMRA.unit
        exists x
        apply OFE.dist_eqv.symm
        apply OFE.equiv_dist.mp
        apply UCMRA.unit_left_id
      · rcases H with ⟨ x1, x2, H1, H2, H3 ⟩
        rcases CMRA.extend (CMRA.validN_succ Hv) H1 with ⟨ y1, y2, H1', H2', H3' ⟩
        exists y1
        exists y2
        apply And.intro
        · exact OFE.Equiv.dist H1'
        apply And.intro
        · exact (uPred_ne P _ H2').mpr H2
        · exact (uPred_ne Q _ H3').mpr H3
    · intros n x _ H
      cases n <;> simp_all
      rcases H with ⟨ x1, x2, H1, H2, H3 ⟩
      exists x1
      exists x2
      apply And.intro _ ⟨ H2, H3 ⟩
      apply OFE.Dist.lt H1 (Nat.lt_add_one _)
  later_persistently := by
    intro _ _
    constructor <;> simp [BI.persistently, persistently, BI.later, later]
  later_false_em := by
    intro P n x Hv
    simp [BI.later, later, BI.imp, imp, BI.or, or]
    cases n <;> simp
    intro H
    right
    intro n' x' Hx'le Hn' Hv'
    simp
    cases n' <;> simp
    · apply P.uPred_mono H (CMRA.Included.incN Hx'le) (Nat.zero_le _)
    intro H''
    exact False.elim H''

instance : BILaterContractive (uPred M) where
  toContractive := later_contractive

end uPred
