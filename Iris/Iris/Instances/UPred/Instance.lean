/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Mario Carneiro, Viet Anh Nguyen
-/
module

public import Iris.BI
public import Iris.Algebra.OFE
public import Iris.Algebra.CMRA
public import Iris.Algebra.UPred
public import Iris.Algebra.Updates
public import Iris.BI.Lib.BUpdPlain
public meta import Iris.Std.RocqPorting
public meta import Iris.Std.RocqPorting

@[expose] public section

section UPredInstance

open Iris BI

namespace UPred

variable [UCMRA M]

section bidefs

protected def Entails (P Q : UPred M) : Prop := ∀ n (x : ValidAt M n), P n x → Q n x

protected def pure (p : Prop) : UPred M where
  holds _ _ := p
  mono h _ _ := h

protected def and (P Q : UPred M) : UPred M where
  holds n x := P n x ∧ Q n x
  mono HPQ Hle Hn := ⟨P.mono HPQ.1 Hle Hn, Q.mono HPQ.2 Hle Hn⟩

protected def or (P Q : UPred M) : UPred M where
  holds n x := P n x ∨ Q n x
  mono
  | .inl H, Hle, Hn => .inl (P.mono H Hle Hn)
  | .inr H, Hle, Hn => .inr (Q.mono H Hle Hn)

protected def imp (P Q : UPred M) : UPred M where
  holds n x := ∀ n' (x' : ValidAt M n'), x.val ≼ x'.val → n' ≤ n → P n' x' → Q n' x'
  mono {n₁ n₂ x₁ x₂} H := fun ⟨m₁, Hle⟩ Hn n x ⟨m₂, Hxle⟩ Hnle HP => by
    have Hx :=
      calc x.val ≡{n}≡ x₂ • m₂    := Hxle.dist
           _     ≡{n}≡ (x₁ • m₁) • m₂ := (Hle.le Hnle).op_l
    refine (uPred_ne (m₂ := ⟨(x₁.val • m₁) • m₂, Hx.validN.mp x.property⟩) Hx).mpr
      (H _ _ ?_ ?_ ?_)
    · calc x₁.val ≡ x₁ • UCMRA.unit  := CMRA.unit_right_id.symm
           _  ≼ x₁ • (m₁ • m₂)   := CMRA.op_mono_right _ CMRA.inc_unit
           _  ≡ (x₁ • m₁) • m₂   := CMRA.assoc
    · exact Nat.le_trans Hnle Hn
    · exact (uPred_ne Hx).mp HP

protected def sForall (Ψ : UPred M → Prop) : UPred M where
  holds n x := ∀ p, Ψ p → p n x
  mono a a_1 a_2 p a_3 := p.mono (a p a_3) a_1 a_2

protected def sExists (Ψ : UPred M → Prop) : UPred M where
  holds n x := ∃ p, Ψ p ∧ p n x
  mono := fun ⟨p, HΨ, Hp⟩ Hv Hn => ⟨p, HΨ, p.mono Hp Hv Hn⟩

protected def eq [OFE O] (o1 o2 : O) : UPred M where
  holds n _ := o1 ≡{n}≡ o2
  mono H1 _ H2 := H1.le H2

protected def sep (P Q : UPred M) : UPred M where
  holds n x := ∃ x1 x2, ∃ (H : x.val ≡{n}≡ x1 • x2),
    P n ⟨x1, CMRA.validN_op_left (CMRA.validN_ne H x.property)⟩
    ∧ Q n ⟨x2, CMRA.validN_op_right (CMRA.validN_ne H x.property)⟩
  mono {n₁ n₂ m₁ m₂} := fun ⟨x₁, x₂, Hx, HP, HQ⟩ ⟨m, Hm⟩ Hn => by
    refine ⟨x₁, x₂ • m, ?_, ?_, ?_⟩
    · calc m₂.val ≡{n₂}≡ m₁ • m := Hm
          _       ≡{n₂}≡ (x₁ • x₂) • m := (Hx.le Hn).op_l
          _       ≡{n₂}≡ x₁ • (x₂ • m) := CMRA.assoc.symm.dist
    · exact P.mono HP (CMRA.incN_refl x₁) Hn
    · exact Q.mono HQ (CMRA.incN_op_left n₂ x₂ m) Hn

protected def wand (P Q : UPred M) : UPred M where
  holds n x := ∀ n' x', n' ≤ n → (H : ✓{n'} (x.val • x'))
    → P n' ⟨x', CMRA.validN_op_right H⟩ → Q n' ⟨x • x', H⟩
  mono {n₁ n₂ m₁ m₂} H Hm Hn n' x Hn' Hv HP := by
    refine Q.mono_unpacked (CMRA.validN_of_incN (CMRA.op_monoN_left _ (Hm.le Hn')) Hv) Hv ?_
      (CMRA.op_monoN_left _ (CMRA.incN_of_incN_le Hn' Hm)) (Nat.le_refl _)
    let ⟨y, Hx⟩ := Hm
    refine H _ _ (Nat.le_trans Hn' Hn) ?_ HP

protected def plainly (P : UPred M) : UPred M where
  holds n _ := P n ⟨UCMRA.unit, CMRA.unit_validN⟩
  mono H _ Hn := P.mono H (CMRA.incN_refl UCMRA.unit) Hn

protected def persistently (P : UPred M) : UPred M where
  holds n x := P n ⟨CMRA.core x, CMRA.validN_core x.property⟩
  mono H Hx Hn := P.mono H (CMRA.core_incN_core Hx) Hn

protected def later (P : UPred M) : UPred M where
  holds n x := match n with | 0 => True | Nat.succ n' => P n' (x.le (Nat.le_succ _))
  mono {n₁ n₂} := by
    cases n₁ <;> cases n₂ <;> simp
    exact fun H Hx Hn => P.mono H (CMRA.incN_of_incN_succ Hx) Hn

def ownM (m : M) : UPred M where
  holds n x := m ≼{n} x
  mono {n₁ n₂ x₁ x₂} := fun ⟨m₁, Hm₁⟩ ⟨m₂, Hm₂⟩ Hn => by
    exists m₁ • m₂
    calc x₂.val ≡{n₂}≡ x₁ • m₂ := Hm₂
         _      ≡{n₂}≡ (m • m₁) • m₂ := (Hm₁.le Hn).op_l
         _      ≡{n₂}≡ m • (m₁ • m₂) := CMRA.assoc.symm.dist

def cmraValid {A} [CMRA A] (a : A) : UPred M where
  holds n _ := ✓{n} a
  mono hv _ le := CMRA.validN_of_le le hv

def bupd (Q : UPred M) : UPred M where
  holds n x := ∀ k yf, k ≤ n → ✓{k} (x.val • yf)
    → ∃ x', ∃ H : ✓{k} (x' • yf), Q k ⟨x', CMRA.validN_op_left H⟩
  mono {n1 n2} {x1 x2} HQ := by
    rintro ⟨x3, Hx⟩ Hn k yf Hk Hx0
    have Hxy' : ✓{k} x1.val • (x3 • yf) := by
      refine CMRA.validN_ne ?_ Hx0
      refine .trans ?_ CMRA.op_assocN.symm
      exact CMRA.op_left_dist _ (OFE.Dist.le Hx Hk)
    rcases HQ k (x3 • yf) (Nat.le_trans Hk Hn) Hxy' with ⟨x', Hx', HQ'⟩
    exists (x' • x3)
    refine ⟨CMRA.validN_ne CMRA.op_assocN Hx', ?_⟩
    refine Q.mono HQ' ?_ k.le_refl
    exact CMRA.incN_op_left k x' x3

protected def emp : UPred M where
  holds _ _ := True
  mono _ _ _ := trivial

end bidefs

@[rocq_alias uPred_primitive.persistently_ne]
instance persistently_ne : OFE.NonExpansive UPred.persistently (α := UPred M) where
  ne _ _ _ H _ _ Hn Hx := H _ _ Hn (CMRA.validN_core Hx)

@[rocq_alias uPred_primitive.later_contractive]
instance later_contractive : OFE.Contractive UPred.later (α := UPred M) where
  distLater_dist {n x y} Hl :=
    match n with
    | 0 => by
      intro _ _ Hle _
      simp only [Nat.le_zero_eq] at Hle; subst Hle; simp_all [UPred.later]
    | n + 1 => fun
      | 0 => by simp [UPred.later]
      | n' + 1 => fun x' Hn' Hx' => Hl _ Hn' _ _ (Nat.le_refl _) (CMRA.validN_succ Hx')

@[rocq_alias uPred_primitive.ownM_ne]
instance ownM_ne : OFE.NonExpansive (ownM : M → UPred M) where
  ne _ _ _ H _ _ Hn _ := OFE.Dist.incN (OFE.Dist.le H Hn) .rfl

instance {A} [CMRA A] : OFE.NonExpansive (cmraValid : A → UPred M) where
  ne _ _ _ H _ _ Hn _ := (H.le Hn).validN

@[rocq_alias uPred_primitive.bupd_ne]
instance bupd_ne : OFE.NonExpansive (bupd : UPred M → UPred M) where
  ne n x1 x2 Hx m y Hm Hv := by
    constructor
    · intro H k yf Hk Hyf
      rcases (H k yf Hk Hyf) with ⟨x', ⟨Hx'1, Hx'2⟩⟩
      refine ⟨x', ⟨Hx'1, ?_⟩⟩
      refine uPred_holds_ne ?_ k.le_refl (CMRA.validN_op_left Hx'1) _ Hx'2
      exact OFE.Dist.le Hx.symm (Nat.le_trans Hk Hm)
    · intro H k yf Hk Hyf
      rcases (H k yf Hk Hyf) with ⟨x', ⟨Hx'1, Hx'2⟩⟩
      refine ⟨x', ⟨Hx'1, ?_⟩⟩
      refine uPred_holds_ne ?_ k.le_refl (CMRA.validN_op_left Hx'1) _ Hx'2
      exact OFE.Dist.le Hx (Nat.le_trans Hk Hm)

instance : BIBase (UPred M) where
  Entails      := UPred.Entails
  emp          := UPred.emp
  pure         := UPred.pure
  and          := UPred.and
  or           := UPred.or
  imp          := UPred.imp
  sForall      := UPred.sForall
  sExists      := UPred.sExists
  sep          := UPred.sep
  wand         := UPred.wand
  persistently := UPred.persistently
  later        := UPred.later

instance uPred_entails_preorder : Std.Preorder (Entails (PROP := UPred M)) where
  refl _ _ H := H
  trans H1 H2 _ _ Hv := H2 _ _ <| H1 _ _ Hv

theorem uPred_entails_lim {cP cQ : Chain (UPred M)} (H : ∀ n, cP n ⊢ cQ n) :
    IsCOFE.compl cP ⊢ IsCOFE.compl cQ := by
  intros n Hv HP
  refine uPred_holds_ne IsCOFE.conv_compl n.le_refl _ Hv.property ?_
  refine H _ _ Hv ?_
  exact uPred_holds_ne IsCOFE.conv_compl.symm n.le_refl _ Hv.property HP

instance : BI (UPred M) where
  entails_preorder := inferInstance
  equiv_iff {P Q} := by
    constructor <;> intro HE
    · constructor <;> intro n ⟨x, Hv⟩ H <;> apply uPred_holds_ne ?_ (Nat.le_refl n) Hv Hv H
      · exact fun n' x a => HE.symm n' x
      · exact fun n' x a => HE n' x
    · intro n m Hv
      exact ⟨fun H => HE.1 _ ⟨_, Hv⟩ H, fun H => HE.2 _ ⟨_, Hv⟩ H⟩
  and_ne.ne _ _ _ H _ _ H' _ _ Hn' Hv' := by
    constructor <;> intro H <;> rcases H with ⟨H1, H2⟩
    · constructor
      · exact (H _ _ Hn' Hv').mp H1
      · exact (H' _ _ Hn' Hv').mp H2
    · constructor
      · exact (H.symm _ _ Hn' Hv').mp H1
      · exact (H'.symm _ _ Hn' Hv').mp H2
  or_ne.ne _ _ _ H _ _ H' _ _ Hn' Hv := by
    constructor <;> intro H'' <;>  rcases H'' with H'' | H''
    · left; exact (H _ _ Hn' Hv).mp H''
    · right; exact (H' _ _ Hn' Hv).mp H''
    · left; exact (H.symm _ _ Hn' Hv).mp H''
    · right; exact (H'.symm _ _ Hn' Hv).mp H''
  imp_ne.ne _ _ _ H _ _ H' _ _ Hn' Hv := by
    constructor <;> intro Hi n' x' Hle Hn'' H''
    · refine (H' _ _ (Nat.le_trans Hn'' Hn') x'.property).mp ?_
      refine Hi _ _ Hle Hn'' ?_
      exact (H _ _ (Nat.le_trans Hn'' Hn') x'.property).mpr H''
    · refine (H' _ _ (Nat.le_trans Hn'' Hn') x'.property).mpr ?_
      refine Hi _ _ Hle Hn'' ?_
      exact (H _ _ (Nat.le_trans Hn'' Hn') x'.property).mp H''
  sep_ne.ne _ _ _ H _ _ H' x n' Hn' Hv := by
    constructor <;> intro Hi <;> rcases Hi with ⟨z1, z2, H1, H2, H3⟩
    · refine ⟨z1, z2, H1, (H _ _ Hn' ?_).mp H2, (H' _ _ Hn' ?_).mp H3⟩
      · exact CMRA.validN_op_right ((H1.trans CMRA.op_commN).validN.1 Hv)
      · exact CMRA.validN_op_right (H1.validN.1 Hv)
    · refine ⟨z1, z2, H1, (H _ _ Hn' ?_).mpr H2, (H' _ _ Hn' ?_).mpr H3⟩
      · exact CMRA.validN_op_right ((H1.trans CMRA.op_commN).validN.1 Hv)
      · exact CMRA.validN_op_right (H1.validN.1 Hv)
  wand_ne.ne _ _ _ H _ _ H' _ _ Hn' Hv := by
    constructor <;> intro HE n x Hn Hv H''
    · refine (H' _ _ (Nat.le_trans Hn Hn') Hv).mp ?_
      refine HE _ _ Hn Hv ?_
      exact (H _ _ (Nat.le_trans Hn Hn') (CMRA.validN_op_right Hv)).mpr H''
    · refine (H' _ _ (Nat.le_trans Hn Hn') Hv).mpr ?_
      refine HE _ _ Hn Hv ?_
      exact (H _ _ (Nat.le_trans Hn Hn') (CMRA.validN_op_right Hv)).mp H''
  persistently_ne := persistently_ne
  later_ne := inferInstanceAs (OFE.NonExpansive UPred.later)
  sForall_ne := fun ⟨HR1, HR2⟩ n' x' Hn' Hx' => by
    constructor
    · intro H p Hp
      let ⟨p', Hp', Hp'eq⟩ := HR2 p Hp
      exact (Hp'eq n' _ Hn' Hx').mp (H _ Hp')
    · intro H p Hp
      let ⟨p', Hp', Hp'eq⟩ := HR1 p Hp
      exact (Hp'eq n' _ Hn' Hx').mpr (H _ Hp')
  sExists_ne := fun ⟨HR1, HR2⟩ n' x' Hn' Hx' => by
    constructor <;> rintro ⟨p, Hp, H⟩
    · let ⟨p', Hp', Hp'eq⟩ := HR1 p Hp
      exact ⟨p', Hp', (Hp'eq n' _ Hn' Hx').mp H⟩
    · let ⟨p', Hp', Hp'eq⟩ := HR2 p Hp
      exact ⟨p', Hp', (Hp'eq n' _ Hn' Hx').mpr H⟩
  pure_intro P _ _ _ := P
  pure_elim' I n x P := I P n x trivial
  and_elim_l _ _ I := I.1
  and_elim_r _ _ I := I.2
  and_intro H1 H2 _ Hv H := ⟨H1 _ Hv H, H2 _ Hv H⟩
  or_intro_l _ _ H := .inl H
  or_intro_r _ _ H := .inr H
  or_elim H1 H2 _ Hv := fun
    | .inl H => H1 _ Hv H
    | .inr H => H2 _ Hv H
  imp_intro I _ _ HP _ Hv Hin Hle HQ :=
    I _ Hv ⟨UPred.mono _ HP Hin.incN Hle, HQ⟩
  imp_elim H' _ Hv := fun ⟨HP, HQ⟩ =>
    H' _ Hv HP _ Hv (CMRA.inc_refl _) (Nat.le_refl _) HQ
  sForall_intro H _ _ Hp _ HΨ := H _ HΨ _ _ Hp
  sForall_elim HΨ _ _ H := H _ HΨ
  sExists_intro H _ _ Hp := ⟨_, H, Hp⟩
  sExists_elim H _ Hv := fun ⟨_, HΨ, H'⟩ => H _ HΨ _ Hv H'
  sep_mono H1 H2 n x :=
    fun ⟨x1, x2, HE, Hx1, Hx2⟩ => ⟨x1, x2, HE, H1 _ _ Hx1, H2 _ _ Hx2⟩
  emp_sep {P} := by
    constructor
    · intro _ _ ⟨x1, x2, HE1, _, HE2⟩
      exact P.mono HE2 ⟨x1, HE1.trans CMRA.op_commN⟩ (Nat.le_refl _)
    · intro _ x H
      exact ⟨_, _, UCMRA.unit_left_id.symm.dist, ⟨⟩, H⟩
  sep_symm _ _ := fun ⟨x1, x2, HE, HP, HQ⟩ => by
    refine ⟨x2, x1, ?_, HQ, HP⟩
    exact HE.trans CMRA.comm.dist
  sep_assoc_l n x := fun ⟨x1, x2, Hx, ⟨y1, y2, Hy, h1, h2⟩, h3⟩ => by
    refine ⟨y1, y2 • x2, ?_, h1, y2, x2, .rfl, h2, h3⟩
    calc x.val ≡{n}≡ x1 • x2 := Hx
         _ ≡{n}≡ (y1 • y2) • x2 := Hy.op_l
         _ ≡{n}≡ y1 • (y2 • x2) := CMRA.assoc.symm.dist
  wand_intro H n x HP n' x' Hn Hv HQ :=
    H _ _ ⟨x, x', .rfl, UPred.mono _ HP .rfl Hn, HQ⟩
  wand_elim H n x := fun ⟨y1, y2, Hy, HP, HQ⟩ => by
    have Hv := Hy.validN.1 x.property
    refine UPred.mono (x1 := ⟨y1 • y2, Hv⟩) _ ?_ Hy.symm.to_incN (Nat.le_refl _)
    exact H n ⟨y1, (CMRA.validN_op_left Hv)⟩ HP _ y2 (Nat.le_refl _) Hv HQ
  persistently_mono H n x H' := H _ ⟨_, CMRA.validN_core x.property⟩ H'
  persistently_idem_2 {P} _ x H := by
    refine P.mono H ?_ (Nat.le_refl _)
    refine (CMRA.incN_iff_right ?_).mpr (CMRA.incN_refl _)
    exact (CMRA.core_idem x.val).dist
  persistently_emp_2 := Std.refl
  persistently_and_2 := Std.refl
  persistently_sExists_1 n x := fun ⟨p, HΨ, H⟩ => by
    refine ⟨iprop(<pers> p), ⟨p, ?_⟩, H⟩
    ext; exact and_iff_right HΨ
  persistently_absorb_l {P Q} _ x := fun ⟨x1, x2, H1, H2, H3⟩ =>
    P.mono H2 (CMRA.core_incN_core ⟨x2, H1⟩) (Nat.le_refl _)
  persistently_and_l _ x H := ⟨CMRA.core x, x, (CMRA.core_op _).symm.dist, H⟩
  later_mono H := fun
    | 0, _ => id
    | _+1, x => H _ ⟨_, CMRA.validN_succ x.property⟩
  later_intro {P} := fun
    | 0, _, _ => trivial
    | _+1, _, Hp => P.mono Hp (CMRA.incN_refl _) (Nat.le_add_right ..)
  later_sForall_2 {Ψ} := fun
    | 0, _, _ => trivial
    | _+1, _, H => fun _ => by
      exact H _ ⟨_, rfl⟩ _ _ (CMRA.inc_refl _) (Nat.le_refl _)
  later_sExists_false := fun
    | 0, _, _ => .inl trivial
    | _+1, x, ⟨p', Hp', H⟩ => by
      refine .inr ⟨later p', ⟨p', ?_⟩, H⟩
      ext n x; exact and_iff_right Hp'
  later_sep {P Q} := by
    constructor <;> rintro (_ | n) x H
    · exact ⟨UCMRA.unit, x, UCMRA.unit_left_id.dist.symm, trivial, trivial⟩
    · let ⟨x1, x2, H1, H2, H3⟩ := H
      let ⟨y1, y2, H1', H2', H3'⟩ := CMRA.extend (CMRA.validN_succ x.property) H1
      exact ⟨y1, y2, H1'.dist,
        (uPred_ne (m₁ := ⟨_, _⟩) (m₂ := ⟨_, _⟩) H2').mpr H2,
        (uPred_ne (m₁ := ⟨_, _⟩) (m₂ := ⟨_, _⟩) H3').mpr H3⟩
    · trivial
    · let ⟨x1, x2, H1, H2, H3⟩ := H
      exact ⟨x1, x2, H1.lt (Nat.lt_add_one _), H2, H3⟩
  later_persistently := ⟨fun | 0, _ | _+1, _ => id, fun | 0, _ | _+1, _ => id⟩
  later_false_em {P} := fun
    | 0, _, _ => .inl trivial
    | _+1, x, H => .inr fun
      | 0, x', Hx'le, Hn', _ => P.mono H Hx'le.incN (Nat.zero_le _)

@[rocq_alias uPred_persistently_forall]
instance : BIPersistentlyForall (UPred M) where
  persistently_sForall_2 _ _ x h p hp :=
    h _ ⟨p, rfl⟩ _ x (CMRA.inc_refl _) (Nat.le_refl _) hp

@[rocq_alias uPred_later_contractive]
instance : BILaterContractive (UPred M) where
  toContractive := later_contractive

instance (P : UPred M) : Affine P where
  affine _ := by simp [emp, UPred.emp]

@[rocq_alias uPred_affine]
instance : BIAffine (UPred M) := ⟨by infer_instance⟩

protected def uPredSiPure (Pi : SiProp) : UPred M where
  holds n _ := Pi.holds n
  mono H _ Hn := Pi.closed H Hn

protected def uPredSiEmpValid (P : UPred M) : SiProp where
  holds n := P n ⟨UCMRA.unit, CMRA.unit_validN⟩
  closed h hle := P.mono h (CMRA.incN_refl _) hle

@[rocq_alias si_pure_ne]
instance uPredSiPure_ne : OFE.NonExpansive (UPred.uPredSiPure : SiProp → UPred M) where
  ne _ _ _ hp _ _ hn _ := hp hn

@[rocq_alias si_emp_valid_ne]
instance uPredSiEmpValid_ne : OFE.NonExpansive (UPred.uPredSiEmpValid : UPred M → SiProp) where
  ne _ _ _ h m hm := h m UCMRA.unit hm CMRA.unit_validN

instance : SiPure (UPred M) := ⟨UPred.uPredSiPure⟩

instance : SiEmpValid (UPred M) := ⟨UPred.uPredSiEmpValid⟩

section SiPropEmbedding

/-
## Rules for the SiProp embedding
-/

@[rocq_alias si_pure_mono]
theorem uPredSiPure_mono {Pi Qi : SiProp} (hpq : Pi ⊢ Qi) : <si_pure> Pi ⊢@{UPred M} <si_pure> Qi :=
  fun n _ hp => hpq n hp

@[rocq_alias si_emp_valid_mono]
theorem uPredSiEmpValid_mono {P Q : UPred M} (h : P ⊢ Q) : <si_emp_valid> P ⊢ <si_emp_valid> Q :=
  fun n hp => h n ⟨CMRA.unit, CMRA.unit_validN⟩ hp

@[rocq_alias si_pure_impl_2]
theorem uPredSiPure_imp_mpr {Pi Qi : SiProp} :
    (<si_pure> Pi → <si_pure> Qi) ⊢@{UPred M} <si_pure> (Pi → Qi) :=
  fun _ x hpq m hle => hpq m (x.le hle) .rfl hle

@[rocq_alias si_pure_later]
theorem uPredSiPure_later {Pi : SiProp} : <si_pure> (▷ Pi) ⊣⊢@{UPred M} ▷ <si_pure> Pi :=
  ⟨fun | 0, _ | _+1, _ => id, fun | 0, _ | _+1, _ => id⟩

@[rocq_alias si_emp_valid_later_1]
theorem uPredSiEmpValid_later_mp {P : UPred M} : <si_emp_valid> (▷ P) ⊢ ▷ <si_emp_valid> P :=
  fun | 0 | _+1 => id

@[rocq_alias si_emp_valid_si_pure]
theorem uPredSiEmpValid_uPredSiPure {Pi : SiProp} : <si_emp_valid> (<si_pure> Pi : UPred M) ⊣⊢ Pi :=
  ⟨fun _ hp => hp, fun _ hp => hp⟩

@[rocq_alias si_pure_si_emp_valid]
theorem uPredSiPure_uPredSiEmpValid {P : UPred M} : <si_pure> <si_emp_valid> P ⊢ <pers> P :=
  fun n _ hp => P.mono hp CMRA.incN_unit n.le_refl

@[rocq_alias persistently_impl_si_pure]
theorem persistently_imp_uPredSiPure {Pi : SiProp} {Q : UPred M} :
    (<si_pure> Pi → <pers> Q) ⊢ <pers> (<si_pure> Pi → Q) := by
  intro n x hpq m y hinc hle hp
  have hq := hpq m (x.le hle) (CMRA.inc_refl x.val) hle hp
  exact (Q.mono hq hinc.incN m.le_refl)

-- si_pure_forall_2 is already in Sbi.lean
theorem uPredSiPure_forall_mpr {α : Type _} {Pi : α → SiProp} :
    (∀ x, <si_pure> Pi x : UPred M) ⊢ <si_pure> (∀ x, Pi x) := by
  rintro n x hp Ψ ⟨a, rfl⟩
  exact hp iprop(<si_pure> Pi a) ⟨a, rfl⟩

-- si_emp_valid_exist_1 is already in Sbi.lean
theorem uPredSiEmpValid_exist_mp {α : Type _} {P : α → UPred M} :
    (<si_emp_valid> (∃ x, P x) : SiProp) ⊢ ∃ x, <si_emp_valid> P x := by
  rintro n ⟨Ψ, ⟨a, rfl⟩, hp⟩
  exact ⟨iprop(<si_emp_valid> P a), ⟨a, rfl⟩, hp⟩

-- prop_ext_2 is already in SIProp.lean
theorem prop_ext_uPredSiEmpValid {P Q : UPred M} : <si_emp_valid> (P ∗-∗ Q) ⊢ SiProp.internalEq P Q := by
  intro _ hpq n x hn hv
  have hu : UCMRA.unit • x ≡{n}≡ x := UCMRA.unit_left_id.dist
  have hvu : ✓{n} UCMRA.unit • x := hu.validN.mpr hv
  constructor
  · exact fun hp => (uPred_ne hu).mp (hpq.1 n x hn hvu hp)
  · exact fun hq => (uPred_ne hu).mp (hpq.2 n x hn hvu hq)

end SiPropEmbedding

instance : Sbi (UPred M) where
  siPure_ne := uPredSiPure_ne
  siEmpValid_ne := uPredSiEmpValid_ne
  siPure_mono := uPredSiPure_mono
  siEmpValid_mono := uPredSiEmpValid_mono
  siEmpValid_siPure := uPredSiEmpValid_uPredSiPure
  siPure_siEmpValid := uPredSiPure_uPredSiEmpValid
  siPure_imp_mpr := uPredSiPure_imp_mpr
  siPure_sForall_mpr {_ _ _} H _ := H _ ⟨_, rfl⟩ _ _ .rfl (Nat.le_refl _)
  persistently_imp_siPure := persistently_imp_uPredSiPure
  siPure_later := uPredSiPure_later
  siPure_absorbing _ := ⟨fun _ _ ⟨_, _, _, _, h⟩ => h⟩
  siEmpValid_later_mp := uPredSiEmpValid_later_mp
  siEmpValid_affinely_mpr _ h := ⟨trivial, h⟩
  prop_ext_siEmpValid := prop_ext_uPredSiEmpValid

@[rocq_alias uPred_sbi_emp_valid_exist]
instance : SbiEmpValidExist (UPred M) where
  siEmpValid_sExists_1 Ψ n h := by
    obtain ⟨p, hΨ, hp⟩ := h
    exact ⟨_, ⟨p, rfl⟩, hΨ, hp⟩

/-- The Sbi-derived plainly on UPred unfolds to `UPred.plainly`. -/
theorem plainly_eq_uPred_plainly (P : UPred M) : iprop(■ P) = UPred.plainly P := rfl

/-- The Sbi-derived `internalCmraValid` on UPred unfolds to `UPred.cmraValid`. -/
theorem internalCmraValid_eq_uPred_cmraValid [CMRA A] (a : A) :
    (internalCmraValid a : UPred M) = UPred.cmraValid a := rfl

instance : BUpd (UPred M) := ⟨bupd⟩

instance : OFE.NonExpansive (BUpd.bupd (PROP := UPred M)) := bupd_ne

@[rocq_alias uPred_bi_bupd]
instance : BIUpdate (UPred M) where
  intro {P} _ x HP _ _ Hn H := ⟨_, ⟨H, P.mono HP (CMRA.incN_refl x.val) Hn⟩⟩
  mono Himp n x HP k yf Hn H := by
    rcases HP k yf Hn H with ⟨x', Hx1, Hx2⟩
    exact ⟨x', ⟨Hx1, Himp k ⟨x', CMRA.validN_op_left Hx1⟩ Hx2⟩⟩
  trans n x H k yf Hx Hyf :=
    let ⟨x', Hx', Hx''⟩ := H k yf Hx Hyf
    Hx'' k yf k.le_refl Hx'
  frame_r {P R} n x := fun ⟨x1, x2, Hx, HP, HR⟩ k yf Hk Hyf => by
    have L : ✓{k} x1 • (x2 • yf) :=
      (CMRA.op_assocN.trans (Hx.le Hk).op_l.symm).validN.2 Hyf
    let ⟨x', Hx'1, Hx'2⟩ := HP k (x2 • yf) Hk L
    refine ⟨x' • x2, CMRA.op_assocN.validN.1 Hx'1, x', x2, .rfl, Hx'2, ?_⟩
    exact R.mono HR (CMRA.incN_refl x2) Hk

@[rocq_alias uPred_primitive.bupd_si_pure]
theorem bupd_si_pure (Pi : SiProp) : (|==> <si_pure> Pi : UPred M) ⊢ <si_pure> Pi := by
  intro n x Hv
  have L : ✓{n} x.val • UCMRA.unit := CMRA.unit_right_id.symm.dist.validN.1 x.property
  let ⟨_, _, Hv'⟩ := Hv n UCMRA.unit n.le_refl L
  exact Hv'

@[rocq_alias uPred_bi_bupd_sbi]
instance : BIBUpdateSbi (UPred M) where
  bupd_si_pure := bupd_si_pure

instance : BIBUpdatePlainly (UPred M) where
  bupd_plainly {P} n x Hv := by
    have L : ✓{n} x.val • CMRA.unit := CMRA.unit_right_id.symm.dist.validN.1 x.property
    let ⟨x', _, Hx'⟩ := Hv n CMRA.unit n.le_refl L
    rw [plainly_eq_uPred_plainly] at Hx'
    exact P.mono Hx' CMRA.incN_unit n.le_refl

@[rocq_alias uPred_primitive.ownM_valid]
theorem ownM_valid (m : M) : ownM m ⊢ internalCmraValid m := fun _ h hp => hp.validN h.property

@[rocq_alias uPred_primitive.ownM_op]
theorem ownM_op (m1 m2 : M) : ownM (m1 • m2) ⊣⊢ ownM m1 ∗ ownM m2 := by
  constructor
  · intro n x ⟨z, Hz⟩
    refine ⟨m1, m2 • z, ?_, .rfl, CMRA.incN_op_left n m2 z⟩
    exact Hz.trans CMRA.assoc.symm.dist
  · intro n x ⟨y1, y2, H, ⟨w1, Hw1⟩, ⟨w2, Hw2⟩⟩
    exists w1 • w2
    calc
      x.val ≡{n}≡ y1 • y2 := H
      _     ≡{n}≡ (m1 • w1) • (m2 • w2) := Hw1.op Hw2
      _     ≡{n}≡ m1 • (w1 • (m2 • w2)) := CMRA.assoc.symm.dist
      _     ≡{n}≡ m1 • ((m2 • w2) • w1) := CMRA.comm.op_r.dist
      _     ≡{n}≡ m1 • (m2 • (w2 • w1)) := CMRA.assoc.symm.op_r.dist
      _     ≡{n}≡ (m1 • m2) • (w2 • w1) := CMRA.assoc.dist
      _     ≡{n}≡ (m1 • m2) • (w1 • w2) := CMRA.comm.op_r.dist

theorem ownM_eqv {m1 m2 : M} (H : m1 ≡ m2) : ownM m1 ⊣⊢ ownM m2 :=
  ⟨fun _ _ => (CMRA.incN_iff_left H.dist).mp, fun _ _ => (CMRA.incN_iff_left H.dist).mpr⟩

theorem ownM_always_invalid_elim (m : M) (H : ∀ n, ¬✓{n} m) : internalCmraValid m ⊢@{UPred M} False :=
  fun n _ => H n

@[rocq_alias uPred.ownM_unit]
theorem ownM_unit P : P ⊢ □ ownM (CMRA.unit : M) :=
  fun _ _ _ => ⟨trivial, CMRA.incN_unit⟩

@[rocq_alias uPred.persistently_ownM_core]
theorem persistently_ownM_core (a : M) : ownM a ⊢ <pers> ownM (CMRA.core a) :=
  fun _ _ => CMRA.core_incN_core

theorem intuitionistically_ownM_core (m : M) : ownM m ⊢ □ ownM (CMRA.core m) :=
  fun _ _ h => ⟨trivial, CMRA.core_incN_core h⟩

instance {a : M} : Persistent (ownM (CMRA.core a)) where
  persistent := by
    refine .trans (persistently_ownM_core _) ?_
    refine persistently_mono ?_
    refine equiv_iff.mp ?_ |>.mp
    refine OFE.NonExpansive.eqv ?_
    exact CMRA.core_idem a

@[rocq_alias uPred.bupd_ownM_updateP]
theorem bupd_ownM_updateP (x : M) (Φ : M → Prop) :
  (x ~~>: Φ) → ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ ownM y := by
  intro Hup n x2 ⟨x3, Hx⟩ k yf Hk Hyf
  have Hxv : ✓{k} x • (x3 • yf) := by
    refine CMRA.validN_ne ?_ Hyf
    exact (Hx.le Hk).op_l.trans CMRA.assoc.symm.dist
  rcases Hup k (some (x3 • yf)) Hxv with ⟨y, HΦy, Hyv⟩
  refine ⟨y • x3, CMRA.validN_ne CMRA.op_assocN Hyv, ?_⟩
  refine ⟨iprop(⌜Φ y⌝ ∧ ownM y), ?_, ?_⟩
  · exists y
  · exact ⟨HΦy, CMRA.incN_op_left k y x3⟩

@[rocq_alias uPred.ownM_forall]
theorem ownM_forall (f : A → M) :
  (∀ a, ownM (f a)) ⊢ ∃ z, ownM z ∧ (∀ a, ∃ xf, UPred.eq z (f a • xf)) := by
  intro n x Hf
  refine ⟨iprop(ownM x ∧ ∀ a, ∃ xf, UPred.eq x.val (f a • xf)), ⟨x, rfl⟩, ?_⟩
  refine ⟨CMRA.incN_refl x.val, ?_⟩
  rintro p ⟨a, rfl⟩
  rcases Hf (ownM (f a)) ⟨a, rfl⟩ with ⟨xf, Hxf⟩
  exact ⟨iprop(UPred.eq x.val (f a • xf)), ⟨xf, rfl⟩, Hxf⟩

@[rocq_alias uPred.later_ownM]
theorem later_ownM (a : M) : ▷ ownM a ⊢ ∃ b, ownM b ∧ ▷ <si_pure> (SiProp.internalEq a b)
  | 0, _, _ =>
    let Ψ := iprop(ownM UCMRA.unit ∧ ▷ <si_pure> (SiProp.internalEq a UCMRA.unit))
    ⟨Ψ, ⟨UCMRA.unit, rfl⟩, CMRA.incN_unit, trivial⟩
  | n+1, x, ⟨y, hx⟩ => by
    let ⟨a', y', hx', ha', hy'⟩ := CMRA.extend (CMRA.validN_succ x.property) hx
    let Ψ := iprop(ownM a' ∧ ▷ <si_pure> (SiProp.internalEq a a'))
    refine ⟨Ψ, ⟨a', rfl⟩, ?_, ?_⟩
    · exact (CMRA.incN_iff_right (OFE.equiv_dist.mp hx' (n + 1))).mpr (CMRA.incN_op_left (n + 1) a' y')
    · exact OFE.Dist.symm ha'

theorem pure_soundness : iprop(True ⊢ (⌜P⌝ : UPred M)) → P :=
  (· 0 ⟨CMRA.unit, CMRA.unit_validN⟩ ⟨⟩)

theorem later_soundness : iprop(True ⊢ ▷ P) → iprop((True : UPred M) ⊢ P) := by
  intro HP n x H
  exact UPred.mono _ (HP n.succ ⟨CMRA.unit, CMRA.unit_validN⟩ H) CMRA.incN_unit (Nat.le_refl _)

section derived

/-
## Ported from base_logic/derived.v
-/

@[rocq_alias uPred.intuitionistically_ownM]
theorem intuitionistically_ownM (a : M) [CMRA.CoreId a] : □ ownM a ⊣⊢ ownM a := by
  refine ⟨intuitionistically_elim, ?_⟩
  refine (intuitionistically_ownM_core a).trans ?_
  refine intuitionistically_mono ?_
  exact (ownM_eqv (CMRA.core_eqv_self a).symm).mpr

@[rocq_alias uPred.ownM_invalid]
theorem ownM_invalid (a : M) (hnv : ¬ ✓{0} a) : ownM a ⊢ False :=
  (ownM_valid a).trans (internalCmraValid_elim a) |>.trans (pure_mono hnv)

@[rocq_alias uPred.ownM_mono]
theorem ownM_mono {a b : M} (hinc : b ≼ a) : ownM a ⊢ ownM b :=
  fun n _ ha => CMRA.incN_trans (CMRA.incN_of_inc n hinc) ha

@[rocq_alias uPred.ownM_unit']
theorem ownM_unit' : ownM UCMRA.unit ⊣⊢@{UPred M} True :=
  ⟨fun _ _ _ => trivial, fun _ _ _ => CMRA.incN_unit⟩

@[rocq_alias uPred.bupd_ownM_update]
theorem bupd_ownM_update {x y : M} (hupd : x ~~> y) : ownM x ⊢ |==> ownM y := by
  refine (bupd_ownM_updateP x (y = ·) (UpdateP.of_update hupd)).trans ?_
  exact BIUpdate.mono (exists_elim fun z => pure_elim_l fun hyz => hyz ▸ .rfl)

@[rocq_alias uPred.ownM_timeless]
instance ownM_timeless (a : M) [OFE.DiscreteE a] : BI.Timeless (ownM a) where
  timeless
    | 0, _, _ => .inl trivial
    | n+1, x, ⟨_y, Hxy⟩ =>
      let ⟨_a', y', Hx, Ha', _⟩ := CMRA.extend (CMRA.validN_succ x.property) Hxy
      .inr ⟨y', (Hx.trans (OFE.DiscreteE.discrete (Ha'.symm.le n.zero_le)).symm.op_l).dist⟩

@[rocq_alias uPred.ownM_persistent]
instance ownM_persistent (a : M) [CMRA.CoreId a] : Persistent (ownM a) where
  persistent := by
    refine (persistently_ownM_core a).trans ?_
    exact persistently_mono (ownM_eqv (CMRA.core_eqv_self a)).mp

@[rocq_alias uPred.bupd_soundness]
theorem bupd_soundness {P : UPred M} [Plain P] : (⊢ |==> P) → ⊢ P :=
  fun h => h.trans bupd_elim

end derived

theorem plainly_valid_mpr [CMRA A] (a : A) :
    internalCmraValid a ⊢@{UPred M} ■ internalCmraValid a :=
  fun _ _ hv => hv

theorem persistently_valid_mpr [CMRA A] (a : A) :
    internalCmraValid a ⊢@{UPred M} <pers> internalCmraValid a :=
  (plainly_valid_mpr a).trans plainly_elim_persistently

theorem plainly_valid [CMRA A] (a : A) :
    ■ internalCmraValid a ⊣⊢@{UPred M} internalCmraValid a :=
  ⟨plainly_elim, plainly_valid_mpr a⟩

theorem intuitionistically_valid {A} [CMRA A] (a : A) :
    □ internalCmraValid a ⊣⊢@{UPred M} internalCmraValid a := by
  constructor
  · exact intuitionistically_elim
  · exact (persistently_valid_mpr a).trans intuitionistically_iff_persistently.mpr

theorem discrete_valid [CMRA A] [CMRA.Discrete A] (a : A) :
    internalCmraValid a ⊣⊢@{UPred M} ⌜✓ a⌝ :=
  ⟨fun n _ hv => (CMRA.valid_iff_validN' n).mpr hv, fun _ _ hv => hv.validN⟩

instance valid_timeless [CMRA A] [CMRA.Discrete A] {a : A} :
    Timeless (internalCmraValid a : UPred M) where
  timeless := by
    refine (later_mono (discrete_valid a).mp).trans ?_
    exact Timeless.timeless.trans (except0_mono (discrete_valid a).mpr)

instance valid_plain [CMRA A] {a : A} : Plain (internalCmraValid a : UPred M) where
  plain := plainly_valid_mpr a

instance valid_persistent [CMRA A] {a : A} : Persistent (internalCmraValid a : UPred M) where
  persistent := persistently_valid_mpr a

end UPred

section UPredAlt

open BUpdPlain CMRA UPred

/-
## Compatibility between the UPred model of BUpd and the BUpd construction for generic Sbi instances
-/

def BUpdPlain_pred [UCMRA M] (P : UPred M) (y : M) : UPred M where
  holds k _ := ∃ x'', ∃ H : ✓{k} (x'' • y), P k ⟨x'', CMRA.validN_op_left H⟩
  mono {_ _ _ _} := fun ⟨z, Hz1, Hz2⟩ _ Hn =>
    ⟨z, validN_of_le Hn Hz1, P.mono Hz2 (incN_refl z) Hn⟩

/-- The alternative definition entails the ordinary basic update -/
theorem BUpdPlain_bupd [UCMRA M] (P : UPred M) : BUpdPlain P ⊢ |==> P := by
  intro n ⟨x, Hx⟩ H k y Hkn Hxy
  have := (H _ ⟨BUpdPlain_pred P y, rfl⟩) k y Hkn Hxy ?_
  · rw [plainly_eq_uPred_plainly] at this
    exact this
  · intro _ z _ Hvyz HP
    rw [plainly_eq_uPred_plainly]
    refine ⟨z, validN_ne op_commN Hvyz, HP⟩

theorem BUpdPlain_bupd_iff [UCMRA M] (P : UPred M) : BUpdPlain P ⊣⊢ |==> P :=
  ⟨BUpdPlain_bupd P, BUpd_BUpdPlain (PROP := UPred M)⟩

theorem ownM_updateP [UCMRA M] {x : M} {R : UPred M} (Φ : M → Prop) (Hup : x ~~>: Φ) :
    ownM x ∗ (∀ y, iprop(⌜Φ y⌝) -∗ ownM y -∗ ■ R) ⊢ ■ R := by
  rw [plainly_eq_uPred_plainly]
  intro n z ⟨x1, z2, Hx, ⟨z1, Hz1⟩, HR⟩
  have Hvalid : ✓{n} (x •? some (z1 • z2)) := by
    show ✓{n} (x • (z1 • z2))
    refine CMRA.validN_ne ?_ z.property
    calc z.val ≡{n}≡ x1 • z2 := Hx
         _     ≡{n}≡ (x • z1) • z2 := Hz1.op_l
         _     ≡{n}≡ x • (z1 • z2) := CMRA.assoc.symm.dist
  have ⟨y, HΦy, Hvalid_y⟩ := Hup n (some (z1 • z2)) Hvalid
  have Hp := HR (iprop(⌜Φ y⌝ -∗ (UPred.ownM y -∗ UPred.plainly R))) ⟨y, rfl⟩
  exact Hp n z1 (Nat.le_refl _)
    (CMRA.validN_ne CMRA.comm.dist (CMRA.validN_op_right Hvalid)) HΦy n y (Nat.le_refl _)
    (CMRA.validN_ne (by
      calc y • (z1 • z2) ≡{n}≡ y • (z2 • z1) := CMRA.comm.dist.op_r
           _ ≡{n}≡ (z2 • z1) • y := CMRA.comm.symm.dist) Hvalid_y)
    (incN_refl y)

section UPredAlt
