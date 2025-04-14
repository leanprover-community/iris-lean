/-
Copyright (c) 2025 Leo Stefanesco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Stefanesco
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

namespace Iris

section agree

variable {α : Type u}

variable (α) in
@[ext]
structure Agree where
  car : List α
  not_nil : car ≠ []

def toAgree (a : α) : Agree α := ⟨[a], by simp⟩

theorem mem_of_agree (x : Agree α) : ∃ a, a ∈ x.car := by
  rcases x with ⟨as, h⟩
  rcases as
  · contradiction
  · simp_all

variable [OFE α]

def Agree.dist (n : Nat) (x y : Agree α) : Prop :=
  (∀ a ∈ x.car, ∃ b ∈ y.car, a ≡{n}≡ b) ∧
  (∀ b ∈ y.car, ∃ a ∈ x.car, a ≡{n}≡ b)

theorem Agree.dist_equiv : Equivalence (dist (α := α) n) where
  refl := by
    rintro ⟨x, h⟩; constructor
    · rintro a ha; exists a; simp_all [OFE.dist_eqv.refl]
    · rintro b hb; exists b; simp_all [OFE.dist_eqv.refl]
  symm := by
    rintro  _ _ ⟨h₁, h₂⟩
    simp only [dist] at h₁ h₂ ⊢
    constructor
    · rintro a ha
      obtain ⟨b, hb, hd⟩ := h₂ a ha
      exact ⟨b, hb, hd.symm⟩
    · rintro b hb
      obtain ⟨a, ha, hd⟩ := h₁ b hb
      exact ⟨a, ha, hd.symm⟩
  trans := by
    rintro _ _ _ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    constructor
    · rintro a ha
      obtain ⟨b, hb, hd₁⟩ := h₁ a ha
      obtain ⟨c, hc, hd₂⟩ := h₂ b hb
      exact ⟨c, hc,  hd₁.trans hd₂⟩
    · rintro c hc
      obtain ⟨b, hb, hd₁⟩ := h₂' c hc
      obtain ⟨a, ha, hd₂⟩ := h₁' b hb
      exact ⟨a, ha,  hd₂.trans hd₁⟩

instance : OFE (Agree α) where
  Equiv x y := ∀ n, Agree.dist n x y
  Dist := Agree.dist
  dist_eqv := Agree.dist_equiv
  equiv_dist := by simp
  dist_lt {n x y m} hn hlt := by
    rcases hn with ⟨h₁, h₂⟩; constructor
    · rintro a ha
      obtain ⟨b, hb, hd⟩ := h₁ a ha
      exact ⟨b, hb, OFE.Dist.lt hd hlt⟩
    · rintro b hb
      obtain ⟨a, ha, hd⟩ := h₂ b hb
      exact ⟨a, ha, OFE.Dist.lt hd hlt⟩


def Agree.validN (n : Nat) (x : Agree α) : Prop :=
  match x.car with
  | [_] => True
  | _ => ∀ a ∈ x.car, ∀ b ∈ x.car, a ≡{n}≡ b

theorem Agree.validN_def {x : Agree α} :
    x.validN n ↔ ∀ a ∈ x.car, ∀ b ∈ x.car, a ≡{n}≡ b := by
  rcases x with ⟨⟨⟩ | ⟨a, ⟨⟩| _⟩, _⟩ <;> simp_all [validN, OFE.Dist.rfl]

def Agree.valid (x : Agree α) : Prop := ∀ n, x.validN n

def Agree.op (x y : Agree α) : Agree α :=
  ⟨x.car ++ y.car, by apply List.append_ne_nil_of_left_ne_nil; exact x.not_nil⟩

theorem Agree.op_comm {x y : Agree α} :  x.op y ≡ y.op x := by
  rintro n; simp_all only [dist, op, List.mem_append]; constructor <;>
    (rintro a ha; exists a; simp_all [OFE.Dist.rfl, Or.symm])

theorem Agree.op_commN {x y : Agree α} :  x.op y ≡{n}≡ y.op x := op_comm n

theorem Agree.op_assoc {x y z : Agree α} :  x.op (y.op z) ≡ (x.op y).op z := by
  rintro n; simp_all only [dist, op, List.mem_append, List.append_assoc]; constructor <;>
    (rintro a ha; exists a; simp_all [OFE.Dist.rfl, Or.symm])

theorem Agree.idemp {x : Agree α} : x.op x ≡ x := by
  rintro n; constructor <;> (rintro a ha; exists a; simp_all [op, OFE.Dist.rfl])

theorem Agree.validN_ne {x y : Agree α} : x ≡{n}≡ y → x.validN n → y.validN n := by
  simp only [OFE.Dist, dist, validN_def, and_imp]
  intro h₁ h₂ hn a ha b hb
  obtain ⟨a', ha', ha'a⟩ := h₂ _ ha
  obtain ⟨b', hb', hb'b⟩ := h₂ _ hb
  have ha'b' := hn _ ha' _ hb'
  exact (ha'a.symm.trans (ha'b'.trans hb'b))

theorem Agree.op_ne {x : Agree α} : OFE.NonExpansive x.op := by
  constructor; simp only [OFE.Dist, dist, op, List.mem_append, and_imp]
  intro n y₁ y₂ heq₁ heq₂; constructor
  -- This would probably be dealt with by aesop easily
  · rintro a (hx | hy)
    · exists a; simp [OFE.Dist.rfl, hx]
    · obtain ⟨b, hb, heq⟩ := heq₁ _ hy
      exists b; simp_all
  · rintro a (hx | hy)
    · exists a; simp [OFE.Dist.rfl, hx]
    · obtain ⟨b, hb, heq⟩ := heq₂ _ hy
      exists b; simp_all

theorem Agree.op_ne₂ : OFE.NonExpansive₂ (Agree.op (α := α)) := by
  constructor
  intro n x₁ x₂ hx y₁ y₂ hy
  exact op_ne.ne hy |>.trans (op_comm n) |>.trans (op_ne.ne hx) |>.trans (op_comm n)

theorem Agree.op_invN {x y : Agree α} : (x.op y).validN n → x ≡{n}≡ y := by
  simp only [op, validN_def, List.mem_append, OFE.Dist, dist]
  intro h; constructor
  · intro a ha
    obtain ⟨b, hb⟩ := mem_of_agree y
    exists b; simp_all
  · intro a ha
    obtain ⟨b, hb⟩ := mem_of_agree x
    exists b; simp_all

instance : CMRA (Agree α) where
  pcore := some
  op := Agree.op
  ValidN := Agree.validN
  Valid := Agree.valid

  op_ne := Agree.op_ne
  pcore_ne := by simp
  validN_ne := Agree.validN_ne

  valid_iff_validN := by rfl
  validN_succ := by
    simp [Agree.validN_def]; intro x n hsuc a ha b hb
    exact (OFE.dist_lt (hsuc a ha b hb) (by omega))

  assoc := Agree.op_assoc
  comm := Agree.op_comm
  pcore_op_left := by simp [Agree.idemp]
  pcore_idem := by simp [OFE.Equiv.rfl]
  pcore_op_mono := by
    simp only [Option.some.injEq]
    rintro x _ y rfl
    exists y
    apply OFE.Equiv.rfl
  validN_op_left := by
    intro n x y
    simp only [Agree.op, Agree.validN_def, List.mem_append]
    intro h a ha b hb
    exact h _ (.inl ha) _ (.inl hb)

  extend := by
    intro n x y₁ y₂ hval heq₁
    exists x, x
    have heq₂ := Agree.op_invN (Agree.validN_ne heq₁ hval)
    have heq₃ : y₁.op y₂ ≡{n}≡ y₁ := Agree.op_ne.ne heq₂.symm |>.trans (Agree.idemp n)
    exact ⟨Agree.idemp.symm, heq₁.trans heq₃, heq₁.trans heq₃ |>.trans heq₂⟩

theorem Agree.includedN {x y : Agree α} : x ≼{n} y ↔ y ≡{n}≡ y • x := by
  refine ⟨fun ⟨z, h⟩ => ?_, fun h => ⟨y, h.trans op_commN⟩⟩
  have hid := idemp (x := x) |>.symm
  exact h.trans <| op_commN.trans <|
    (op_ne.ne (hid n)).trans <|
    .trans (op_assoc n) <|
    op_commN.trans <|
    (op_ne.ne (h.trans op_commN).symm).trans <|
    op_commN

theorem Agree.included {x y : Agree α} : x ≼ y ↔ y ≡ y • x :=
  ⟨fun ⟨z, h⟩ n => includedN.mp ⟨z, h n⟩, fun h => ⟨y, h.trans op_comm⟩⟩
