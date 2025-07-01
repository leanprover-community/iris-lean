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
    · rintro a ha; exists a
    · rintro b hb; exists b
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
  rintro n; simp_all only [dist, op, List.mem_append]
  constructor <;> exact fun _ ha => ⟨_, ha.symm, .rfl⟩

theorem Agree.op_commN {x y : Agree α} :  x.op y ≡{n}≡ y.op x := op_comm n

theorem Agree.op_assoc {x y z : Agree α} :  x.op (y.op z) ≡ (x.op y).op z := by
  rintro n; simp_all only [dist, op, List.mem_append, List.append_assoc]
  constructor <;> (intro a ha; exists a)

theorem Agree.idemp {x : Agree α} : x.op x ≡ x := by
  rintro n; constructor <;> (intro a ha; exists a; simp_all [op])

theorem Agree.validN_ne {x y : Agree α} : x ≡{n}≡ y → x.validN n → y.validN n := by
  simp only [OFE.Dist, dist, validN_def, and_imp]
  intro h₁ h₂ hn a ha b hb
  have ⟨a', ha', ha'a⟩ := h₂ _ ha
  have ⟨b', hb', hb'b⟩ := h₂ _ hb
  have ha'b' := hn _ ha' _ hb'
  exact ha'a.symm.trans (ha'b'.trans hb'b)

theorem Agree.op_ne {x : Agree α} : OFE.NonExpansive x.op := by
  constructor; simp only [OFE.Dist, dist, op, List.mem_append, and_imp]
  intro n y₁ y₂ heq₁ heq₂; constructor
  -- This would probably be dealt with by aesop easily
  · rintro a (hx | hy)
    · exists a; simp [hx]
    · obtain ⟨b, hb, heq⟩ := heq₁ _ hy
      exists b; simp_all
  · rintro a (hx | hy)
    · exists a; simp [hx]
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

instance Agree_CMRA : CMRA (Agree α) where
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
  pcore_op_mono := by simp only [Option.some.injEq]; rintro x _ rfl y; exists y
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

theorem Agree.toAgree.is_discrete {a : α} (Ha : OFE.DiscreteE a) : OFE.DiscreteE (toAgree a) := by
  simp [toAgree]
  intro y Ha _
  cases y
  rcases Ha with ⟨Hal, Har⟩
  constructor <;> simp_all
  · rcases Hal with ⟨b, Hb1, Hb2⟩
    refine ⟨b, ⟨Hb1, ?_⟩⟩
    exact OFE.Equiv.dist (Ha (Har b Hb1))
  · intro H Hb
    exact OFE.Equiv.dist (Ha (Har H Hb))

open OFE OFE.Discrete in
instance [OFE α] [OFE.Discrete α] : OFE.Discrete (Agree α) where
  discrete_0 {x y} H := by
    intro n
    constructor
    · intro a Ha
      rcases H.1 a Ha with ⟨c, Hc⟩
      refine ⟨c, ⟨Hc.1, ?_⟩⟩
      apply equiv_dist.mp <| discrete_0 (Dist.le Hc.2 <| Nat.zero_le 0)
    · intro b Hb
      rcases H.2 b Hb with ⟨c, Hc⟩
      refine ⟨c, ⟨Hc.1, ?_⟩⟩
      apply equiv_dist.mp <| discrete_0 (Dist.le Hc.2 <| Nat.zero_le 0)

instance toAgree.ne [OFE α] : OFE.NonExpansive (toAgree : α → Agree α) where
  ne n x y H := by
    simp [toAgree]
    constructor
    · intro a Ha; exists y
      simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
      simp only [List.mem_cons, List.not_mem_nil, or_false, true_and]
      exact Ha ▸ H
    · intro b Hb; exists x
      simp only [List.mem_cons, List.not_mem_nil, or_false] at Hb
      simp only [List.mem_cons, List.not_mem_nil, or_false, true_and]
      exact Hb ▸ H

theorem toAgree.inj {a1 a2 : α} {n} (H : toAgree a1 ≡{n}≡ toAgree a2) : a1 ≡{n}≡ a2 := by
  rcases H.1 a1 (by simp [toAgree]) with ⟨_, ⟨_, _⟩⟩; simp_all [toAgree]

instance : CMRA.IsTotal (Agree α) where
  total := by simp [CMRA.pcore]

theorem agree_valid_includedN {n} {x y : Agree α} : x ≼{n} y → ✓{n} y → x ≡{n}≡ y := by
  rintro ⟨z, Hy⟩ H
  have H' : ✓{n} (x • z) := (OFE.Dist.validN Hy).mp H
  refine .trans ?_ Hy.symm
  have H'' := Agree.op_invN H'
  refine H''.trans ?_
  refine .trans ?_ CMRA.op_commN
  refine .trans ?_ (CMRA.op_ne.ne H''.symm)
  exact Agree.idemp.symm _

theorem toAgree.incN {a b : α} {n} : toAgree a ≼{n} toAgree b ↔ a ≡{n}≡ b := by
  refine ⟨?_, fun H => (CMRA.incN_iff_right <| toAgree.ne.ne H).mp <| CMRA.incN_refl _⟩
  intro H
  apply toAgree.inj
  exact agree_valid_includedN H trivial
