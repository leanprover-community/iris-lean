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

attribute [simp] Agree.not_nil

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
  refl := fun ⟨x, h⟩ => by
    constructor
    · intro a ha; exists a
    · intro b hb; exists b
  symm := fun ⟨h₁, h₂⟩ => by
    constructor
    · intro a ha
      obtain ⟨b, hb, hd⟩ := h₂ a ha
      exact ⟨b, hb, hd.symm⟩
    · intro b hb
      obtain ⟨a, ha, hd⟩ := h₁ b hb
      exact ⟨a, ha, hd.symm⟩
  trans := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ => by
    constructor
    · intro a ha
      obtain ⟨b, hb, hd₁⟩ := h₁ a ha
      obtain ⟨c, hc, hd₂⟩ := h₂ b hb
      exact ⟨c, hc,  hd₁.trans hd₂⟩
    · intro c hc
      obtain ⟨b, hb, hd₁⟩ := h₂' c hc
      obtain ⟨a, ha, hd₂⟩ := h₁' b hb
      exact ⟨a, ha,  hd₂.trans hd₁⟩

instance : OFE (Agree α) where
  Equiv x y := ∀ n, Agree.dist n x y
  Dist := Agree.dist
  dist_eqv := Agree.dist_equiv
  equiv_dist := by simp
  dist_lt {n x y m} := fun ⟨h₁, h₂⟩ hlt => by
    constructor
    · intro a ha
      obtain ⟨b, hb, hd⟩ := h₁ a ha
      exact ⟨b, hb, OFE.Dist.lt hd hlt⟩
    · intro b hb
      obtain ⟨a, ha, hd⟩ := h₂ b hb
      exact ⟨a, ha, OFE.Dist.lt hd hlt⟩

theorem Agree.equiv_def {x y : Agree α} : x ≡ y ↔ ∀ n, Agree.dist n x y := .rfl
theorem Agree.dist_def {x y : Agree α} : x ≡{n}≡ y ↔ Agree.dist n x y := .rfl

def Agree.validN (n : Nat) (x : Agree α) : Prop :=
  match x.car with
  | [_] => True
  | _ => ∀ a ∈ x.car, ∀ b ∈ x.car, a ≡{n}≡ b

theorem Agree.validN_iff {x : Agree α} :
    x.validN n ↔ ∀ a ∈ x.car, ∀ b ∈ x.car, a ≡{n}≡ b := by
  rcases x with ⟨⟨⟩ | ⟨a, ⟨⟩| _⟩, _⟩ <;> simp_all [validN, OFE.Dist.rfl]

def Agree.valid (x : Agree α) : Prop := ∀ n, x.validN n

def Agree.op (x y : Agree α) : Agree α :=
  ⟨x.car ++ y.car, by apply List.append_ne_nil_of_left_ne_nil; exact x.not_nil⟩

theorem Agree.op_comm {x y : Agree α} :  x.op y ≡ y.op x := by
  intro n; simp_all only [dist, op, List.mem_append]
  constructor <;> exact fun _ ha => ⟨_, ha.symm, .rfl⟩

theorem Agree.op_commN {x y : Agree α} :  x.op y ≡{n}≡ y.op x := op_comm n

theorem Agree.op_assoc {x y z : Agree α} :  x.op (y.op z) ≡ (x.op y).op z := by
  intro n; simp_all only [dist, op, List.mem_append, List.append_assoc]
  constructor <;> (intro a ha; exists a)

theorem Agree.idemp {x : Agree α} : x.op x ≡ x := by
  intro n; constructor <;> (intro a ha; exists a; simp_all [op])

theorem Agree.validN_ne {x y : Agree α} : x ≡{n}≡ y → x.validN n → y.validN n := by
  simp only [OFE.Dist, dist, validN_iff, and_imp]
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
  simp only [op, validN_iff, List.mem_append, OFE.Dist, dist]
  intro h; constructor
  · intro a ha
    obtain ⟨b, hb⟩ := mem_of_agree y
    exists b; simp_all
  · intro a ha
    obtain ⟨b, hb⟩ := mem_of_agree x
    exists b; simp_all

theorem Agree.op_inv {x y : Agree α} : (x.op y).valid → x ≡ y := by
  simp [valid, equiv_def]
  intro h n
  exact op_invN (h n)

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
    simp [Agree.validN_iff]; intro x n hsuc a ha b hb
    exact (OFE.dist_lt (hsuc a ha b hb) (by omega))

  assoc := Agree.op_assoc
  comm := Agree.op_comm
  pcore_op_left := by simp [Agree.idemp]
  pcore_idem := by simp [OFE.Equiv.rfl]
  pcore_op_mono := by simp only [Option.some.injEq]; rintro x _ rfl y; exists y
  validN_op_left := by
    intro n x y
    simp only [Agree.op, Agree.validN_iff, List.mem_append]
    exact fun h a ha b hb => h _ (.inl ha) _ (.inl hb)
  extend := by
    intro n x y₁ y₂ hval heq₁
    have heq₂ := Agree.op_invN (Agree.validN_ne heq₁ hval)
    have heq₃ : y₁.op y₂ ≡{n}≡ y₁ := Agree.op_ne.ne heq₂.symm |>.trans (Agree.idemp n)
    exact ⟨x, x, Agree.idemp.symm, heq₁.trans heq₃, heq₁.trans heq₃ |>.trans heq₂⟩

theorem Agree.op_def {x y : Agree α} : x • y = x.op y := rfl
theorem Agree.validN_def {x : Agree α} : ✓{n} x ↔ x.validN n := .rfl
theorem Agree.valid_def {x : Agree α} : ✓ x ↔ x.valid := .rfl

instance : CMRA.IsTotal (Agree α) where
  total x := ⟨x, rfl⟩

instance [OFE.Discrete α] : CMRA.Discrete (Agree α) where
  discrete_0 := by
    intro x y ⟨h₁, h₂⟩ n
    constructor <;> intro a ha
    · obtain ⟨b, hb, heq⟩ := h₁ a ha
      exists b; simp_all [OFE.Discrete.discrete_n]
    · obtain ⟨b, hb, heq⟩ := h₂ a ha
      exists b; simp_all [OFE.Discrete.discrete_n]
  discrete_valid {x} hval n := by
    rw [Agree.validN_def] at hval
    rw [Agree.validN_iff] at hval ⊢
    exact fun a ha b hb => OFE.discrete_n (hval a ha b hb)

instance : OFE.NonExpansive (@toAgree α) where
  ne n x₁ x₂ heq := by constructor <;> simp_all [toAgree]

theorem Agree.toAgree_injN {a b : α} : toAgree a ≡{n}≡ toAgree b → a ≡{n}≡ b := by
  intro ⟨h₁, h₂⟩; simp_all [toAgree]

theorem Agree.toAgree_inj {a b : α} : toAgree a ≡ toAgree b → a ≡ b := by
  simp only [OFE.equiv_dist]
  exact fun heq n => toAgree_injN (heq n)

theorem Agree.toAgree_uninjN {x : Agree α} : ✓{n} x → ∃ a, toAgree a ≡{n}≡ x := by
  rw [validN_def, validN_iff]
  obtain ⟨a, ha⟩ := mem_of_agree x
  intro h; exists a
  constructor <;> intros
  · exists a; simp_all [toAgree]
  · simp_all [toAgree]

theorem Agree.toAgree_uninj {x : Agree α} : ✓ x → ∃ a, toAgree a ≡ x := by
  simp only [valid_def, valid, validN_iff, equiv_def]
  obtain ⟨a, ha⟩ := mem_of_agree x
  intro h; exists a; intro n
  constructor <;> intros
  · exists a; simp_all [toAgree]
  · simp_all [toAgree]

theorem Agree.includedN {x y : Agree α} : x ≼{n} y ↔ y ≡{n}≡ y • x := by
  refine ⟨fun ⟨z, h⟩ => ?_, fun h => ⟨y, h.trans op_commN⟩⟩
  have hid := idemp (x := x) |>.symm
  calc
    y ≡{n}≡ x • z := h
    _ ≡{n}≡ (x • x) • z := .op_l (hid n)
    _ ≡{n}≡ x • (x • z) := CMRA.op_assocN.symm
    _ ≡{n}≡ x • y := h.symm.op_r
    _ ≡{n}≡ y • x := op_commN

theorem Agree.included {x y : Agree α} : x ≼ y ↔ y ≡ y • x :=
  ⟨fun ⟨z, h⟩ n => includedN.mp ⟨z, h n⟩, fun h => ⟨y, h.trans op_comm⟩⟩

theorem Agree.toAgree.is_discrete {a : α} (Ha : OFE.DiscreteE a) : OFE.DiscreteE (toAgree a) := by
  simp [toAgree]
  constructor
  intro y Ha _
  cases y
  rcases Ha with ⟨Hal, Har⟩
  constructor <;> simp_all
  · rcases Hal with ⟨b, Hb1, Hb2⟩
    refine ⟨b, ⟨Hb1, ?_⟩⟩
    exact OFE.Equiv.dist (Ha.discrete (Har b Hb1))
  · intro H Hb
    exact OFE.Equiv.dist (Ha.discrete (Har H Hb))

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

theorem Agree.valid_includedN {x y : Agree α} : ✓{n} y → x ≼{n} y → x ≡{n}≡ y := by
  intro hval ⟨z, heq⟩
  have : ✓{n} (x • z) := heq.validN.mp hval
  calc
    x ≡{n}≡ x • x := .symm (idemp _)
    _ ≡{n}≡ x • z := (op_invN this).op_r
    _ ≡{n}≡ y := heq.symm

theorem Agree.valid_included {x y : Agree α} : ✓ y → x ≼ y → x ≡ y := by
  intro hval ⟨z, heq⟩
  have heq' : x ≡ z := op_inv <| (CMRA.valid_iff heq).mp hval
  calc
    x ≡ x • x := idemp.symm
    _ ≡ x • z := .op_r heq'
    _ ≡ y := heq.symm

@[simp]
theorem Agree.toAgree_includedN {a b : α} : toAgree a ≼{n} toAgree b ↔ a ≡{n}≡ b := by
  constructor <;> intro h
  · exact toAgree_injN (valid_includedN trivial h)
  · exists toAgree a
    calc
      toAgree b ≡{n}≡ toAgree a := OFE.NonExpansive.ne h.symm
      _         ≡{n}≡ toAgree a • toAgree a := .symm (idemp n)

@[simp]
theorem Agree.toAgree_included {a b : α} : toAgree a ≼ toAgree b ↔ a ≡ b := by
  constructor <;> intro h
  · exact toAgree_inj (valid_included (fun _ => trivial) h)
  · exists toAgree a
    calc
      toAgree b ≡ toAgree a := OFE.NonExpansive.eqv (OFE.Equiv.symm h)
      _         ≡ toAgree a • toAgree a := .symm (CMRA.pcore_op_left rfl)

@[simp]
theorem Agree.toAgree_included_L [OFE.Leibniz α] {a b : α} :
    toAgree a ≼ toAgree b ↔ a = b := by simp

instance {x : Agree α} : CMRA.Cancelable x where
  cancelableN {n y z} hval heq := by
    obtain ⟨a, ha⟩ := Agree.toAgree_uninjN (CMRA.validN_op_left hval)
    obtain ⟨b, hb⟩ := Agree.toAgree_uninjN (CMRA.validN_op_right hval)
    have hval' : ✓{n} x • z := (OFE.Dist.validN heq).mp hval
    have : ✓{n} z := CMRA.validN_op_right hval'
    obtain ⟨c, hc⟩ := Agree.toAgree_uninjN this
    have heq₁ : a ≡{n}≡ b := Agree.toAgree_injN <| calc
      toAgree a ≡{n}≡ x         := ha
      _         ≡{n}≡ y         := Agree.op_invN hval
      _         ≡{n}≡ toAgree b := hb.symm
    have heq₂ : a ≡{n}≡ c := Agree.toAgree_injN <| calc
      toAgree a ≡{n}≡ x         := ha
      _         ≡{n}≡ z         := Agree.op_invN hval'
      _         ≡{n}≡ toAgree c := hc.symm
    have heq₃ : b ≡{n}≡ c := heq₁.symm.trans heq₂
    calc
      y ≡{n}≡ toAgree b := hb.symm
      _ ≡{n}≡ toAgree c := OFE.NonExpansive.ne heq₃
      _ ≡{n}≡ z := hc

theorem Agree.toAgree_op_validN_iff_dist {a b : α} :
    ✓{n} (toAgree a • toAgree b) ↔ a ≡{n}≡ b := by
  constructor <;> intro h
  · exact toAgree_injN (op_invN h)
  · have : toAgree a ≡{n}≡ toAgree b := OFE.NonExpansive.ne h
    have : toAgree a • toAgree b ≡{n}≡ toAgree a := calc
      toAgree a • toAgree b ≡{n}≡ toAgree a • toAgree a := this.symm.op_r
      _ ≡{n}≡ toAgree a := idemp n
    exact this.symm.validN.mp trivial

theorem Agree.toAgree_op_valid_iff_equiv {a : α} : ✓ (toAgree a • toAgree b) ↔ a ≡ b := by
  simp [OFE.equiv_dist, CMRA.valid_iff_validN, toAgree_op_validN_iff_dist]

theorem toAgree_op_valid_iff_eq [OFE.Leibniz α] {a : α} :
    ✓ (toAgree a • toAgree b) ↔ a = b := by simp_all [Agree.toAgree_op_valid_iff_equiv]

end agree

def Agree.map' {α β} (f : α → β) (a : Agree α) : Agree β := ⟨a.car.map f, by simp⟩

section agree_map

variable {α β} [OFE α] [OFE β] {f : α → β} [hne : OFE.NonExpansive f]

local instance : OFE.NonExpansive (Agree.map' f) where
  ne := by
    intro n x₁ x₂ h
    simp only [Agree.map', Agree.dist_def, Agree.dist, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]  at h ⊢
    constructor
    · intro a ha
      obtain ⟨b, hb, heq⟩ := h.1 a ha
      exact ⟨f b, ⟨b, hb, rfl⟩, OFE.NonExpansive.ne heq⟩
    · intro a ha
      obtain ⟨b, hb, heq⟩ := h.2 a ha
      exact ⟨f b, ⟨b, hb, rfl⟩, OFE.NonExpansive.ne heq⟩

variable (f) in
def Agree.map : CMRA.Hom (Agree α) (Agree β) where
  f := map' f
  ne := inferInstance
  validN {n x} hval := by
    simp [validN_def, map', validN_iff] at hval ⊢
    intro a ha b hb
    exact OFE.NonExpansive.ne (hval a ha b hb)
  pcore x := .rfl
  op x y n := by
    simp only [dist, map', op_def, op, List.map_append, List.mem_append, List.mem_map]
    constructor <;>
    · intro a ha
      obtain ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ := ha
      · exact ⟨f b, .inl ⟨_, hb, rfl⟩, .rfl⟩
      · exact ⟨f b, .inr ⟨_, hb, rfl⟩, .rfl⟩

theorem Agree.agree_map_ext {g : α → β} [OFE.NonExpansive g] (heq : ∀ a, f a ≡ g a) :
    map f x ≡ map g x := by
  intro n
  simp only [dist, map, map', List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor <;> intro a ha
  · exact ⟨g a, ⟨a, ha, rfl⟩, (heq a).dist⟩
  · exact ⟨f a, ⟨a, ha, rfl⟩, (heq a).dist⟩

end agree_map
