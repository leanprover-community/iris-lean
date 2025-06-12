/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/

import Iris.Algebra.CMRA

namespace Iris

section excl

variable {α : Type u}

inductive Excl α where
  | excl : α → Excl α
  | exclInvalid : Excl α

open OFE

variable [OFE α]

/- COFE -/
@[simp] def Excl.equiv (x y : Excl α) : Prop := match x, y with
  | Excl.excl a, Excl.excl b => a ≡ b
  | Excl.exclInvalid, Excl.exclInvalid => True
  | _, _ => False

@[simp] def Excl.dist (n : Nat) : Excl α → Excl α → Prop
  | Excl.excl a, Excl.excl b => a ≡{n}≡ b
  | Excl.exclInvalid, Excl.exclInvalid => True
  | _, _ => False

theorem Excl.dist_equiv {n} : Equivalence (Excl.dist (α := α) n) where
  refl {x} := by
    cases x with
    | excl a => exact Dist.of_eq rfl
    | exclInvalid => trivial
  symm {x y} h := by
    cases x <;> cases y <;> try trivial
    exact Dist.symm h
  trans {x y z} h₁ h₂ := by
    cases x <;> cases y <;> cases z <;> try trivial
    exact Dist.trans h₁ h₂

instance : OFE (Excl α) where
  Equiv := Excl.equiv
  Dist := Excl.dist
  dist_eqv := Excl.dist_equiv
  equiv_dist {x y} := by
    constructor
    · intro h n
      cases x <;> cases y <;> simp at *
      exact Equiv.dist h
    · intro h
      cases x <;> cases y <;> simp at *
      exact equiv_dist.mpr h
  dist_lt {n x y m} hn hlt := by
    cases x <;> cases y <;> simp at *
    exact Dist.lt hn hlt

/- Adapted from the corresponding definitions for Option -/
@[simp] def Excl.getD (opt : Excl α) (dflt : α) : α :=
  match opt with
  | excl x => x
  | exclInvalid => dflt

@[simp] def Excl.map (f : α → β) : Excl α → Excl β
  | excl x => excl (f x)
  | exclInvalid   => exclInvalid

def exclChain (c : Chain (Excl α)) (x : α) : Chain α := by
  refine ⟨fun n => (c n).getD x, fun {n i} H => ?_⟩
  dsimp; have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist]

instance [IsCOFE α] : IsCOFE (Excl α) where
  compl c := (c 0).map fun x => IsCOFE.compl (exclChain c x)
  conv_compl {n} c := by
    have := c.cauchy (Nat.zero_le n); revert this
    rcases c.chain 0 with _|x' <;> rcases e : c.chain n with _|y' <;> simp [Dist]
    refine fun _ => OFE.dist_eqv.trans IsCOFE.conv_compl ?_
    simp [exclChain, e]

/- CMRA -/
instance : CMRA (Excl α) where
  pcore _ := none
  op _ _ := Excl.exclInvalid
  ValidN _ x := match x with
    | Excl.excl _ => True
    | Excl.exclInvalid => False
  Valid x := match x with
    | Excl.excl _ => True
    | Excl.exclInvalid => False

  op_ne := by exact { ne := fun ⦃n⦄ ⦃x₁ x₂⦄ a => trivial }
  pcore_ne := by simp
  validN_ne {n x y} h₁ h₂ := by cases x <;> cases y <;> trivial
  valid_iff_validN {x} := by
    constructor
    · intro h n; cases x <;> trivial
    · intro h; cases x <;> simp_all
  validN_succ {x n} h := by cases x <;> trivial

  assoc {x y z} := by simp
  comm {x y} := by simp
  pcore_op_left {x cx} := by simp
  pcore_idem {x cx} := by simp
  pcore_op_mono {x cx} := by simp
  validN_op_left {n x y} := by simp

  extend {n x y₁ y₂} h₁ h₂ := by cases x <;> trivial

/- Functors -/
abbrev ExclOF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => Excl (F A B)

theorem exclO_map_nonexpansive {α β} [OFE α] [OFE β] (f : α -n> β) : NonExpansive (Excl.map f) := ⟨by
  intro n x₁ x₂ h
  cases x₁ <;> cases x₂ <;> try trivial
  have ⟨hne⟩ := f.ne
  exact hne h
⟩

def exclO_map {α β} [OFE α] [OFE β] (f : α -n> β) : Excl α -C> Excl β :=
  ⟨⟨Excl.map f, exclO_map_nonexpansive f⟩,
  by intro n x h; cases x <;> trivial,
  by intro x; trivial,
  by intro x y; trivial⟩

instance [COFE.OFunctor F] : RFunctor (fun A B _ _ => Excl (F A B)) where
  cmra := inferInstance
  map f g := exclO_map (COFE.OFunctor.map f g)
  map_ne.ne := by
    intros n f₁ f₂ hf g₁ g₂ hg x
    cases x with
    | excl a =>
      apply COFE.OFunctor.map_ne.ne
      exact hf
      exact hg
    | exclInvalid => trivial
  map_id {_ _} _ _ x := by
    cases x
    · apply COFE.OFunctor.map_id
    · trivial
  map_comp f g f' g' x := by
    cases x
    · apply COFE.OFunctor.map_comp
    · trivial

instance [COFE.OFunctorContractive F] : RFunctorContractive (ExclOF F) where
  map_contractive.1 {n x y} HKL z := by
    rewrite [RFunctor.map]
    cases z
    · apply COFE.OFunctorContractive.map_contractive.1
      exact HKL
    · trivial
