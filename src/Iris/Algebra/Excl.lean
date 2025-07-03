/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Mario Carneiro
-/

import Iris.Algebra.CMRA

namespace Iris

section excl

inductive Excl α where
  | excl : α → Excl α
  | invalid : Excl α

open Excl OFE

/-! ## COFE -/
@[simp] protected def Excl.Equiv [OFE α] : Excl α → Excl α → Prop
  | excl a, excl b => a ≡ b
  | invalid, invalid => True
  | _, _ => False

@[simp] protected def Excl.Dist [OFE α] (n : Nat) : Excl α → Excl α → Prop
  | excl a, excl b => a ≡{n}≡ b
  | invalid, invalid => True
  | _, _ => False

theorem Excl.dist_eqv [OFE α] {n} : Equivalence (Excl.Dist (α := α) n) where
  refl {x} := by
    cases x with
    | excl a => exact Dist.of_eq rfl
    | invalid => trivial
  symm {x y} h := by
    cases x <;> cases y <;> try trivial
    exact Dist.symm h
  trans {x y z} h₁ h₂ := by
    cases x <;> cases y <;> cases z <;> try trivial
    exact Dist.trans h₁ h₂

instance [OFE α] : OFE (Excl α) where
  Equiv := Excl.Equiv
  Dist := Excl.Dist
  dist_eqv := dist_eqv
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

instance [OFE α] : NonExpansive excl (α := α) where
  ne _ _ _ a := a

instance [OFE α] [Discrete α] : Discrete (Excl α) where
  discrete_0 {x y} h' := by
    cases x <;> cases y <;> try exact h'
    exact discrete_0 (α := α) h'

instance [OFE α] [Leibniz α] : Leibniz (Excl α) where
  eq_of_eqv {x y} h' := by
    cases x <;> cases y <;> try trivial
    exact congrArg excl (eq_of_eqv h')

instance [OFE α] {a : α} [h : DiscreteE a] : DiscreteE (excl a) where
  discrete {x} h' := by
    cases x
    · exact h.discrete h'
    · exact h'

instance [OFE α] : DiscreteE (@invalid α) where
  discrete {x} h := by cases x <;> exact h

/- Adapted from the corresponding definitions for [Option]. -/
/- This could be simplified if there was an isomorphism lemma for [COFE]s in [OFE.lean]. -/
@[simp] def Excl.getD (x : Excl α) (dflt : α) : α :=
  match x with
  | excl a => a
  | invalid => dflt

@[simp] def Excl.map (f : α → β) : Excl α → Excl β
  | excl a => excl (f a)
  | invalid => invalid

def exclChain [OFE α] (c : Chain (Excl α)) (a : α) : Chain α := by
  refine ⟨fun n => (c n).getD a, fun {n i} H => ?_⟩
  dsimp; have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist]

instance [OFE α] [IsCOFE α] : IsCOFE (Excl α) where
  compl c := (c 0).map fun x => IsCOFE.compl (exclChain c x)
  conv_compl {n} c := by
    have := c.cauchy (Nat.zero_le n); revert this
    obtain _|x' := c.chain 0 <;> rcases e : c.chain n with _|y' <;> simp [Dist]
    refine fun _ => dist_eqv.trans IsCOFE.conv_compl ?_
    simp [exclChain, e]

/-! ## CMRA -/
@[simp] def Excl.Valid : Excl α → Prop
  | excl _ => True
  | invalid => False

instance [OFE α] : CMRA (Excl α) where
  pcore _ := none
  op _ _ := invalid
  ValidN _ := Valid
  Valid
  op_ne.ne _ _ _ _ := trivial
  pcore_ne := by simp
  validN_ne {n x y} h₁ h₂ := by cases x <;> cases y <;> trivial
  valid_iff_validN {x} := by
    constructor
    · intro h n; cases x <;> trivial
    · intro h; cases x <;> simp_all
  validN_succ {x n} h := by cases x <;> trivial
  assoc := by simp
  comm := by simp
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono := by simp
  validN_op_left := by simp
  extend {n x y₁ y₂} h₁ h₂ := by cases x <;> trivial

theorem excl_included [OFE α] {x y : Excl α} : x ≼ y ↔ y = invalid := by
  constructor
  · intro h
    rcases h with ⟨z, hz⟩
    cases x <;> cases y <;> trivial
  · intro h
    exists invalid
    exact Equiv.of_eq h

theorem excl_includedN [OFE α] {x y : Excl α} (n) : x ≼{n} y ↔ y = invalid := by
  constructor
  · intro ⟨z, hz⟩; cases x <;> cases y <;> trivial
  · rintro rfl; exists invalid

instance [OFE α] {x : Excl α} : CMRA.Exclusive x where exclusive0_l := fun _ a => a

instance [OFE α] [OFE.Discrete α] : CMRA.Discrete (Excl α) where
  discrete_valid a := a

theorem invalid_included [OFE α] (ea : Excl α) : ea ≼ invalid := by exists invalid

/-! ## Functors -/
theorem excl_map_id : map id x = x := by
  cases x <;> simp

theorem excl_map_compose (f : α → β) (g : β → γ) :
    map (g ∘ f) x = map g (map f x) := by
  cases x <;> simp

theorem excl_map_ext [OFE α] [OFE β] (f g : α → β) (h : ∀ x, f x ≡ g x) : map f x ≡ map g x := by
  cases x; apply h _; simp

theorem excl_map_ne [OFE α] [OFE β] (f : α -n> β) : NonExpansive (map f) where
  ne n x₁ x₂ h := by
    cases x₁ <;> cases x₂ <;> try trivial
    have ⟨hne⟩ := f.ne
    exact hne h

def exclO_map [OFE α] [OFE β] (f : α -n> β) : Excl α -C> Excl β := by
  refine ⟨⟨map f, excl_map_ne f⟩, ?_, ?_, ?_⟩
  · intro n x h; cases x <;> trivial
  · intro x; trivial
  · intro x y; trivial

abbrev ExclOF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => Excl (F A B)

instance {F} [COFE.OFunctor F] : RFunctor (ExclOF F) where
  cmra := inferInstance
  map f g := exclO_map (COFE.OFunctor.map f g)
  map_ne.ne := by
    intros n f₁ f₂ hf g₁ g₂ hg x
    cases x with
    | excl a =>
      apply COFE.OFunctor.map_ne.ne
      exact hf
      exact hg
    | invalid => trivial
  map_id {_ _} _ _ x := by
    cases x
    · apply COFE.OFunctor.map_id
    · trivial
  map_comp f g f' g' x := by
    cases x
    · apply COFE.OFunctor.map_comp
    · trivial

instance {F} [COFE.OFunctorContractive F] : RFunctorContractive (ExclOF F) where
  map_contractive.1 {n x y} HKL z := by
    rewrite [RFunctor.map]
    cases z
    · apply COFE.OFunctorContractive.map_contractive.1
      exact HKL
    · trivial
