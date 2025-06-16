/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/

import Iris.Algebra.CMRA

namespace Iris

section excl

variable {α : Type u} {β : Type v} {γ : Type w}
variable [OFE α] [OFE β]

inductive Excl α where
  | excl : α → Excl α
  | exclInvalid : Excl α

variable (x y : Excl α)

open Excl
open OFE

/- COFE -/
@[simp] def Excl.equiv : Prop := match x, y with
  | excl a, excl b => a ≡ b
  | exclInvalid, exclInvalid => True
  | _, _ => False

@[simp] def Excl.dist (n : Nat) : Excl α → Excl α → Prop
  | excl a, excl b => a ≡{n}≡ b
  | exclInvalid, exclInvalid => True
  | _, _ => False

theorem Excl.dist_eqv {n} : Equivalence (dist (α := α) n) where
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
  Equiv := equiv
  Dist := dist
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

instance : @NonExpansive α (Excl α) _ _ (excl) := by
  exact { ne := fun ⦃n⦄ ⦃x₁ x₂⦄ a => a }

instance : Discrete α → Discrete (Excl α) := by
  intro ⟨h⟩; refine { discrete_0 := ?_ }; intro x y h'
  cases x <;> cases y <;> try exact h'
  apply h h'

instance : Leibniz α → Leibniz (Excl α) := by
  intro ⟨h⟩; refine { eq_of_eqv := ?_ }; intro x y h'
  cases x <;> cases y <;> try trivial
  exact congrArg excl (h h')

instance {a : α} : DiscreteE a → DiscreteE (excl a) := by
  intro h; intro x h'
  cases x
  · exact h h'
  · exact h'

instance : DiscreteE (@exclInvalid α) := by
  intro x h
  cases x <;> exact h

/- Adapted from the corresponding definitions for [Option]. -/
/- This could be simplified if there was an isomorphism lemma for [COFE]s in [OFE.lean]. -/
@[simp] def Excl.getD (dflt : α) : α :=
  match x with
  | excl a => a
  | exclInvalid => dflt

@[simp] def Excl.map (f : α → β) : Excl α → Excl β
  | excl a => excl (f a)
  | exclInvalid   => exclInvalid

def exclChain (c : Chain (Excl α)) (a : α) : Chain α := by
  refine ⟨fun n => (c n).getD a, fun {n i} H => ?_⟩
  dsimp; have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist]

instance [IsCOFE α] : IsCOFE (Excl α) where
  compl c := (c 0).map fun x => IsCOFE.compl (exclChain c x)
  conv_compl {n} c := by
    have := c.cauchy (Nat.zero_le n); revert this
    rcases c.chain 0 with _|x' <;> rcases e : c.chain n with _|y' <;> simp [Dist]
    refine fun _ => dist_eqv.trans IsCOFE.conv_compl ?_
    simp [exclChain, e]

/- CMRA -/
@[simp] def Excl.pcore : Excl α → Option (Excl α) :=
  λ _ => none
@[simp] def Excl.op : Excl α → Excl α → Excl α :=
  λ _ _ => Excl.exclInvalid
@[simp] def Excl.ValidN : Nat → Excl α → Prop := λ _ x =>
  match x with | excl _ => True | exclInvalid => False
@[simp] def Excl.Valid : Excl α → Prop := λ x =>
  match x with | excl _ => True | exclInvalid => False

instance : CMRA (Excl α) where
  pcore; op; ValidN; Valid;

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

theorem excl_included : x ≼ y ↔ y = exclInvalid := by
  constructor
  · intro h
    rcases h with ⟨z, hz⟩
    cases x <;> cases y <;> trivial
  · intro h
    exists exclInvalid
    exact Equiv.of_eq h

theorem excl_includedN n : x ≼{n} y ↔ y = exclInvalid := by
  constructor
  · intro h
    rcases h with ⟨z, hz⟩
    cases x <;> cases y <;> trivial
  · intro h
    exists exclInvalid
    exact Dist.of_eq h

instance : CMRA.Exclusive x := { exclusive0_l := fun _ a => a }

instance : OFE.Discrete α → CMRA.Discrete (Excl α) := by
  intro h
  refine { toDiscrete := ?_, discrete_valid := fun {x} a => a }
  refine instDiscreteExcl ?_
  exact h

theorem exclInvalid_included ea : ea ≼ (@exclInvalid α) := by
  exists exclInvalid

/- Functors -/
omit [OFE α] in
theorem excl_map_id : map id x = x := by
  cases x <;> simp

omit [OFE α] [OFE β] in
theorem excl_map_compose (f : α → β) (g : β → γ):
  map (g ∘ f) x = map g (map f x) := by
  cases x <;> simp

omit [OFE α] in
theorem excl_map_ext (f g : α → β) :
  (∀ x, f x ≡ g x) → map f x ≡ map g x := by
  intro h; cases x
  apply h _; simp

theorem excl_map_ne (f : α -n> β) : NonExpansive (map f) := ⟨by
  intro n x₁ x₂ h
  cases x₁ <;> cases x₂ <;> try trivial
  have ⟨hne⟩ := f.ne
  exact hne h
⟩

def exclO_map {α β} [OFE α] [OFE β] (f : α -n> β) : Excl α -C> Excl β :=
  ⟨⟨map f, excl_map_ne f⟩,
  by intro n x h; cases x <;> trivial,
  by intro x; trivial,
  by intro x y; trivial⟩

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
    | exclInvalid => trivial
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
