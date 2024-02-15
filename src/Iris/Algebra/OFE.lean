/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Logic

namespace Iris

/-- Ordered family of equivalences -/
class OFE (α : Type) where
  Equiv : α → α → Prop
  Dist : Nat → α → α → Prop
  equiv_eqv : Equivalence Equiv
  dist_eqv : Equivalence (Dist n)
  equiv_dist : Equiv x y ↔ ∀ n, Dist n x y
  dist_lt : Dist n x y → m < n → Dist m x y

open OFE

scoped infix:25 " ≡ " => OFE.Equiv
scoped notation x " ≡{" n "}≡ " y:26 => OFE.Dist n x y

namespace OFE

def NonExpansive [OFE α] (f : α → α) :=
  ∀ n x₁ x₂, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f x₂

def NonExpansive₂ [OFE α] (f : α → α → α) :=
  ∀ n x₁ x₂, x₁ ≡{n}≡ x₂ → ∀ y₁ y₂, y₁ ≡{n}≡ y₂ → f x₁ y₁ ≡{n}≡ f x₂ y₂

structure Chain (α : Type) [OFE α] where
  chain : Nat → α
  cauchy : n ≤ i → chain i ≡{n}≡ chain n

instance [OFE α] : CoeFun (Chain α) (fun _ => Nat → α) := ⟨Chain.chain⟩

def ofDiscrete (Equiv : α → α → Prop) (equiv_eqv : Equivalence Equiv) : OFE α where
  Equiv := Equiv
  Dist _ := Equiv
  equiv_eqv := equiv_eqv
  dist_eqv := equiv_eqv
  equiv_dist := (forall_const _).symm
  dist_lt h _ := h

end OFE

/-- Complete ordered family of equivalences -/
class COFE (α : Type) extends OFE α where
  compl : Chain α → α
  conv_compl {c : Chain α} : compl c ≡{n}≡ c n

namespace COFE

def ofDiscrete (Equiv : α → α → Prop) (equiv_eqv : Equivalence Equiv) : COFE α :=
  let _ := OFE.ofDiscrete Equiv equiv_eqv
  { compl := fun c => c 0
    conv_compl := fun {_ c} => equiv_eqv.2 (c.cauchy (Nat.zero_le _)) }
