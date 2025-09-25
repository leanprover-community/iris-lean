/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI
import Iris.Algebra.OFE
import Iris.Algebra.CMRA
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred

section Own

open Iris COFE UPred

/-- IApp: Apply an OFunctor to the solution to the Iris Fixpoint -/
def Iris.COFE.OFunctorPre.IApp (F : OFunctorPre) (FF) [IsGFunctors FF] : Type _ :=
  F (IPre FF) (IPre FF)

/- Attempt 1: Like InG
class ElemG (FF) [GF : IsGFunctors FF] (τ : GType) (A : Type _) [inst : CMRA A] where
  get : A = (FF τ (IPre FF) (IPre FF))
  get_cmra : (RFunctor.cmra : CMRA (FF τ (IPre FF) (IPre FF))) = get ▸ inst

def ElemG.ofA [IsGFunctors FF] [CMRA A] [E : ElemG FF τ A] : A → FF τ (IPre FF) (IPre FF) :=
  fun a => E.get ▸ a

def ElemG.toA [IsGFunctors FF] [CMRA A] [E : ElemG FF τ A] : FF τ (IPre FF) (IPre FF) → A :=
  fun v => E.get ▸ v

theorem ElemG.ofA_toA [IsGFunctors FF] [CMRA A] [E : ElemG FF τ A] (a : A) :
    E.toA (E.ofA a) = a := by
  unfold ElemG.ofA
  unfold ElemG.toA
  grind only -- What the heck??

theorem ElemG.toA_ofA [IsGFunctors FF] [CMRA A] [E : ElemG FF τ A] (a : FF τ (IPre FF) (IPre FF)) :
    E.ofA (E.toA a) = a := by
  unfold ElemG.ofA
  unfold ElemG.toA
  grind only -- What the heck??

def iSingleton [IsGFunctors FF] (τ : GType) (γ : GName) (v : FF τ (IPre FF) (IPre FF)) : IResUR FF :=
  fun τ' γ' => if Hτ : τ' = τ then if γ' = γ then some (Hτ ▸ v) else none else none

def iOwn [IsGFunctors FF] (τ : GType) (γ : GName) (v : FF τ (IPre FF) (IPre FF)) : IProp FF :=
  UPred.ownM <| iSingleton τ γ v

set_option pp.all true
theorem ElemG.ofA_valid [IsGFunctors FF] [CMRA A] [E : ElemG FF τ A] (a : A) :
    ✓ a → ✓ (E.ofA a) := by
  rw [E.get_cmra]
  sorry -- Stuck, nasty
-/

-- Attempt 2

class ElemG (FF) [GF : IsGFunctors FF] (τ : GType) (F : OFunctorPre) where
  get : FF τ = F

def ElemG.Lift [IsGFunctors FF] [E : ElemG FF τ F] : F (IPre FF) (IPre FF) → FF τ (IPre FF) (IPre FF) :=
  fun a => E.get ▸ a


def IProp.proj_unfold [GF : IsGFunctors FF] : FF τ (IProp FF) (IProp FF) -n> FF τ (IPre FF) (IPre FF):=
  OFunctor.map (IProp.fold FF) (IProp.unfold FF)

def IProp.proj_fold [IsGFunctors FF] :
    FF τ (IPre FF) (IPre FF) -n> FF τ (IProp FF) (IProp FF) :=
  OFunctor.map (IProp.unfold FF) (IProp.fold FF)

theorem IProp.proj_unfold_fold [IsGFunctors FF] (x : FF τ (IPre FF) (IPre FF)) :
    proj_unfold (proj_fold x) ≡ x := by
  sorry

theorem IProp.proj_fold_unfold [IsGFunctors FF] (x : FF τ (IProp FF) (IProp FF)) :
    proj_fold (proj_unfold x) ≡ x := by
  sorry

def iSingleton [IsGFunctors FF] (τ : GType) (γ : GName) (v : FF τ (IProp FF) (IProp FF)) : IResUR FF :=
  fun τ' γ' => if Hτ : τ' = τ then if γ' = γ then some (Hτ ▸ (IProp.proj_unfold <| v)) else none else none

instance [IsGFunctors FF] {τ : GType} {γ : GName} : OFE.NonExpansive (iSingleton (FF := FF) τ γ) where
  ne {x} := by sorry

def iOwn [IsGFunctors FF] (τ : GType) (γ : GName) (v : FF τ (IProp FF) (IProp FF)) : IProp FF :=
  UPred.ownM <| iSingleton τ γ v

theorem iSingleton_op [IsGFunctors FF]  (x y : FF τ (IProp FF) (IProp FF)):
    (iSingleton τ γ x) • iSingleton τ γ y ≡ iSingleton τ γ (x • y) := by
  intro τ' γ'
  unfold iSingleton
  simp [CMRA.op]
  split
  · split <;> simp [optionOp]
    sorry
  · simp [optionOp]

end Own
