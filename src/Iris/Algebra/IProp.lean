/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.COFESolver

import Init.Data.Vector

namespace Iris

def GFunctors := Array COFE.OFunctorPre

def GId (FF : GFunctors) : Type _ := Fin FF.size

instance (FF : GFunctors) : GetElem GFunctors (GId FF) COFE.OFunctorPre (fun _ _ => True) where
  getElem _ x _ := FF.get x.1 x.2

abbrev IsGFunctors (G : GFunctors) := ∀ (i : GId G), RFunctorContractive G[i]

def SubG (FF₁ FF₂ : GFunctors) : Prop :=
  ∀ i : GId FF₁, ∃ j : GId FF₂, FF₁[i] = FF₂[j]

/-
namespace SubG

variable (FF₁ FF₂ FF₃ : GFunctors)

theorem split_L (H : SubG (FF₁ ++ FF₂) FF₃) : SubG FF₁ FF₃ := by
  intro i
  rcases i with ⟨i, Hi⟩
  have Hi' : i < (FF₁ ++ FF₂).len := by
    simp only [Array.length_toList, Array.size_append]
    exact Nat.lt_add_right (Array.size FF₂) Hi
  rcases H ⟨i, Hi'⟩ with ⟨j, Hj⟩
  exists j
  rw [<- Hj]
  apply Array.getElem_append_left'

theorem comm (H : SubG (FF₁ ++ FF₂) FF₃) : SubG (FF₂ ++ FF₁) FF₃ := by
  intro i
  rcases i with ⟨i, Hi⟩
  sorry

theorem split_R (H : SubG (FF₁ ++ FF₂) FF₃) : SubG FF₁ FF₃ := by
  sorry

theorem refl : SubG FF₁ FF₁ := by
  sorry

theorem app_R (H : SubG FF₁ FF₂) : SubG FF₁ (FF₂ ++ FF₃) := by
  sorry

end SubG
-/


-- Why does Iris use positive here?
def GName := LeibnizO Nat

abbrev IResF (FF : GFunctors) : COFE.OFunctorPre :=
  DiscreteFunOF (fun i : GId FF => gen_mapOF GName FF[i])

section IProp

open COFE

variable (FF : GFunctors) [IG : IsGFunctors FF]

def iPrePropO : Type _ := OFunctor.Fix (UPredOF (IResF FF))

instance : COFE (iPrePropO FF) := COFE.OFunctor.fix_COFE

def IResUR : Type :=
  DiscreteFunO (fun (i : GId FF) => GName -d> Option (FF[i] (iPrePropO FF) (iPrePropO FF)))

instance : UCMRA (IResUR FF) :=
  DiscreteFunO.isCMRA fun (i : GId FF) => GName -d> Option (FF[i] (iPrePropO FF) (iPrePropO FF))

abbrev IProp := UPred (IResUR FF)

-- #synth COFE (IProp FF)

end IProp

end Iris
