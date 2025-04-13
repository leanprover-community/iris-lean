/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.uPred
import Iris.Algebra.COFESolver

import Init.Data.Vector

namespace Iris

abbrev gFunctors := Array COFE.OFunctorPre

abbrev gFunctors.len (FF : gFunctors) := FF.size

abbrev gid (FF : gFunctors) : Type _ := Fin (FF.len)


abbrev IsGFunctors (G : gFunctors) := ∀ (i : gid G), RFunctorContractive G[i]

def subG (FF₁ FF₂ : gFunctors) : Prop :=
  ∀ i : gid FF₁, ∃ j : gid FF₂, FF₁[i] = FF₂[j]

/-
namespace subG

variable (FF₁ FF₂ FF₃ : gFunctors)

theorem split_L (H : subG (FF₁ ++ FF₂) FF₃) : subG FF₁ FF₃ := by
  intro i
  rcases i with ⟨ i, Hi ⟩
  have Hi' : i < (FF₁ ++ FF₂).len := by
    simp only [Array.length_toList, Array.size_append]
    exact Nat.lt_add_right (Array.size FF₂) Hi
  rcases H ⟨ i, Hi' ⟩ with ⟨ j, Hj ⟩
  exists j
  rw [<- Hj]
  apply Array.getElem_append_left'

theorem comm (H : subG (FF₁ ++ FF₂) FF₃) : subG (FF₂ ++ FF₁) FF₃ := by
  intro i
  rcases i with ⟨ i, Hi ⟩
  sorry

theorem split_R (H : subG (FF₁ ++ FF₂) FF₃) : subG FF₁ FF₃ := by
  sorry

theorem refl : subG FF₁ FF₁ := by
  sorry

theorem app_R (H : subG FF₁ FF₂) : subG FF₁ (FF₂ ++ FF₃) := by
  sorry

end subG
-/


-- Why does Iris use positive here?
abbrev gname :=  { n : Nat // 0 < n }
def gnameO := LeibnizO gname

abbrev iResF (FF : gFunctors) : COFE.OFunctorPre :=
  discrete_funOF (fun i : gid FF => gen_mapOF gname FF[i])

section iProp

open COFE

variable (FF : gFunctors) [IG : IsGFunctors FF]

local instance : Inhabited (uPredOF (iResF FF) (ULift Unit) (ULift Unit)) := ⟨ fun _ _ => True, by simp ⟩

local instance (α : Type) [COFE α] : IsCOFE (uPredOF (iResF FF) α α) := uPred_IsCOFE

def iPrePropO : Type _ := OFunctor.Fix (uPredOF (iResF FF))

instance : COFE (iPrePropO FF) := COFE.OFunctor.fix_COFE

def iResUR : Type :=
  discrete_funO (fun (i : gid FF) => gen_map gname (FF[i] (iPrePropO FF) (iPrePropO FF)))

instance : UCMRA (iResUR FF) :=
  discrete_funO.isCMRA fun (i : gid FF) => gen_map gname (FF[i] (iPrePropO FF) (iPrePropO FF))

abbrev iProp := uPred (iResUR FF)

-- #synth COFE (iProp FF)

end iProp

end Iris
