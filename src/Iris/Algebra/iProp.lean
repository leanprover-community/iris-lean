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

abbrev gFunctors := Array (Type _ → Type _ → Type _)

abbrev gFunctors.len (FF : gFunctors) := FF.size

abbrev gid (FF : gFunctors) : Type _ := Fin (FF.len)

class IsgFunctors (G : gFunctors) where
  functor (i : gid G) : RFunctorContractive G[i]

attribute [instance] IsgFunctors.functor

def subG (FF₁ FF₂ : gFunctors) : Prop :=
  ∀ i : gid FF₁, ∃ j : gid FF₂, FF₁[i] = FF₂[j]

namespace subG

variable (FF₁ FF₂ FF₃ : gFunctors)

theorem split_L (H : subG (FF₁ ++ FF₂) FF₃) : subG FF₁ FF₃ := by
  sorry

theorem comm (H : subG (FF₁ ++ FF₂) FF₃) : subG (FF₂ ++ FF₁) FF₃ := by
  sorry

theorem split_R (H : subG (FF₁ ++ FF₂) FF₃) : subG FF₁ FF₃ := by
  sorry

theorem refl : subG FF₁ FF₁ := by
  sorry

theorem app_R (H : subG FF₁ FF₂) : subG FF₁ (FF₂ ++ FF₃) := by
  sorry

end subG


-- Why does Iris use positive here?
abbrev gname :=  { n : Nat // 0 < n }
def gnameO := LeibnizO gname

def iResF (FF : gFunctors) : (Type _ -> Type -> Type _) :=
  discrete_fun_OF (fun i : gid FF => gen_mapOF gname FF[i])

-- instance (FF) [IsgFunctors FF] (c : gid FF) : URFunctor (gen_mapOF gname FF[c]) := by infer_instance
instance (FF) [IsgFunctors FF] : URFunctorContractive (iResF FF) := by
  unfold iResF
  infer_instance

section iProp

open COFE


variable (FF : gFunctors) [IG : IsgFunctors FF]
-- #synth OFunctorContractive (uPredOF (iResF FF))


local instance DELETEME : Inhabited (uPredOF (iResF FF) (ULift Unit) (ULift Unit)) := sorry

local instance DELETEME2 : (α : Type) → [inst : COFE α] → IsCOFE (uPredOF (iResF FF) α α) :=
  fun α {H} => by sorry

def iPrePropO : Type _ := OFunctor.Fix (uPredOF (iResF FF))

-- FIXME: Remove, Mario wants to remove COFE.OFunctor.fix_COFE
instance : COFE (iPrePropO FF) := COFE.OFunctor.fix_COFE

def iResUR : Type :=
  discrete_fun (fun (i : gid FF) => gen_map gname (FF[i] (iPrePropO FF) (iPrePropO FF)))


local instance DELETEME3 : CMRA (iResUR FF) := by
  unfold iResUR
  sorry

abbrev iProp := uPred (iResUR FF)

local instance : UCMRA (iResUR FF) := sorry

-- This was inferring before, why did it stop?
instance : COFE (iProp FF) := by sorry

end iProp

end Iris
