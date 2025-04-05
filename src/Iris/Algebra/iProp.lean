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

-- TODO: Externalize!!!
structure gFunctor : Type _ where
  F : Type _ -> Type _ -> Type _
  functor : RFunctorContractive F

attribute [instance] gFunctor.functor

def gFunctor.ap (F : gFunctor) (A : Type _) [COFE A] : Type _ := F.F A A

-- gFunctors: thin wrapper around Array to make working with it less painful

abbrev gFunctors : Type _ := Array gFunctor

abbrev gFunctors.len (FF : gFunctors) := FF.size

abbrev gid (FF : gFunctors) : Type _ := Fin (FF.len)

def gFunctors.lookup (FF : gFunctors) (n : gid FF) : gFunctor := FF[n]

-- Why does Iris use positive here?
abbrev gname :=  { n : Nat // 0 < n }
def gnameO := LeibnizO gname

def gFunctors.nil : gFunctors := #[]

def gFunctors.singleton (F : gFunctor) : gFunctors := #[F]

def gFunctors.app (FF₁ FF₂ : gFunctors) := FF₁ ++ FF₂

class subG (FF₁ FF₂ : gFunctors) : Prop where
  in_subG : ∀ i : gid FF₁, ∃ j : gid FF₂, FF₁.lookup i = FF₂.lookup j

theorem subG_split_L (FF₁ FF₂ FF₃ : gFunctors) (H : subG (FF₁.app FF₂) FF₃) : (subG FF₁ FF₃) := sorry

theorem subG_comm (FF₁ FF₂ FF₃ : gFunctors) (H : subG (FF₁.app FF₂) FF₃) : subG (FF₂.app FF₁) FF₃ := sorry

theorem subG_split_R (FF₁ FF₂ FF₃ : gFunctors) (H : subG (FF₁.app FF₂) FF₃) : (subG FF₁ FF₃) := sorry

theorem subG_refl (FF : gFunctors) : subG FF FF := sorry

theorem subG_aop_R (FF₁ FF₂ FF₃ : gFunctors) (H : subG FF₁ FF₂) : (subG FF₁ (FF₂.app FF₃)) := sorry


def iResF (FF : gFunctors) : (Type _ -> Type -> Type _) :=
  discrete_fun_OF (fun i : gid FF => gen_mapOF gname (gFunctors.lookup FF i).F)

-- We need gmap so that IResF is a real URFunctor: gFunctors.lookup is an rFunctor not a urFunctor

instance DELETEME0 (FF : gFunctors) (c : gid FF) : ∀ (_ : gname), URFunctor (FF.lookup c).F := sorry
instance (FF : gFunctors) (c : gid FF) : URFunctor (discrete_fun_OF fun (_ : gname) => (FF.lookup c).F) :=
  @IsOFEFun_UF _ _ (DELETEME0 FF c)
instance DELETEME1 (x : gFunctors) : URFunctor (iResF x) := by apply @IsOFEFun_UF


section iProp

local instance DELETEME2 (FF : gFunctors): COFE.OFunctorContractive (uPredOF (iResF FF)) := sorry


-- Should be the case for ever OFunctorContractive, and in particular for the one we're using,
-- but this is here to make sure the right instances are inferred below
local instance DELETEME3 (FF : gFunctors) : ∀ (α : Type) [inst : COFE α],
      @Iris.IsCOFE.{0} (@Iris.uPredOF.{0, 0} (Iris.iResF.{0, 0} FF) (Iris.DELETEME1.{0, 0} FF) α α)
        (@Iris.COFE.OFunctor.cofe.{0, 0, 0} (@Iris.uPredOF.{0, 0} (Iris.iResF.{0, 0} FF) (Iris.DELETEME1.{0, 0} FF))
          (@Iris.COFE.OFunctorContractive.toOFunctor.{0, 0, 0}
            (@Iris.uPredOF.{0, 0} (Iris.iResF.{0, 0} FF) (Iris.DELETEME1.{0, 0} FF))
            (Iris.DELETEME2.{0} FF))
          α α inst inst) := sorry

local instance DELETEME4 (FF : gFunctors) : Inhabited (uPredOF (iResF FF) (ULift Unit) (ULift Unit)) := sorry
-- set_option pp.all true

def iPrePropO (FF : gFunctors) : Type _ := COFE.OFunctor.Fix (uPredOF (iResF FF))

-- FIXME: Remove, Mario wants to remove COFE.OFunctor.fix_COFE
instance (FF : gFunctors) : COFE (iPrePropO FF) := COFE.OFunctor.fix_COFE


def iResUR (FF : gFunctors) : Type :=
  discrete_fun (fun (i : gid FF) =>
gen_map gname ((FF.lookup i).F (iPrePropO FF) (iPrePropO FF)))

local instance DELELTEME5 : IsUCMRAFun (iResUR) := sorry -- Will be able to show this is a UCMRA after gmap change

abbrev iProp (FF : gFunctors) := uPred (iResUR FF)

-- variable (FF : gFunctors)
-- #synth COFE (iProp FF)

end iProp

end Iris
