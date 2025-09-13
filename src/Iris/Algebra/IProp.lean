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
  getElem _ x _ := (show Array _ from FF)[x.1]

abbrev IsGFunctors (G : GFunctors) := ∀ (i : GId G), RFunctorContractive G[i]

def SubG (FF₁ FF₂ : GFunctors) : Prop :=
  ∀ i : GId FF₁, ∃ j : GId FF₂, FF₁[i] = FF₂[j]

abbrev GName := Nat

abbrev IResF (FF : GFunctors) : COFE.OFunctorPre :=
  DiscreteFunOF (fun i : GId FF => GenMapOF GName FF[i])

section IProp
open COFE

variable (FF : GFunctors) [IG : IsGFunctors FF]

def iPrePropO : Type _ := OFunctor.Fix (UPredOF (IResF FF))

instance : COFE (iPrePropO FF) := inferInstanceAs (COFE (OFunctor.Fix _))

def IResUR : Type := (i : GId FF) → GName → Option (FF[i] (iPrePropO FF) (iPrePropO FF))

instance : UCMRA (IResUR FF) :=
  ucmraDiscreteFunO (β := fun (i : GId FF) => GName → Option (FF[i] (iPrePropO FF) (iPrePropO FF)))

abbrev IProp := UPred (IResUR FF)

end IProp
end Iris
