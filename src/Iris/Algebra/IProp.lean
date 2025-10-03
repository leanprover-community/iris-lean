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

open COFE

abbrev GType := Nat

def BundledGFunctors := GType → Σ F : OFunctorPre, RFunctorContractive F

def BundledGFunctors.default : BundledGFunctors := fun _ => ⟨COFE.constOF Unit, by infer_instance⟩

def BundledGFunctors.set (GF : BundledGFunctors) (i : Nat) (FB : Σ F, RFunctorContractive F) :
    BundledGFunctors :=
  fun j => if j = i then FB else GF j

abbrev GName := Nat

abbrev IResF (FF : BundledGFunctors) : OFunctorPre :=
  DiscreteFunOF (fun i => GenMapOF GName (FF i).fst)

instance (FF: BundledGFunctors) (i : GName) : RFunctorContractive ((FF i).fst) := (FF i).snd

section IProp

variable (FF : BundledGFunctors)

def IPre : Type _ := OFunctor.Fix (UPredOF (IResF FF))

instance : COFE (IPre FF) := inferInstanceAs (COFE (OFunctor.Fix _))

def IResUR : Type := (i : GType) → GName → Option (FF i |>.fst (IPre FF) (IPre FF))

instance : UCMRA (IResUR FF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GName → Option (FF i |>.fst (IPre FF) (IPre FF)))

abbrev IProp := UPred (IResUR FF)

def IProp.unfold : IProp FF -n> IPre FF :=
  OFE.Iso.hom <| OFunctor.Fix.iso (F := (UPredOF (IResF FF)))

def IProp.fold : IPre FF -n> IProp FF :=
  OFE.Iso.inv <| OFunctor.Fix.iso (F := (UPredOF (IResF FF)))

end IProp

end Iris
