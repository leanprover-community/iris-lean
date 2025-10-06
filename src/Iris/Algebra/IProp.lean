/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.GenMap
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

abbrev IResF (GF : BundledGFunctors) : OFunctorPre :=
  DiscreteFunOF (fun i => GenMapOF GName (GF i).fst)

instance (GF : BundledGFunctors) (i : GName) : RFunctorContractive ((GF i).fst) := (GF i).snd

section IProp

variable (GF : BundledGFunctors)

-- instance : OFunctorContractive (UPredOF (IResF GF)) := by
--   unfold IResF
--   let X := @instUPredOFunctorContractive (F := IResF GF)
--   sorry

def IPre : Type _ := OFunctor.Fix (UPredOF (IResF GF))

instance : COFE (IPre GF) := inferInstanceAs (COFE (OFunctor.Fix _))

def IResUR : Type := (i : GType) → GName → Option (GF i |>.fst (IPre GF) (IPre GF))

instance : UCMRA (IResUR GF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GName → Option (GF i |>.fst (IPre GF) (IPre GF)))

abbrev IProp := UPred (IResUR GF)

-- def IProp.unfold : IProp GF -n> IPre GF :=
--   OFE.Iso.hom <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

def IProp.unfold :=
  OFE.Iso.hom <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

def IProp.fold : IPre GF -n> IProp GF :=
  OFE.Iso.inv <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

end IProp

end Iris
