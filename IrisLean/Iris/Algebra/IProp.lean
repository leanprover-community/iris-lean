/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.UPred
public import Iris.Algebra.GenMap
public import Iris.Algebra.COFESolver
public import Init.Data.Vector
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

open COFE

abbrev GType := Nat

def BundledGFunctors := GType → Σ F : OFunctorPre, RFunctorContractive F

def BundledGFunctors.default : BundledGFunctors := fun _ => ⟨COFE.constOF Unit, by infer_instance⟩

def BundledGFunctors.set (GF : BundledGFunctors) (i : Nat) (FB : Σ F, RFunctorContractive F) :
    BundledGFunctors :=
  fun j => if j = i then FB else GF j

abbrev GName := Nat

@[rocq_alias iResF]
abbrev IResF (GF : BundledGFunctors) : OFunctorPre :=
  DiscreteFunOF (fun i => GenMapOF (GF i).fst)

instance (GF : BundledGFunctors) (i : GName) : RFunctorContractive ((GF i).fst) := (GF i).snd

section IProp

variable (GF : BundledGFunctors)

@[rocq_alias iPrePropO]
def IPre : Type _ := OFunctor.Fix (UPredOF (IResF GF))

@[rocq_alias iPreProp_cofe]
instance : COFE (IPre GF) := inferInstanceAs (COFE (OFunctor.Fix _))

@[rocq_alias iResUR]
def IResUR : Type := (i : GType) → GenMap (GF i |>.fst (IPre GF) (IPre GF))

instance : UCMRA (IResUR GF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GenMap (GF i |>.fst (IPre GF) (IPre GF)))

@[rocq_alias iProp]
abbrev IProp := UPred (IResUR GF)

@[rocq_alias iProp_unfold]
def IProp.unfold : IProp GF -n> IPre GF :=
  OFE.Iso.hom <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

@[rocq_alias iProp_fold]
def IProp.fold : IPre GF -n> IProp GF :=
  OFE.Iso.inv <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

end IProp

end Iris
