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

@[expose] public section

namespace Iris

open COFE

abbrev GType := Nat

@[rocq_alias gFunctor]
abbrev GFunctor := Σ F : OFunctorPre, RFunctorContractive F

@[rocq_alias gFunctors]
def BundledGFunctors := GType → GFunctor

def BundledGFunctors.default : BundledGFunctors := fun _ => ⟨constOF Unit, by infer_instance⟩

def BundledGFunctors.set (GF : BundledGFunctors) (i : Nat) (FB : GFunctor) :
    BundledGFunctors :=
  fun j => if j = i then FB else GF j

#rocq_ignore gid "Not needed, `gFunctors` is bundled"
#rocq_ignore gFunctors.nil "Not needed, `gFunctors` is bundled"
#rocq_ignore gFunctors.singleton "Not needed, `gFunctors` is bundled"
#rocq_ignore gFunctors.app "Not needed, `gFunctors` is bundled"

@[rocq_alias gname]
abbrev GName := Nat

#rocq_ignore gnameO "Not needed"

@[rocq_alias iResF]
abbrev IResF (GF : BundledGFunctors) : OFunctorPre :=
  DiscreteFunOF (fun i => GenMapOF (GF i).fst)

#rocq_ignore subG "Not needed, see `ElemG`"
#rocq_ignore subG_inv "Not needed"
#rocq_ignore subG_refl "Not needed"
#rocq_ignore subG_app_l "Not needed"
#rocq_ignore subG_app_r "Not needed"

instance (GF : BundledGFunctors) (i : GName) : RFunctorContractive ((GF i).fst) := (GF i).snd

section IProp

variable (GF : BundledGFunctors)

@[rocq_alias iProp_solution.iPrePropO, rocq_alias iProp_solution.iProp_result]
def IPre : Type _ := OFunctor.Fix (UPredOF (IResF GF))

@[rocq_alias iProp_solution.iPreProp_cofe]
instance : COFE (IPre GF) := inferInstanceAs (COFE (OFunctor.Fix _))

@[rocq_alias iProp_solution.iResUR]
def IResUR : Type := (i : GType) → GenMap (GF i |>.fst (IPre GF) (IPre GF))

#rocq_ignore iResUR "Not needed, only used for sealing in Rocq"

instance : UCMRA (IResUR GF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GenMap (GF i |>.fst (IPre GF) (IPre GF)))

abbrev IProp := UPred (IResUR GF)

@[rocq_alias iProp_solution.iProp_unfold]
def IProp.unfold : IProp GF -n> IPre GF :=
  OFE.Iso.hom <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

@[rocq_alias iProp_solution.iProp_fold]
def IProp.fold : IPre GF -n> IProp GF :=
  OFE.Iso.inv <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

end IProp

end Iris
