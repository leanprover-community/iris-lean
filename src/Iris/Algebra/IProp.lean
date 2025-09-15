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

-- MARKUSDE: The number of types of ghost state being finite is not necessary
-- for any of the ghost state constructions so we can remove it and simplify
-- the types.

/-- GType: Each type of ghost state in the global context of ghost states is
referenced by its index (GType) in a GFunctors list. -/
abbrev GType := Nat

def GFunctors := GType → COFE.OFunctorPre

-- MARKUSDE: Abbreviation so synthesis of IsGFunctors works
abbrev GFunctors.default : GFunctors := fun _ => COFE.constOF Unit

def GFunctors.set (GF : GFunctors) (i : Nat) (F : COFE.OFunctorPre) : GFunctors :=
  fun j => if j == i then F else GF j

abbrev IsGFunctors (G : GFunctors) := ∀ i, RFunctorContractive (G i)

instance [IsGFunctors GF] [RFunctorContractive F] : IsGFunctors (GF.set i F) :=
  fun _ => by unfold GFunctors.set; split <;> infer_instance

def SubG (FF₁ FF₂ : GFunctors) : Prop := ∀ i, ∃ j, FF₁ i = FF₂ j

/-- GName: Ghost variable name. In iProp, there are an unlimited amount of names for
each GType .-/
abbrev GName := Nat

abbrev IResF (FF : GFunctors) : COFE.OFunctorPre :=
  DiscreteFunOF (fun i => GenMapOF GName (FF i))

section IProp

variable (GF : BundledGFunctors)

def IPre : Type _ := OFunctor.Fix (UPredOF (IResF GF))

instance : COFE (IPre GF) := inferInstanceAs (COFE (OFunctor.Fix _))

def IResUR : Type := (i : GType) → GenMap Nat (GF i |>.fst (IPre GF) (IPre GF))

instance : UCMRA (IResUR GF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GenMap GName (GF i |>.fst (IPre GF) (IPre GF)))

abbrev IProp := UPred (IResUR GF)

def IProp.unfold : IProp GF -n> IPre GF :=
  OFE.Iso.hom <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

def IProp.fold : IPre GF -n> IProp GF :=
  OFE.Iso.inv <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

end IProp

end Iris
