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
open COFE

variable (FF : GFunctors) [IsGFunctors FF]

def iPrePropO : Type _ := OFunctor.Fix (UPredOF (IResF FF))

instance : COFE (iPrePropO FF) := inferInstanceAs (COFE (OFunctor.Fix _))

def IResUR : Type := (i : GType) → GName → Option (FF i (iPrePropO FF) (iPrePropO FF))

instance : UCMRA (IResUR FF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GName → Option (FF i (iPrePropO FF) (iPrePropO FF)))

abbrev IProp := UPred (IResUR FF)

end IProp

class InG (FF : GFunctors) [IsGFunctors FF] (A : Type _) where
  typ : GType
  lookup : A = FF typ (iPrePropO FF) (iPrePropO FF) := by rfl

instance : InG GFunctors.default Unit where typ := 0

def OwnR (FF : GFunctors) [IsGFunctors FF] [I : InG FF A] (γ : GName) (a : A) : IResUR FF :=
  fun τ' γ' => if H : τ' = I.typ ∧ γ' = γ then H.1▸I.lookup |>.mp a else none

-- Issue: Not necessarily true that the CMRA instance for B is the same as the tranasport
-- of the CMRA instance for A.
-- Solutions: Bundle CMRA instance in GFunctors & add constraint to InG
-- Internalize CMRA data?
-- theorem CMRA.Valid_transport {A B : Type _} [CMRA A] [CMRA B] {a : A} {b : B}
--     (H : A = B) : (✓ a) = (✓ (H ▸ a)) := by
--   subst H
--   congr 1
--   sorry

section OwnR

/-
variable (FF : GFunctors) [IsGFunctors FF]

theorem valid_iff [CMRA A] [InG FF A] (a : A) : ✓ a ↔ ✓ (OwnR FF γ a) := by
  refine ⟨fun Hv τ' γ' => ?_, ?_⟩
  · simp only [CMRA.Valid, optionValid, OwnR]
    split <;> try trivial
    rename_i x y He; revert He
    split
    · rintro ⟨H⟩
      sorry
    · rintro ⟨⟩
  · sorry
-/
end OwnR



attribute [irreducible] OwnR -- OwnR should be manipulated using equations only

end Iris
