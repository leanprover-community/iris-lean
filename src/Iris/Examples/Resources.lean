/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI
import Iris.ProofMode
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Own
import Iris.Algebra.Agree


namespace Iris.Examples
open Iris.BI

section no_resources

abbrev FF0 : GFunctors := #[]

local instance : IsGFunctors FF0 := nofun

-- A proof with no resources
example (P Q : IProp FF0) : P ∗ Q ⊢ ⌜True⌝ := by
  iintro ⟨HP, HQ⟩
  ipure_intro
  trivial

example (P Q : IProp FF0) : P ∗ Q ⊢ P := by
  iintro ⟨HP, HQ⟩
  iexact HP

end no_resources

section const_agree

variable {FF1 : GFunctors} [inG FF1 (Agree (LeibnizO String))]

@[simp]
def MyAg (S : String) : Agree (LeibnizO String) := ⟨[⟨S⟩], by simp⟩

@[simp]
def MyR (S : String) : Iris.IResUR FF1 := iRes_singleton (MyAg S)

--set_option pp.explicit true in
set_option pp.proofs true in
theorem MyR_always_invalid (S₁ S₂ : String) (Hne : S₁ ≠ S₂) (n : Nat) : ¬✓{n} MyR S₁ • @MyR FF1 _ S₂ := by
  simp [CMRA.op, CMRA.ValidN]
  rename_i i; rcases i with ⟨ gid, prf ⟩; simp [ap, RFunctor.ap] at prf

  exists gid, ⟨ 0 ⟩
  simp [iRes_singleton, discrete_fun_singleton, discrete_fun_insert,
        instIsGFunctors, CMRA.ValidN, CMRA.op, Agree.op, Agree.validN,
        instCOFELeibnizO, COFE.ofDiscrete, OFE.ofDiscrete, optionOp, optionValidN]
  unfold CMRA.op; unfold CMRA.ValidN;
  simp [RFunctor.cmra, RFunctorContractive.toRFunctor]
  unfold GFunctor.map_contractive
  unfold GFunctor.car at prf
  simp [cast]
  sorry

  -- exact fun a => id (Ne.symm Hne)

#check MyR_always_invalid

def AgreeString (S : String) : IProp FF1 := UPred.ownM (MyR S)

example : AgreeString "I <3 iris-lean!" ⊢ (@AgreeString FF1 _ "I don't :<" -∗ False) := by
  iintro H H2
  istop
  apply (UPred.ownM_op _ _).2.trans    -- Combine ghost state
  apply (UPred.ownM_valid _).trans     -- Reduce to invalidity
  apply UPred.ownM_always_invalid_elim -- The resource is invalid
  apply MyR_always_invalid; simp       -- Simplify

end const_agree
end Iris.Examples
