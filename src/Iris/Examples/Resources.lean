/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI
import Iris.ProofMode
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Agree

namespace Iris.Examples
open Iris.BI

section no_resources

abbrev FF0 : GFunctors := GFunctors.default

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

abbrev γ : GType := 1

abbrev FF1 : GFunctors := GFunctors.default.set γ (COFE.constOF (Agree (LeibnizO String)))

@[simp]
def MyAg (S : String) : Agree (LeibnizO String) := ⟨[⟨S⟩], by simp⟩

@[simp]
def MyR (S : String) : IResUR FF1
| 1, 0 => some (MyAg S)
| _, _ => none

theorem MyR_always_invalid (S₁ S₂ : String) (Hne : S₁ ≠ S₂) (n : Nat) : ¬✓{n} MyR S₁ • MyR S₂ := by
  simp only [CMRA.ValidN, CMRA.op, MyR, MyAg, Classical.not_forall]
  refine ⟨γ, 0, fun H => ?_⟩
  exact Hne <| LeibnizO.dist_inj <| Agree.toAgree_op_validN_iff_dist.mp H

def AgreeString (S : String) : IProp FF1 := UPred.ownM (MyR S)

example : AgreeString "I <3 iris-lean!" ⊢ (AgreeString "I don't :<" -∗ False) := by
  iintro H H2
  istop
  apply (UPred.ownM_op _ _).2.trans    -- Combine ghost state
  apply (UPred.ownM_valid _).trans     -- Reduce to invalidity
  apply UPred.ownM_always_invalid_elim -- The resource is invalid
  apply MyR_always_invalid; simp       -- Simplify

end const_agree
end Iris.Examples
