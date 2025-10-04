/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI
import Iris.ProofMode
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Instances.IProp.Instance
import Iris.Algebra.Agree

namespace Iris.Examples
open Iris.BI COFE

/-
section no_resources

variable [UCMRA M]

-- A proof with no resources
example (P Q : UPred M) : P ∗ Q ⊢ ⌜True⌝ := by
  iintro ⟨HP, HQ⟩
  ipure_intro
  trivial

example (P Q : IProp FF0) : P ∗ Q ⊢ P := by
  iintro ⟨HP, HQ⟩
  iexact HP

end no_resources

section const_agree

abbrev γ : GType := 1

@[simp]
def MyAg (S : String) : (Option (Agree (LeibnizO String))) := some ⟨[⟨S⟩], by simp⟩

theorem MyR_always_invalid (S₁ S₂ : String) (Hne : S₁ ≠ S₂) (n : Nat) : ¬✓{n} MyAg S₁ • MyAg S₂ := by
  simp only [CMRA.ValidN, CMRA.op, MyAg, optionValidN, optionOp]
  exact (Hne <| LeibnizO.dist_inj <| Agree.toAgree_op_validN_iff_dist.mp ·)

def AgreeString (S : String) : UPred (Option (Agree (LeibnizO String))) := UPred.ownM (MyAg S)

example : AgreeString "I <3 iris-lean!" ⊢ (AgreeString "I don't :<" -∗ False) := by
  iintro H H2
  istop
  apply (UPred.ownM_op _ _).2.trans    -- Combine ghost state
  apply (UPred.ownM_valid _).trans     -- Reduce to invalidity
  apply UPred.ownM_always_invalid_elim -- The resource is invalid
  apply MyR_always_invalid; simp       -- Simplify

end const_agree




end Iris.Examples
-/
