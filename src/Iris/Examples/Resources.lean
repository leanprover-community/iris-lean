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

abbrev FF0 : GFunctors := #[]

local instance : IsGFunctors FF0 := by
  intro i; exfalso; cases i.2

-- A proof with no resources
example (P Q : IProp FF0) : P ∗ Q ⊢ ⌜True ⌝ := by
  iintro ⟨HP, HQ⟩
  ipure_intro
  trivial

example (P Q : IProp FF0) : P ∗ Q ⊢ P := by
  iintro ⟨HP, HQ⟩
  iexact HP

end no_resources



section const_agree

abbrev FF1 : GFunctors := #[COFE.constOF (Agree (LeibnizO String))]
abbrev γ : GId FF1 := ⟨0, Nat.zero_lt_succ _⟩
theorem HγE  (i : GId FF1) : i = γ := by unfold γ; cases i; congr; apply Nat.lt_one_iff.mp; trivial
theorem HγLookup : FF1[γ] = COFE.constOF (Agree (LeibnizO String)) := rfl
local instance : IsGFunctors FF1 := fun i => by rw [HγE i, HγLookup]; infer_instance

@[simp]
def MyAg (S : String) : Agree (LeibnizO String) := ⟨[⟨S⟩], by simp⟩

@[simp]
def MyR (S : String) : IResUR FF1 := fun i => fun _ => some (HγE i ▸ MyAg S)

theorem MyR_always_invalid (S₁ S₂ : String) (Hne : S₁ ≠ S₂) (n : Nat) : ¬✓{n} MyR S₁ • MyR S₂ := by

  simp [CMRA.op, CMRA.ValidN] -- , optionOp]
  exists γ, ⟨0⟩
  rw [← HγE ⟨Nat.zero, Nat.le.refl⟩]
  simp [instIsGFunctorsFF1, CMRA.ValidN, CMRA.op, Agree.op, Agree.validN,
        instCOFELeibnizO, COFE.ofDiscrete, OFE.ofDiscrete, optionOp, optionValidN]
  exact fun a => id (Ne.symm Hne)

def AgreeString (S : String) : IProp (FF1) := UPred.ownM (MyR S)

example : AgreeString "I <3 iris-lean!" ⊢ (AgreeString "I don't :<" -∗ False) := by
  iintro H H2
  istop
  apply UPred.uPred_entails_preorder.trans (UPred.ownM_op _ _).2 -- Combine ghost state
  apply UPred.uPred_entails_preorder.trans (UPred.ownM_valid _)  -- Reduce to invalidity
  apply UPred.ownM_always_invalid_elim                           -- The resource is invalid
  apply MyR_always_invalid; simp                                 -- Simplify

end const_agree



end Iris.Examples
