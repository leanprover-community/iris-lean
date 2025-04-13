/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI
import Iris.ProofMode
import Iris.Algebra.iProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Agree

namespace Iris.Examples
open Iris.BI

section no_resources

abbrev FF0 : gFunctors := #[]

local instance : IsGFunctors FF0 := by
  intro i; exfalso; cases i.2

-- A proof with no resources
example (P Q : iProp FF0) : P ∗ Q ⊢ ⌜True ⌝ := by
  iintro ⟨ HP, HQ ⟩
  ipure_intro
  trivial

example (P Q : iProp FF0) : P ∗ Q ⊢ P := by
  iintro ⟨ HP, HQ ⟩
  iexact HP

end no_resources



section const_agree

abbrev FF1 : gFunctors := #[COFE.OFunctor.constOF (Agree (LeibnizO String))]
abbrev γ : gid FF1 := ⟨ 0, Nat.zero_lt_succ _⟩
theorem HγE  (i : gid FF1) : i = γ := by unfold γ; cases i; congr; apply Nat.lt_one_iff.mp; trivial
theorem HγLookup : FF1[γ] = COFE.OFunctor.constOF (Agree (LeibnizO String)) := by rfl
local instance : IsGFunctors FF1 := fun i => by rw [HγE i, HγLookup]; infer_instance

@[simp]
def MyAg (S : String) : Agree (LeibnizO String) := ⟨ [ ⟨ S ⟩ ], by simp ⟩

@[simp]
def MyR (S : String) : iResUR FF1 := ⟨ fun i => ⟨ fun _ => ⟨ some (HγE i ▸ MyAg S) ⟩ ⟩ ⟩

theorem MyR_always_invalid (S₁ S₂ : String) (Hne : S₁ ≠ S₂) (n : Nat) : ¬✓{n} MyR S₁ • MyR S₂ := by
  simp [CMRA.op, discrete_funO.discrete_fun_op, CMRA.ValidN, discrete_funO.discrete_fun_validN]
  apply And.intro ⟨1, Nat.one_pos⟩
  exists γ
  rw [← HγE ⟨Nat.zero, Nat.le.refl⟩]
  simp [instIsGFunctorsFF1, CMRA.ValidN, CMRA.op, Agree.op, Agree.validN,
        instCOFELeibnizO, COFE.ofDiscrete, OFE.ofDiscrete]
  intro H; exfalso; apply Hne H

def AgreeString (S : String) : iProp (FF1) := uPred.ownM (MyR S)

example : AgreeString "I <3 iris-lean!" ⊢ (AgreeString "I don't :<" -∗ False) := by
  iintro H H2
  istop
  apply uPred.uPred_entails_preorder.trans (uPred.ownM_op _ _).2 -- Combine ghost state
  apply uPred.uPred_entails_preorder.trans (uPred.ownM_valid _)  -- Reduce to invalidity
  apply uPred.ownM_always_invalid_elim                           -- The resource is invalid
  apply MyR_always_invalid; simp                                 -- Simplify

end const_agree



end Iris.Examples
