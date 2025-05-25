/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI

namespace Iris.ProofMode
open Iris.BI

inductive ModalityAction (PROP1 PROP2 : Type _) : Type _ where
| MIEnvIsEmpty   : ModalityAction PROP1 PROP2
| MIEnvForall    : PROP1 = PROP2 → (PROP1 → Prop) → ModalityAction PROP1 PROP2
| MIEnvTransform : (PROP2 → PROP1 → Prop) → ModalityAction PROP1 PROP2
| MIEnvClear     : ModalityAction PROP1 PROP2
| MIEnvId        : PROP1 = PROP2 → ModalityAction PROP1 PROP2
export ModalityAction (MIEnvIsEmpty MIEnvForall MIEnvTransform MIEnvClear MIEnvId)

namespace ModalityAction

variable {PROP1 PROP2 : Type _} [BI PROP1] [BI PROP2] (s : ModalityAction PROP1 PROP2)

@[simp]
def intuitionistic_action_spec (M : PROP1 → PROP2) : Prop :=
  match s with
  | .MIEnvIsEmpty => True
  | .MIEnvForall Hconv C =>
      (∀ P, C P → iprop(□ P) ⊢ Hconv ▸ M iprop(□ P)) ∧
      (∀ P Q, iprop(M P ∧ M Q) ⊢ M iprop(P ∧ Q))
  | .MIEnvTransform C =>
      (∀ P Q, C P Q → iprop(□ P) ⊢ M iprop(□ Q)) ∧
      (∀ P Q, iprop(M P ∧ M Q) ⊢ M iprop(P ∧ Q))
  | .MIEnvClear => True
  | .MIEnvId H => ∀ P, iprop(□ P) ⊢ M (H ▸ iprop(□ P))

@[simp]
def spatial_action_spec (M : PROP1 → PROP2) : Prop :=
  match s with
  | .MIEnvIsEmpty => True
  | .MIEnvForall Hconv C => ∀ P, C P → P ⊢ Hconv ▸ M P
  | .MIEnvTransform C => ∀ P Q, C P Q → P ⊢ M Q
  | .MIEnvClear => ∀ P, Absorbing (M P)
  | .MIEnvId Hconv => ∀ P, P ⊢ (Hconv ▸ M P)

end ModalityAction

class IsModal {PROP1 PROP2 : Type _} [BI PROP1] [BI PROP2] (M : PROP1 → PROP2)
    (iaction saction : ModalityAction PROP1 PROP2) where
  spec_intuitionistic : iaction.intuitionistic_action_spec M
  spec_spatial : saction.spatial_action_spec M
  emp : iprop(emp) ⊢ M iprop(emp)
  mono : ∀ {P Q}, (P ⊢ Q) → M P ⊢ M Q
  sep : ∀ {P Q}, iprop(M P ∗ M Q) ⊢ M iprop(P ∗ Q)

instance {PROP : Type _} [BI PROP] : IsModal (PROP1 := PROP) id (MIEnvId rfl) (MIEnvId rfl) := by
  constructor <;> simp
