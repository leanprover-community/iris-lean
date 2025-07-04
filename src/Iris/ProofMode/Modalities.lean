/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI

namespace Iris.ProofMode
open Iris.BI

inductive ModalityAction (PROP1 PROP2 : Type u) : Type u where
| isEmpty   : ModalityAction PROP1 PROP2
| forall    : PROP1 = PROP2 → (PROP1 → Prop) → ModalityAction PROP1 PROP2
| transform : (PROP2 → PROP1 → Prop) → ModalityAction PROP1 PROP2
| clear     : ModalityAction PROP1 PROP2
| id        : PROP1 = PROP2 → ModalityAction PROP1 PROP2

namespace ModalityAction

variable [BI PROP1] [BI PROP2] (s : ModalityAction PROP1 PROP2)

@[simp]
def intuitionistic_action_spec (M : PROP1 → PROP2) : Prop :=
  match s with
  | .isEmpty => True
  | .forall Hconv C =>
      (∀ P, C P → iprop(□ P) ⊢ Hconv ▸ M iprop(□ P)) ∧
      (∀ P Q, iprop(M P ∧ M Q) ⊢ M iprop(P ∧ Q))
  | .transform C =>
      (∀ P Q, C P Q → iprop(□ P) ⊢ M iprop(□ Q)) ∧
      (∀ P Q, iprop(M P ∧ M Q) ⊢ M iprop(P ∧ Q))
  | .clear => True
  | .id H => ∀ P, iprop(□ P) ⊢ M (H ▸ iprop(□ P))

@[simp]
def spatial_action_spec (M : PROP1 → PROP2) : Prop :=
  match s with
  | .isEmpty => True
  | .forall Hconv C => ∀ P, C P → P ⊢ Hconv ▸ M P
  | .transform C => ∀ P Q, C P Q → P ⊢ M Q
  | .clear => ∀ P, Absorbing (M P)
  | .id Hconv => ∀ P, P ⊢ (Hconv ▸ M P)

end ModalityAction

class IsModal [BI PROP1] [BI PROP2] (M : PROP1 → PROP2)
    (iaction saction : ModalityAction PROP1 PROP2) where
  spec_intuitionistic : iaction.intuitionistic_action_spec M
  spec_spatial : saction.spatial_action_spec M
  emp : iprop(emp) ⊢ M iprop(emp)
  mono : ∀ {P Q}, (P ⊢ Q) → M P ⊢ M Q
  sep : ∀ {P Q}, iprop(M P ∗ M Q) ⊢ M iprop(P ∗ Q)

instance [BI PROP] : IsModal (PROP1 := PROP) id (.id rfl) (.id rfl) := by
  constructor <;> simp
