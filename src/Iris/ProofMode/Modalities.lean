/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Michael Sammler
-/
import Iris.BI

namespace Iris.ProofMode
open Iris.BI

inductive ModalityAction (PROP1 : Type u) : Type u → Type (u + 1) where
| isEmpty {PROP2} : ModalityAction PROP1 PROP2
| forall : (PROP1 → Prop) → ModalityAction PROP1 PROP1
| transform {PROP2} : (PROP2 → PROP1 → Prop) → ModalityAction PROP1 PROP2
| clear {PROP2} : ModalityAction PROP1 PROP2
| id : ModalityAction PROP1 PROP1

namespace ModalityAction

variable [BI PROP1] [h2 : BI PROP2] (s : ModalityAction PROP1 PROP2)

@[simp]
def action_spec (p : Bool) : (PROP1 → PROP2) → Prop :=
  match s, h2 with
  | .isEmpty, _ => λ _ => True
  | .forall C, _ => λ M =>
      (∀ P, C P → iprop(□?p P) ⊢ M iprop(□?p P))
      -- For p = true, Iris Rocq also has the following condition, but we don't need it:
      -- ∧ (∀ P Q, iprop(M P ∧ M Q) ⊢ M iprop(P ∧ Q))
  | .transform C, _ => λ M =>
      (∀ P Q, C P Q → iprop(□?p P) ⊢ M iprop(□?p Q))
      -- For p = true, Iris Rocq also has the following condition, but we don't need it:
      -- ∧ (∀ P Q, iprop(M P ∧ M Q) ⊢ M iprop(P ∧ Q))
  | .clear, _ => λ M => if p then True else ∀ P, Absorbing (M P)
  | .id, _ => λ M => ∀ P, iprop(□?p P) ⊢ M (iprop(□?p P))

end ModalityAction

structure Modality PROP1 PROP2 [BI PROP1] [BI PROP2] where
  M : PROP1 → PROP2
  action : Bool → ModalityAction PROP1 PROP2
  spec : ∀ p, (action p).action_spec p M
  emp : iprop(emp) ⊢ M iprop(emp)
  mono : ∀ {P Q}, (P ⊢ Q) → M P ⊢ M Q
  sep : ∀ {P Q}, iprop(M P ∗ M Q) ⊢ M iprop(P ∗ Q)

def modality_id [BI PROP] : Modality PROP PROP where
  M := id
  action _ := .id
  spec := by simp
  emp := by simp
  mono := by simp
  sep := by simp
