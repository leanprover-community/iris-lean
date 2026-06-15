/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.BI
meta import Iris.Algebra.SolveNE

@[expose] public section

namespace Iris.Tests.SolveNE
open Iris BI OFE

/-! This file contains tests for the `solve_ne` and `solve_contractive` tactics. -/

variable {PROP : Type} [BI PROP] (Q R : PROP) {α β : Type} [OFE α] [OFE β]

/-! ## Raw distance goals -/

example {n} {P₁ P₂ : PROP} (h : P₁ ≡{n}≡ P₂) : iprop(P₁ ∗ Q) ≡{n}≡ iprop(P₂ ∗ Q) := by
  solve_ne

example {n} {P₁ P₂ : PROP} (h : P₁ ≡{n}≡ P₂) : iprop(Q -∗ P₁) ≡{n}≡ iprop(Q -∗ P₂) := by
  solve_ne

-- the symmetrized hypothesis is also used
example {n} {P₁ P₂ : PROP} (h : P₂ ≡{n}≡ P₁) : iprop(P₁ ∨ Q) ≡{n}≡ iprop(P₂ ∨ Q) := by
  solve_ne

/-! ## `NonExpansive` over BI connectives -/

example : NonExpansive (fun P : PROP => iprop(P ∗ Q → ▷ P)) := by solve_ne

example : NonExpansive (fun P : PROP => iprop((P -∗ Q) ∨ <pers> (Q ∧ P))) := by solve_ne

-- binders, via the `@[ne_congr]` lemmas `forall_ne`/`exists_ne`
example (Φ : Nat → PROP) : NonExpansive (fun P : PROP => iprop(∀ x, Φ x ∗ P)) := by solve_ne

example (Φ : Nat → PROP) : NonExpansive (fun P : PROP => iprop(∃ x, Φ x -∗ P)) := by solve_ne

-- derived connectives, via registered instances (`iff_ne`) or the unfolding fallback
example : NonExpansive (fun P : PROP => iprop(P ↔ Q)) := by solve_ne

example : NonExpansive (fun P : PROP => iprop(<affine> (P ∗ Q))) := by solve_ne

/-! ## `NonExpansive₂` -/

example : NonExpansive₂ (fun P Q' : PROP => iprop((P → Q') ∗ R)) := by solve_ne

example : NonExpansive₂ (fun P Q' : PROP => iprop((P ↔ Q') ∗ R)) := by solve_ne

/-! ## OFE constructions -/

example : NonExpansive (fun x : α => (x, some x)) := by solve_ne

example (f : α → β) [NonExpansive f] (g : β → α) [NonExpansive g] :
    NonExpansive (fun x => f (g x)) := by solve_ne

example (f : α → β) [NonExpansive f] (g : β → α) [NonExpansive g] :
    NonExpansive (f ∘ g) := by solve_ne

example (y : β) : NonExpansive (fun _ : α => y) := by solve_ne

/-! ## `Contractive` -/

example [BILaterContractive PROP] : Contractive (fun P : PROP => iprop(▷ P ∧ Q)) := by
  solve_contractive

example [BILaterContractive PROP] : Contractive (fun P : PROP => iprop(Q ∗ ▷ (P -∗ Q))) := by
  solve_contractive

example [BILaterContractive PROP] : Contractive (fun P : PROP => iprop(▷ (P ∨ Q) → Q)) := by
  solve_contractive

-- `solve_ne` also crosses `▷` when the hypothesis is a plain `Dist`
example [BILaterContractive PROP] {n} {P₁ P₂ : PROP} (h : P₁ ≡{n}≡ P₂) :
    iprop(▷ P₁ ∗ Q) ≡{n}≡ iprop(▷ P₂ ∗ Q) := by solve_ne

/-! ## Failure behavior -/

-- a goal that does not hold fails with a clean error showing the stuck subgoal
/--
error: solve_ne: cannot solve
  x✝ ≡{n✝}≡ y✝
(for functions of arity ≥ 3 or binders, register a congruence lemma with `@[ne_congr]`)
-/
#guard_msgs in
example : Contractive (fun P : PROP => P) := by solve_contractive

end Iris.Tests.SolveNE
