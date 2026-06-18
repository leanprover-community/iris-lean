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
    NonExpansive (f ∘ g) := by
      solve_ne
      simp only [Function.comp_apply]
      solve_ne

example (y : β) : NonExpansive (fun _ : α => y) := by solve_ne

/-! ## `Contractive` -/

example [BILaterContractive PROP] : Contractive (fun P : PROP => iprop(▷ P ∧ Q)) := by
  solve_ne

example [BILaterContractive PROP] : Contractive (fun P : PROP => iprop(Q ∗ ▷ (P -∗ Q))) := by
  solve_ne

example [BILaterContractive PROP] : Contractive (fun P : PROP => iprop(▷ (P ∨ Q) → Q)) := by
  solve_ne

-- `solve_ne` also crosses `▷` when the hypothesis is a plain `Dist`
example [BILaterContractive PROP] {n} {P₁ P₂ : PROP} (h : P₁ ≡{n}≡ P₂) :
    iprop(▷ P₁ ∗ Q) ≡{n}≡ iprop(▷ P₂ ∗ Q) := by solve_ne

/-! ## Failure behavior -/

-- a goal that does not hold fails with a clean error showing the stuck subgoal
/--
error: unsolved goals
PROP : Type
inst✝² : BI PROP
Q R : PROP
α β : Type
inst✝¹ : OFE α
inst✝ : OFE β
n✝ : Nat
x✝ y✝ : PROP
a✝ : DistLater n✝ x✝ y✝
⊢ x✝ ≡{n✝}≡ y✝
-/
#guard_msgs in
example : Contractive (fun P : PROP => P) := by solve_ne

/-! ## `@[ne_congr]` priorities

When several `@[ne_congr]` lemmas match the same goal, `solve_ne` tries them from
highest to lowest priority. Each wrapper below has a "good" congruence lemma (reduces to
the argument distance, closeable by hypothesis) and a "bad" one (matches the same goal
but leaves an unsolvable `False` subgoal); which one wins is determined purely by the
priorities. -/

section Priority
variable {n : Nat} {P₁ P₂ : PROP}

-- irreducible so that `solve_ne` cannot close the goal directly with the hypothesis and
-- is forced to go through a `@[ne_congr]` congruence lemma
@[irreducible] private def wrapHi (P : PROP) : PROP := P
@[irreducible] private def wrapLo (P : PROP) : PROP := P

@[ne_congr 2000] private theorem wrapHi_good (h : P₁ ≡{n}≡ P₂) : wrapHi P₁ ≡{n}≡ wrapHi P₂ := by
  with_unfolding_all exact h
@[ne_congr 100]  private theorem wrapHi_bad  (h : False)      : wrapHi P₁ ≡{n}≡ wrapHi P₂ := h.elim

-- the higher-priority good rule is tried first, so `solve_ne` succeeds
example (h : P₁ ≡{n}≡ P₂) : wrapHi P₁ ≡{n}≡ wrapHi P₂ := by solve_ne

@[ne_congr 100]  private theorem wrapLo_good (h : P₁ ≡{n}≡ P₂) : wrapLo P₁ ≡{n}≡ wrapLo P₂ := by
  with_unfolding_all exact h
@[ne_congr 2000] private theorem wrapLo_bad  (h : False)      : wrapLo P₁ ≡{n}≡ wrapLo P₂ := h.elim

-- with the priorities swapped, the bad rule wins and `solve_ne` gets stuck on `False`
/--
error: unsolved goals
PROP : Type
inst✝² : BI PROP
Q R : PROP
α β : Type
inst✝¹ : OFE α
inst✝ : OFE β
n : Nat
P₁ P₂ : PROP
h : P₁ ≡{n}≡ P₂
⊢ False
-/
#guard_msgs in
example (h : P₁ ≡{n}≡ P₂) : wrapLo P₁ ≡{n}≡ wrapLo P₂ := by solve_ne

end Priority

end Iris.Tests.SolveNE
