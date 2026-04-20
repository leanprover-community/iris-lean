module

@[expose] public section

namespace Relation

/-- Composes a relation `n` times -/
inductive iterate {α : Type _} (R : α → α → Prop) : Nat → α → α → Prop where
| rfl (x : α): iterate R 0 x x
| tail (y: α) {n : Nat}{x z : α} : iterate R n x y → R y z → iterate R (n+1) x z

attribute [simp] iterate.rfl iterate.tail
