module

public import Iris.Std.FromMathlib

open FromMathlib

public section

namespace Relation

/-- Composes a relation `n` times -/
inductive iterate {α : Type _} (R : α → α → Prop) : Nat → α → α → Prop where
| rfl (x : α): iterate R 0 x x
| tail (y: α) {n : Nat}{x z : α} : iterate R n x y → R y z → iterate R (n+1) x z

attribute [simp] iterate.rfl iterate.tail

theorem ReflTrans_iff_exists_iterate {α : Type _} {R : α → α → Prop} :
    ∀ {x y},
    Relation.ReflTransGen R x y ↔ ∃ n, Relation.iterate R n x y := by
  intros x y
  constructor
  · intros rtcR
    induction rtcR with
    | refl =>
      exists 0; constructor
    | tail rtcMid Rlast IH =>
      obtain ⟨n, h⟩ := IH
      exists (n+1)
      apply Relation.iterate.tail _ h Rlast
  · rintro ⟨n, itR⟩
    induction itR with
    | rfl => constructor
    | tail z itMid Rlast IH =>
      apply Relation.ReflTransGen.tail IH Rlast
