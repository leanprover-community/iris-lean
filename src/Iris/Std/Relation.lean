module

public import Iris.Std.FromMathlib

open FromMathlib

public section

namespace Relation

/-- Composes a relation `n` times -/
inductive Iterate {α : Type _} (R : α → α → Prop) : Nat → α → α → Prop where
| rfl (x : α): Iterate R 0 x x
| tail (y: α) {n : Nat}{x z : α} : Iterate R n x y → R y z → Iterate R (n+1) x z

attribute [simp] Iterate.rfl Iterate.tail

theorem ReflTrans_iff_exists_iterate {α : Type _} {R : α → α → Prop} :
    ∀ {x y},
    Relation.ReflTransGen R x y ↔ ∃ n, Iterate R n x y := by
  intros x y
  constructor
  · intros rtcR
    induction rtcR with
    | refl =>
      exists 0; constructor
    | tail rtcMid Rlast IH =>
      obtain ⟨n, h⟩ := IH
      exists (n+1)
      apply Relation.Iterate.tail _ h Rlast
  · rintro ⟨n, itR⟩
    induction itR with
    | rfl => constructor
    | tail z itMid Rlast IH =>
      apply Relation.ReflTransGen.tail IH Rlast

theorem Iterate.head (hab : r a b) (hbc : Iterate r n b c) : Iterate r (n+1) a c :=
  match hbc with
  | .rfl x => .tail a (.rfl a) hab
  | .tail y hcd hac =>
    .tail y (head hab hcd) hac

theorem Iterate.head_induction_on {b : α}
  {motive : ∀ (n : Nat) (a : α), Iterate r n a b → Prop}
  (rfl : motive _ _ (.rfl b))
  (head : ∀ {n a } c (h' : r a c) (h : Iterate r n c b), motive _ _ h → motive _ _ (h.head h'))
  {n : Nat} {a : α} (h : Iterate r n a b) :
    motive _ _ h := by
  induction h with
  | rfl => exact rfl
  | tail y hxy hyz ih =>
    apply ih
    · exact head _ hyz _ rfl
    · exact fun _ h1 h2 ↦ head _ h1 (h2.tail _ hyz)
