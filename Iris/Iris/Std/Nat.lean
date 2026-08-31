/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init

@[expose] public section

namespace Nat

theorem repeat_add {A : Type _} (n1 n2 : Nat) (f : A → A) (x : A) :
    (n1 + n2).repeat f x = n1.repeat f (n2.repeat f x) := by
  induction n1 with
  | zero => simp [«repeat»]
  | succ n1 IH => simp [show n1 + 1 + n2 = (n1 + n2) + 1 by omega, «repeat», ← IH]

theorem repeat_apply_comm (f : α → α) (k : Nat) (x : α) :
    Nat.repeat f k (f x) = f (Nat.repeat f k x) := by
  induction k with
  | zero => rfl
  | succ _ IH => exact congrArg f IH

theorem repeat_fixed (f : α → α) {x : α} (H : x = f x) : ∀ k, x = Nat.repeat f k x
  | 0 => rfl
  | k + 1 => H.trans (congrArg f (repeat_fixed f H k))

/-- If `f` respects an equivalence `R` and is `R`-related to `g` pointwise, then iterating `f`
and `g` gives `R`-related results. -/
theorem repeat_rel {R : α → α → Prop} (hR : Equivalence R) {f g : α → α}
    (hf : ∀ {x y}, R x y → R (f x) (f y)) (hfg : ∀ z, R (f z) (g z)) :
    ∀ k z, R (Nat.repeat f k z) (Nat.repeat g k z)
  | 0, _ => hR.refl _
  | k + 1, z => hR.trans (hf (repeat_rel hR hf hfg k z)) (hfg _)

theorem repeat_ind (f : α → α) {P : α → Prop} (Hind : ∀ x, P x → P (f x)) {x} (Hx : P x) :
    ∀ k, P (Nat.repeat f k x)
  | 0 => Hx
  | k + 1 => Hind _ (repeat_ind f Hind Hx k)

end Nat
