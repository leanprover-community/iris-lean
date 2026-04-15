/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

@[expose] public section

namespace Nat

theorem eq_of_not_lt_not_lt {a b : Nat} : ¬(a < b) → ¬(b < a) → a = b := by
  intro h_nlt_ab h_nlt_ba
  let h_ge_ab := Nat.ge_of_not_lt h_nlt_ab
  let eq_or_lt := Nat.eq_or_lt_of_le h_ge_ab
  cases eq_or_lt
  case inl h =>
    rw [h]
  case inr =>
    contradiction

def iter {A : Type} (n : Nat) (f : A → A) (x : A) : A := Nat.rec x (fun _ => f) n

@[simp]
theorem iter_zero {A : Type} (f : A → A) (x : A) :
  iter 0 f x = x := by simp [iter]; rfl

@[simp]
theorem iter_succ {A : Type} (n : Nat) (f : A → A) (x : A) :
  iter (n + 1) f x = f (iter n f x) := by simp [iter]

theorem iter_add {A : Type} (n1 n2 : Nat) (f : A → A) (x : A) :
  iter (n1 + n2) f x = iter n1 f (iter n2 f x) := by
  induction n1 with
  | zero => simp only [iter, Nat.zero_add]; rfl
  | succ n IH =>
    rw [show n + 1 + n2 = (n + n2) + 1 by omega]
    simp [IH]

end Nat
