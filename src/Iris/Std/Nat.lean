/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
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

end Nat
