/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

@[expose] public section

namespace Nat

theorem repeat_add {A : Type} (n1 n2 : Nat) (f : A → A) (x : A) :
    (n1 + n2).repeat f x = n1.repeat f (n2.repeat f x) := by
  induction n1 with
  | zero => simp [«repeat»]
  | succ n1 IH => simp [show n1 + 1 + n2 = (n1 + n2) + 1 by omega, «repeat», ← IH]

end Nat
