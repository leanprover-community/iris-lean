/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.View

open Iris


section auth_view_rel

variable (A : Type _) [UCMRA A]

abbrev auth_view_rel : view_rel A A :=
  fun n a b => b ≼{n} a ∧ ✓{n} a

instance : ViewRel (auth_view_rel A) where
  mono := sorry
  rel_validN := sorry
  rel_unit := sorry

end auth_view_rel

section auth

variable (F A : Type _) [UCMRA A] [DFractional F]

abbrev Auth := View F (auth_view_rel A)

-- #synth CMRA (Auth A F)

def auth_auth (dq : DFrac F) (a : A) : Auth F A := ●V{dq} a
def auth_frag (a : A) : Auth F A := ◯V a

notation "●{" dq "} " a => auth_auth dq a
notation "● " a => auth_auth (LeibnizO.mk <| DFracK.Own One.one) a
notation "◯ " b => auth_frag b

end auth
