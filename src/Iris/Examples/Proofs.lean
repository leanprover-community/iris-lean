/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI
import Iris.Proofmode

namespace Iris.Examples
open Iris.BI

theorem proof_example_1 [BI PROP] (P Q R : PROP) (Φ : α → PROP) :
  P ∗ Q ∗ □ R ⊢ □ (R -∗ ∃ x, Φ x) -∗ ∃ x, Φ x ∗ P ∗ Q
:= by
  iintro ⟨HP, HQ, □HR⟩ □HRΦ
  ispecialize HRΦ HR as HΦ
  icases HΦ with ⟨x, HΦ⟩
  iexists x
  isplit r
  · iassumption
  isplit l [HP]
  · iexact HP
  · iexact HQ

end Iris.Examples
