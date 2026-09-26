/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.LogicalStep
public import Iris.BI.Transfinite

@[expose] public section

/-! # Tests for the Transfinite Iris modalities -/

namespace IrisTest.Transfinite
open Iris BI Std

variable {SI : Type _} [instSI : SIdx SI]
local stepindex SI

variable [BI PROP] [BIFUpdate PROP]

/- `imod` eliminates `eventuallyN` in an `eventuallyN` goal. -/
example (E : CoPset) (n : Nat) (P Q : PROP) :
    eventuallyN n E P ⊢ (P -∗ Q) -∗ eventuallyN n E Q := by
  iintro HP HPQ
  imod HP
  iapply HPQ
  iexact HP

/- `imod` eliminates `gstep` in a `gstep` goal. -/
example (Ei E1 E2 : CoPset) (P Q : PROP) :
    gstep Ei E1 E2 P ⊢ (P -∗ Q) -∗ gstep Ei E1 E2 Q := by
  iintro HP HPQ
  imod HP
  iapply HPQ
  iexact HP

/- The big later is introduced by a later. -/
example (P : PROP) : ▷ P ⊢ ⧍ P := by
  iintro HP
  iapply later_bigLater
  iexact HP

end IrisTest.Transfinite
