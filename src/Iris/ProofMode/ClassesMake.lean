/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode.SynthInstance

namespace Iris.ProofMode
open Iris.BI

/-- The class [MakeLaterN n P Q] is used to compute `lP := ▷^n P`. -/
class MakeLaterN [BI PROP] (n : Nat) (P : PROP) (lP : outParam PROP) where
  make_laterN : ▷^[n] P ⊣⊢ lP
export MakeLaterN (make_laterN)
