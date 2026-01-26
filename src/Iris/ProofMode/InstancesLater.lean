/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode.Classes
import Iris.Std.TC

namespace Iris.ProofMode
open Iris.BI Iris.Std

instance fromAssumption_later [BI PROP] (p : Bool) ioP (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(▷ Q) where
  from_assumption := h.1.trans later_intro
