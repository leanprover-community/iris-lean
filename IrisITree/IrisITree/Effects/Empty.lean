/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

import Iris.ProofMode
public import ITree.Effects.Empty
public import IrisITree.Core.Wpi

public section
namespace IrisITree

open Iris BI ITree Effects
variable {PROP : Type _} [BI PROP]

/-- The canonical handler for the empty event type. -/
def emptyH : IHandler PROP emptyE where
  ihandle i := nomatch i
  ihandle_mono i := nomatch i

instance emptyH_sequential : Sequential (PROP := PROP) emptyH := by
  refine ⟨fun i => nomatch i⟩

def insert_emptyE {E R} (t : ITree E R) : ITree (E ⊕ₑ emptyE) R :=
  ITree.interp (fun i => E.trigger i) t

end IrisITree
