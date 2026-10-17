module

import Iris.ProofMode
public import ITree.Effects.Empty
public import IrisITree.Core.Wpi

public section

namespace IrisITree

open Iris BI ITree Effects

section handler

variable {PROP : Type _} [BI PROP]

/-- The canonical handler for the empty event type. -/
def emptyH : IHandler PROP emptyE where
  ihandle := by intro i; cases i
  ihandle_mono := by iintro %i; cases i

instance emptyH_sequential : Sequential (PROP := PROP) emptyH := by
  constructor; iintro %i; cases i

end handler

def insert_emptyE {E R} (t : ITree E R) : ITree (E ⊕ₑ emptyE) R :=
  ITree.interp (fun i => E.trigger i) t

end IrisITree
