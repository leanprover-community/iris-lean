/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.HeapLang
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Tactics.Inductive

@[expose] public section
namespace Iris.Examples.Inductive

open Iris Iris.HeapLang

instance : COFE Loc := .ofDiscrete _
instance : OFE.Discrete Loc := ⟨id⟩

instance : COFE Val := .ofDiscrete _
instance : OFE.Discrete Val := ⟨id⟩

def NIL : Val := hl_val(none())
def CONS (v : Val) (l : Loc) : Val := hl_val(some((&v, #l)))

variable [inst : HeapLangGS hlc GF]

iinductive isList : Loc → List Val → IProp GF where
  | nil (l : Loc) : l ↦ NIL -∗ isList l []
  | cons (l tl : Loc) (v : Val) (vs : List Val) :
      l ↦ CONS v tl -∗ isList tl vs -∗ isList l (v :: vs)

end Iris.Examples.Inductive
