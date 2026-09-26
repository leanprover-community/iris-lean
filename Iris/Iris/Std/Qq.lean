/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Qq
public import Iris.Init

@[expose] public section
open Qq Lean

instance : Inhabited (QuotedDefEq a b) := ⟨⟨⟩⟩

def instantiateMVarsQ' {u : Level} {α : Q(Sort u)} (e : Q($α)) : MetaM ((e' : Q($α)) ×' $e =Q $e') := do
  return ⟨← instantiateMVarsQ e, ⟨⟩⟩
