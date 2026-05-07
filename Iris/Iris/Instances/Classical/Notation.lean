/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

public import Iris.Instances.Classical.Instance
public meta import Iris.BI.Notation

@[expose] public section

namespace Iris.Instances.Classical
open Iris.Instances.Data

def maps_to (l : Nat) (v : Val) : HeapProp Val :=
  fun state => state l = result v

/-- State that a heap cell contains a certain value. -/
syntax:52 (name := bi_pointsTo) term:53 " ↦ " term:53 : term

open Lean Lean.Elab Lean.Elab.Term Iris.BI in
@[term_elab Iris.Instances.Classical.bi_pointsTo]
meta def elabBiPointsTo : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let l : Term := ⟨stx[0]⟩
  let v : Term := ⟨stx[2]⟩
  elabTerm (← `(maps_to $l $v)) expectedType?

delab_rule maps_to
  | `($_ $l $v) => `(iprop($l ↦ $v))

end Iris.Instances.Classical
