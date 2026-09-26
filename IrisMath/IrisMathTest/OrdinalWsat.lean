/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IrisMath.TimeCredits

/-! Tests: world satisfaction, fancy updates and time credits over ordinal step-indices. -/

@[expose] public noncomputable section

namespace Iris.Transfinite.Test

open Iris BI

abbrev OrdSI := Ordinal.{1}
local stepindex OrdSI

/-- Ghost state for invariants and time credits, over `SI = Ordinal.{1}`. Ghost state in `Type` is
lifted with `ULiftOF`. -/
def GF : BundledGFunctors.{0, 2} := fun n =>
  match n with
  | 0 => ⟨InvMapF, inferInstance⟩
  | 1 => ⟨ULiftOF.{2} (constOF CoPsetDisjL), inferInstance⟩
  | 2 => ⟨ULiftOF.{2} (constOF (DisjointLeibnizSet PosSet)), inferInstance⟩
  | 3 => ⟨constOFU.{2} (Auth (OrdCam.{0} OrdSI)), inferInstance⟩
  | _ => ⟨ULiftOF.{2} (constOF Unit), inferInstance⟩

instance : WsatGpreS GF where
  inv := .ofEq 0 (by unfold GF; rfl)
  enabled := .ofEqLift 1 (by unfold GF; rfl)
  disabled := .ofEqLift 2 (by unfold GF; rfl)

/-- Soundness of the transfinite fancy update at ordinal step-indices. -/
example (φ : Prop) (h : ∀ (_ : WsatGS GF), ⊢ |={⊤,⊤}=> (⌜φ⌝ : IProp GF)) : φ :=
  UPred.pure_soundness (fupd_plain_soundness ⊤ ⊤ h)

instance : TcGS.{0} GF where
  elem := .ofEq 3 (by unfold GF; rfl)
  name := 0

example : Persistent (tc (GF := GF) 0) := inferInstance

end Iris.Transfinite.Test
