/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProofMode
public import Iris.Algebra.IProp
public import Iris.Algebra.Auth
public import Iris.Instances.UPred.Instance
public import Iris.Instances.IProp.Instance
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.Invariants
public import Iris.Std.HeapInstances

@[expose] public section

namespace Iris.Examples.ClosedProofs
open Iris.BI COFE HeapView Auth Std.LawfulSet

/-!
This file shows how to obtain closed (pure Lean) propositions by taking a détour
through the Iris logic in the presence of circular resources such as invariants.

`GF` is a family of GFunctors that specifies the input functor for IProp. Each slot is
an indexed functor contributing one resource algebra: the first slot carries `InvMapF` (the
invariant map, which makes `IProp` self-referential), slots 1–2 carry the invariant
mask bookkeeping, and slot 3 carries later credits. Additional user resources can be
added at higher indices together with a matching `GpreS` instance.

`pure_soundness` converts a proof of `⊢ ⌜P⌝` in the Iris logic into the plain Lean
proposition `P`. The `step_fupdN_soundness_no_lc'` wrapper accounts for the fancy
update steps required to allocate invariants.
-/
section proof

noncomputable def GF : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF, by infer_instance⟩
  | 1  => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3  => ⟨AuthURF (F := PNat) (constOF Credit), by infer_instance⟩
  | _  => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS GF where
  inv := { τ := 0, transp := by unfold GF; rfl }
  enabled := { τ := 1, transp := by unfold GF; rfl }
  disabled := { τ := 2, transp := by unfold GF; rfl }

instance : LcGpreS GF where
  lc_elem := { τ := 3, transp := by unfold GF; rfl }

instance : InvGpreS GF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

example : True := by
  apply pure_soundness (PROP := IProp GF)
  iapply step_fupdN_soundness_no_lc' (m := 0) (n := 1)
  iintro %_ _
  simp only [Nat.repeat]
  icases inv_alloc nroot ⊤ iprop(True) $$ [] with >#Hinv
  · inext; ipure_intro; simp
  imod inv_acc ⊤ $$ Hinv with ⟨HP, Hcl⟩
  · rw [nclose_root]; exact subset_refl
  imod Hcl $$ HP with HP
  iapply fupd_mask_intro empty_subset
  iintro Hcl
  inext
  imod Hcl
  imodintro
  iintro _
  iexact HP

end proof

end Iris.Examples.ClosedProofs
