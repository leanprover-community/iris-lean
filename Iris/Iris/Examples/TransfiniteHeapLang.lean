/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.HeapLang.TransfiniteProofMode
public import Iris.Instances.Lib.InvariantsTransfinite
public import Iris.Algebra.Lib.MonoNat
public import Iris.Examples.TransfiniteInvariants

/-! # Opening invariants in heap_lang with transfinite step-indices

This file ports the `heap_lang` examples of `theories/examples/transfinite.v` of Transfinite Iris:
loading from a location protected by an invariant (`invariants_transfinite`) and opening nested
invariants in a single program step (`invariants_transfinite_nested`). Since `▷` does not commute
with `∃` for transfinite step-indices, the contents of an opened invariant are destructed only
after `swp_step` has stripped the later.
-/

@[expose] public noncomputable section

universe u v

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Examples

open Iris Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Iris.Std Iris.BI LawfulSet

variable {GF : BundledGFunctors.{u}} [HeapLangTGS GF] (N : Namespace)

/-- Rocq: `invariants_transfinite`. -/
theorem invariants_transfinite (l : Loc) (Ψ : Val → IProp GF) (φ : Val → IProp GF) :
    ⊢ inv N iprop(∃ v, l ↦ some v ∗ Ψ v) -∗ ▷ (∀ v, True -∗ φ v) -∗
      Iris.Transfinite.wp .NotStuck ⊤ hl(!v(#l)) φ := by
  iintro #I Post
  -- move to the strong weakest precondition, which allows stripping one later
  iapply swp_wp (k := 1) rfl
  iapply swp_atomic (E₂ := ⊤ \ ↑N)
  imod inv_acc subset_top $$ I with ⟨H, Hclose⟩
  imodintro
  -- the step property of `swp` strips the later of the invariant contents
  iapply swp_step
  inext
  icases H with ⟨%v, Hl, HΨ⟩
  iapply swp_load $$ [Hl]
  · iexact Hl
  iintro Hl
  imod Hclose $$ [Hl HΨ] with -
  · inext
    iexists v
    iframe
  imodintro
  iapply Post $$ %v
  itrivial

/-! ## Nested invariants -/

theorem subset_diff_of_disjoint {E F G : CoPset} (h₁ : E ⊆ F) (h₂ : E ## G) : E ⊆ F \ G :=
  fun _ hp => LawfulSet.mem_diff.mpr ⟨h₁ _ hp, fun hg => h₂ _ ⟨hp, hg⟩⟩

section Nested

variable [E : ElemG GF (constOFU.{max u v} MonoNat)]

/-- The value stored at `l` is positive and at least the lower bound `γ` (Rocq: `Pos`). -/
def Pos (N : Namespace) (l : Loc) (γ : GName) : IProp GF :=
  inv N iprop(∃ n : Nat, l ↦ some hl_val(#(n : Int)) ∗ ⌜n > 0⌝ ∗
    iOwn (E := E) γ (ULift.up (◯MN (MaxNat.ofNat n))))

/-- Rocq: `L`. -/
def invL (l₁ : Loc) (γ : GName) : IProp GF :=
  inv (N.@"L") iprop(∃ m : Nat, l₁ ↦ some hl_val(#(m : Int)) ∗
    iOwn (E := E) γ (ULift.up (●MN (MaxNat.ofNat m))))

/-- Rocq: `R`. -/
def invR (l₂ : Loc) (γ : GName) : IProp GF :=
  inv (N.@"R") iprop(∃ l₂' : Loc, l₂ ↦ some hl_val(#l₂') ∗ Pos (N.@"I") l₂' γ)

instance Pos_persistent (N : Namespace) (l : Loc) (γ : GName) :
    Persistent (Pos (GF := GF) N l γ) := by
  unfold Pos; infer_instance

instance invL_persistent (l : Loc) (γ : GName) : Persistent (invL (GF := GF) N l γ) := by
  unfold invL; infer_instance

instance invR_persistent (l : Loc) (γ : GName) : Persistent (invR (GF := GF) N l γ) := by
  unfold invR; infer_instance

omit [HeapLangTGS GF] in
/-- Rocq: `mnat_own`. -/
theorem mnat_own (m n : Nat) (γ : GName) :
    ⊢ iOwn (E := E) γ (ULift.up (●MN (MaxNat.ofNat m))) -∗
      iOwn (E := E) γ (ULift.up (◯MN (MaxNat.ofNat n))) -∗ ⌜n ≤ m⌝ := by
  iintro Ha Hf
  ihave H := (iOwn_op (E := E) (γ := γ) (a1 := ULift.up (●MN (MaxNat.ofNat m)))
    (a2 := ULift.up (◯MN (MaxNat.ofNat n)))).mpr $$ [Ha Hf]
  · iframe
  ihave ⟨Hv, -⟩ := iOwn_valid_l $$ H
  icases internalCmraValid_discrete.mp $$ Hv with %Hv
  ipureintro
  exact (MonoNat.both_valid _ _).mp Hv

/-- Rocq: `invariants_transfinite_nested`. -/
theorem invariants_transfinite_nested (γ : GName) (l₁ l₂ : Loc) (φ : Val → IProp GF) :
    ⊢ invL N l₁ γ ∗ invR N l₂ γ -∗ ▷ (∀ m : Nat, ⌜m > 0⌝ -∗ φ hl_val(#(m : Int))) -∗
      Iris.Transfinite.wp .NotStuck ⊤ hl(!v(#l₁)) φ := by
  unfold invL invR Pos
  iintro ⟨#L, #R⟩ Post
  iapply swp_wp (k := 2) rfl
  -- open the invariants `L` and `R`
  iapply swp_atomic (E₂ := (⊤ \ ↑(N.@"L")) \ ↑(N.@"R"))
  imod inv_acc subset_top $$ L with ⟨HL, CloseL⟩
  imod inv_acc (E := ⊤ \ ↑(N.@"L")) (N := N.@"R")
    (subset_diff_of_disjoint subset_top (ndot_ne_disjoint N (by decide))) $$ R with ⟨HR, CloseR⟩
  imodintro
  iapply swp_step
  inext
  icases HL with ⟨%m, Hl₁, Hγa⟩
  icases HR with ⟨%l₂', Hl₂, #I⟩
  -- open the inner invariant `I`
  iapply swp_atomic (E₂ := ((⊤ \ ↑(N.@"L")) \ ↑(N.@"R")) \ ↑(N.@"I"))
  imod inv_acc (N := N.@"I") (subset_diff_of_disjoint
    (subset_diff_of_disjoint subset_top (ndot_ne_disjoint N (by decide)))
    (ndot_ne_disjoint N (by decide))) $$ I with ⟨HI, CloseI⟩
  imodintro
  iapply swp_step
  inext
  icases HI with ⟨%n, Hl₂', %hn, #Hγf⟩
  icases mnat_own (E := E) m n γ $$ Hγa Hγf with %hle
  iapply swp_load $$ [Hl₁]
  · iexact Hl₁
  iintro Hl₁
  imod CloseI $$ [Hl₂'] with -
  · inext
    iexists n
    iframe Hl₂' Hγf %hn
  imodintro
  imod CloseR $$ [Hl₂] with -
  · inext
    iexists l₂'
    iframe Hl₂ I
  imod CloseL $$ [Hl₁ Hγa] with -
  · inext
    iexists m
    iframe
  imodintro
  iapply Post $$ %m
  ipureintro
  omega

end Nested

end Iris.Transfinite.Examples
