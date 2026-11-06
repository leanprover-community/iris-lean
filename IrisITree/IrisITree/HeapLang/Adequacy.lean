/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import IrisITree.Core.Handler
public import IrisITree.Core.WpiExec
public import IrisITree.HeapLang.ProgramLogic

@[expose] public section

namespace IrisITree

open Iris BI Iris.HeapLang ITree ITree.Effects ITree.Exec

variable {GF : BundledGFunctors} [InvGS GF] [heaplangHGS GF]

section handler

/-- Partial-correctness interpretation. -/
instance heaplangEH_partial_adequate :
    EHandlerAdequate (heaplangH (GF := GF) BI.later)
      (heaplangEH (GE := GE) (GR := GR) (fun _ => 1)) := by
  unfold heaplangH heaplangEH
  infer_instance

/-- Total-correctness interpretation. -/
instance heaplangEH_total_adequate :
    EHandlerAdequate (heaplangH (GF := GF) id)
      (heaplangEH (GE := GE) (GR := GR) (fun _ => 0)) := by
  unfold heaplangH heaplangEH
  infer_instance

end handler

/-- Invariant hold during heaplang execution. -/
abbrev heaplangExecInv (s : HeaplangState (ITree heaplangE Val))
    (Ms : List ((ITree heaplangE Val → IProp GF) → IProp GF)) : IProp GF :=
  heaplangEH_partial_adequate.inv s Ms

theorem heaplang_adequacy (e : Exp) s (Φ : Val → IProp GF) M
    (C : ITree heaplangE Val → HeaplangState (ITree heaplangE Val) → Prop)
    (Hexec : exec (heaplangEH (fun _ => 1)) e.denote s C) :
    WP e @ step[(BI.later : IProp GF → IProp GF)]; M {{ Φ }} -∗
    heaplangExecInv s [] -∗
    |={M, ∅}=> ∃ t' s' Ms' M',
      ⌜C t' s'⌝ ∗ heaplangExecInv s' Ms' ∗
      (∀ P, M' P ={∅}=∗ P t') ∗
      WPi_tp (M' :: Ms') @> (heaplangH BI.later) {{ v, |={∅, M}=> Φ v }} := by
  iintro Hwp
  iapply wpi_adequate
  · exact Hexec
  · iapply wp_unfold $$ Hwp

theorem heaplang_partial_adequacy (e : Exp)
    (σ : heapF Loc (Option Val)) (n : Nat) (φ : Val → Prop)
    (C : ITree heaplangE Val → HeaplangState (ITree heaplangE Val) → Prop)
    (Hexec : exec (heaplangEH (fun _ => 1)) e.denote ⟨ConcState.new, σ, 0, n⟩ C) :
    ∀ [InvGS GF] [_G : heaplangHGS GF],
      ([∗map] l ↦ w ∈ σ, (l ↦? w : IProp GF) -∗
      WP e @ step[(BI.later : IProp GF → IProp GF)]; ⊤ {{ v, ⌜φ v⌝ }}) -∗
    ⌜∃ t' s', C t' s' ∧ ∀ v, t' = .ret v → φ v⌝ := by
  iintro %_ %_ Hwp
  sorry

theorem heaplang_total_adequacy (e : Exp)
    (σ : heapF Loc (Option Val)) (φ : Val → Prop)
    (C : ITree heaplangE Val → HeaplangState (ITree heaplangE Val) → Prop)
    (Hexec : exec (heaplangEH (fun _ => 0)) e.denote ⟨ConcState.new, σ, 0, 0⟩ C) :
    ∀ [InvGS GF] [_G : heaplangHGS GF],
      ([∗map] l ↦ w ∈ σ, (l ↦? w : IProp GF) -∗
      WP e @ step[(id : IProp GF → IProp GF)]; ⊤ {{ v, ⌜φ v⌝ }}) -∗
    ⌜∃ t' s', C t' s' ∧ ∀ v, t' = .ret v → φ v⌝:= by
  sorry


end IrisITree
