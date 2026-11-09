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

/-- Initialize the partial execution invariant from the heap state and credits. -/
private theorem heaplangEH_partial_init (σ : heapF Loc (Option Val)) (n : Nat) :
    stateInterp_heap σ ∗ £ n -∗
    (heaplangEH_partial_adequate (GF := GF) (GE := heaplangE) (GR := Val)).inv
      ⟨ConcState.new, σ, 0, n⟩ [] := by
  change ⊢ (iprop(stateInterp_heap σ ∗ £ n -∗
    <affine> ⌜([] : List ((ITree heaplangE Val → IProp GF) → IProp GF)) = []⌝ ∗
      (stateInterp_heap σ ∗ (True ∗ (emp ∗ £ n)))) : IProp GF)
  iintro ⟨Hheap, Hcredits⟩
  iframe
  itrivial

/-- Initialize the total execution invariant from the heap state. -/
private theorem heaplangEH_total_init (σ : heapF Loc (Option Val)) :
    stateInterp_heap σ -∗
    (heaplangEH_total_adequate (GF := GF) (GE := heaplangE) (GR := Val)).inv
      ⟨ConcState.new, σ, 0, 0⟩ [] := by
  change ⊢ (iprop(stateInterp_heap σ -∗
    <affine> ⌜([] : List ((ITree heaplangE Val → IProp GF) → IProp GF)) = []⌝ ∗
      (stateInterp_heap σ ∗ (True ∗ (emp ∗ emp)))) : IProp GF)
  iintro Hheap
  iframe
  itrivial

end handler

/-- A uniformly provable HeapLang WP yields a pure guarantee for the executable state machine. -/
theorem heaplang_partial_adequacy (e : Exp)
    (σ : heapF Loc (Option Val)) (n : Nat) (φ : Val → Prop)
    (C : ITree heaplangE Val → HeaplangState (ITree heaplangE Val) → Prop)
    (Hexec : exec (heaplangEH (fun _ => 1)) e.denote ⟨ConcState.new, σ, 0, n⟩ C)
    (Hwp : ∀ [InvGS GF] [_G : heaplangHGS GF], ([∗map] l ↦ w ∈ σ, (l ↦? w) : IProp GF) -∗
        WP e @ step[(BI.later : IProp GF → IProp GF)] ; ⊤ {{ v, ⌜φ v⌝ }}) :
    ∃ t' s', C t' s' ∧ ∀ v, t' = .ret v → φ v := by
  apply pure_soundness (PROP := IProp GF)
  apply fupd_soundness .hasLC n (E1 := ⊤) (E2 := ∅)
  iintro %Hinv Hcredits
  imod (fupd_mask_subseteq (E2 := ∅) (by simp)) with Hclose
  imod heapH_init σ with ⟨%Gmod, Hinv, Hsσ, Hσ⟩
  letI G : heaplangHGS GF := ⟨Gmod⟩
  imod Hclose
  ihave Hwp := Hwp $$ Hσ
  ihave Hstate := heaplangEH_partial_init σ n $$ [Hsσ Hcredits]; iframe
  imod wpi_adequate $$ Hwp Hstate with ⟨%t', %s', %Ms', %M, %HC, Heinv, Hcont, Htp⟩; assumption
  by_cases Hret : ∃ v, t' = .ret v
  · obtain ⟨v, rfl⟩ := Hret
    imod wpi_tp_elim 0 $$ Hcont Htp with Hpost; simp
    imod Hpost with %Hφ
    imod (fupd_mask_subseteq (E2 := ∅)) with Hclose; simp
    ipureintro; refine ⟨ITree.ret v, s', ?_⟩
    simp [HC]; intro v' Heq
    cases ITreeF.ret.inj (congrArg ITree.unfold Heq)
    exact Hφ
  · iintro !>; ipureintro
    exists t', s', HC
    intro v Hv
    exfalso; apply Hret
    exists v

theorem heaplang_total_adequacy (e : Exp)
    (σ : heapF Loc (Option Val)) (φ : Val → Prop)
    (C : ITree heaplangE Val → HeaplangState (ITree heaplangE Val) → Prop)
    (Hexec : exec (heaplangEH (fun _ => 0)) e.denote ⟨ConcState.new, σ, 0, 0⟩ C)
    (Hwp : ∀ [InvGS GF] [_G : heaplangHGS GF], ([∗map] l ↦ w ∈ σ, (l ↦? w) : IProp GF) -∗
      WP e @ step[(id : IProp GF → IProp GF)] ; ⊤ {{ v, ⌜φ v⌝ }}) :
    ∃ t' s', C t' s' ∧ ∀ v, t' = .ret v → φ v := by
  apply pure_soundness (PROP := IProp GF)
  apply fupd_soundness .hasLC 0 (E1 := ⊤) (E2 := ∅)
  iintro %Hinv Hcredits
  imod (fupd_mask_subseteq (E2 := ∅) (by simp)) with Hclose
  imod heapH_init σ with ⟨%Gmod, Hinv, Hsσ, Hσ⟩
  letI G : heaplangHGS GF := ⟨Gmod⟩
  imod Hclose
  ihave Hwp := Hwp $$ Hσ
  ihave Hstate := heaplangEH_total_init σ $$ Hsσ
  imod wpi_adequate $$ Hwp Hstate with ⟨%t', %s', %Ms', %M, %HC, Heinv, Hcont, Htp⟩; assumption
  by_cases Hret : ∃ v, t' = .ret v
  · obtain ⟨v, rfl⟩ := Hret
    imod wpi_tp_elim 0 $$ Hcont Htp with Hpost; simp
    imod Hpost with %Hφ
    imod (fupd_mask_subseteq (E2 := ∅)) with Hclose; simp
    ipureintro; refine ⟨ITree.ret v, s', ?_⟩
    simp [HC]; intro v' Heq
    cases ITreeF.ret.inj (congrArg ITree.unfold Heq)
    exact Hφ
  · iintro !>; ipureintro
    exists t', s', HC
    intro v Hv
    exfalso; apply Hret
    exists v

end IrisITree
