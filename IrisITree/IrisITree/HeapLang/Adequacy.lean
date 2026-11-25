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

open Iris BI Iris.Std Iris.HeapLang ITree ITree.Effects ITree.Exec

variable {GF : BundledGFunctors} [InvGS GF] [heaplangHGS GF]
local bi (IProp GF)

section handler

/-- Partial-correctness interpretation. -/
instance heaplangEH_partial_adequate :
    EHandlerAdequate (heaplangH (GF := GF) BI.later)
      (heaplangEH (GE := GE) (GR := GR) (fun _ => 1)) := by
  unfold heaplangH heaplangEH
  infer_instance

theorem heaplangEH_partial_adequate_inv_eq :
  (heaplangEH_partial_adequate (GF := GF) (GE := heaplangE) (GR := Val)).inv s Ms ⊣⊢
    ⌜Ms = ListPerm.ofList (s.tp.pool.filterMap
      (Option.map fun t P => iprop(|={⊤,∅}=> P t)))⌝ ∗
        stateInterp_heap s.heap ∗ £ s.steps_left := by
  simp [EHandlerAdequate.inv.eq_def, heaplangEH_partial_adequate, inferInstance, isoEH_adequate, id,
    sumEEH_adequate, concEH_adequate, EH_of_SEH_adequate, SEHandlerAdequate.inv.eq_def,
    sumSEH_adequate, heapEH_adequate, failEH_adequate, demonicEH_adequate, stepEH_later_adequate]
  isplit
  · iintro ⟨%Ms1, %Ms2, %hp, %h1, %rfl, $, -, -, $⟩
    ipureintro; grind
  · iintro ⟨%hp, $, $⟩
    ipureintro; grind

/-- Total-correctness interpretation. -/
instance heaplangEH_total_adequate :
    EHandlerAdequate (heaplangH (GF := GF) id)
      (heaplangEH (GE := GE) (GR := GR) (fun _ => 0)) := by
  unfold heaplangH heaplangEH
  infer_instance

theorem heaplangEH_total_adequate_inv_eq :
  (heaplangEH_total_adequate (GF := GF) (GE := heaplangE) (GR := Val)).inv s Ms ⊣⊢
    ⌜Ms = ListPerm.ofList (s.tp.pool.filterMap
      (Option.map fun t P => iprop(|={⊤,∅}=> P t)))⌝ ∗
        stateInterp_heap s.heap := by
  simp [EHandlerAdequate.inv.eq_def, heaplangEH_total_adequate, inferInstance, isoEH_adequate, id,
    sumEEH_adequate, concEH_adequate, EH_of_SEH_adequate, SEHandlerAdequate.inv.eq_def,
    sumSEH_adequate, heapEH_adequate, failEH_adequate, demonicEH_adequate, stepEH_id_adequate]
  isplit
  · iintro ⟨%Ms1, %Ms2, %hp, %h1, %rfl, $, -, -⟩
    ipureintro; grind
  · iintro ⟨%hp, $⟩
    ipureintro; grind

/-- Initialize the partial execution invariant from the heap state and credits. -/
private theorem heaplangEH_partial_init (σ : heapF Loc (Option Val)) (n : Nat) :
    stateInterp_heap σ ∗ £ n -∗
    (heaplangEH_partial_adequate (GF := GF) (GE := heaplangE) (GR := Val)).inv
      ⟨ConcState.new, σ, 0, n⟩ ∅ := by
  iintro ⟨Hheap, Hcredits⟩
  rw [heaplangEH_partial_adequate_inv_eq.to_eq]
  iframe
  ipureintro
  rfl

/-- Initialize the total execution invariant from the heap state. -/
private theorem heaplangEH_total_init (σ : heapF Loc (Option Val)) :
    stateInterp_heap σ -∗
    (heaplangEH_total_adequate (GF := GF) (GE := heaplangE) (GR := Val)).inv
      ⟨ConcState.new, σ, 0, 0⟩ ∅ := by
  iintro Hheap
  rw [heaplangEH_total_adequate_inv_eq.to_eq]
  iframe
  ipureintro
  rfl

end handler

/-- A uniformly provable HeapLang WP yields a pure guarantee for the executable state machine. -/
theorem heaplang_partial_adequacy (e : Exp)
    (σ : heapF Loc (Option Val)) (n : Nat) (φ : Val → Prop)
    (C : ITree heaplangE Val → HeaplangState (ITree heaplangE Val) → Prop)
    (Hexec : exec (heaplangEH (fun _ => 1)) e.denote ⟨ConcState.new, σ, 0, n⟩ C)
    (Hwp : ∀ [InvGS GF] [_G : heaplangHGS GF], ([∗map] l ↦ w ∈ σ, (l ↦? w) : IProp GF) -∗
        WP e @ step[later] ; ⊤ {{ v, ⌜φ v⌝ }}) :
    ∃ t' s', C t' s' ∧ ∀ v, t' = .ret v → φ v := by
  apply pure_soundness (PROP := IProp GF)
  apply fupd_soundness .hasLC n (E1 := ⊤) (E2 := ∅)
  iintro %Hinv Hcredits
  imod (fupd_mask_subseteq (E2 := ∅) (by simp)) with Hclose
  imod heapH_init σ with ⟨%Gmod, Hinv, Hsσ, Hσ⟩
  letI G : heaplangHGS GF := ⟨Gmod⟩
  imod Hclose
  ihave Hwp := Hwp $$ Hσ
  imod wpi_adequate (H := heaplangH (GF := GF) BI.later) (Hexec := Hexec) $$ Hwp [Hsσ Hcredits] with
    ⟨%t', %s', %Ms', %M, %HC, -, Hcont, Htp⟩
  · iapply heaplangEH_partial_init
    iframe
  by_cases Hret : ∃ v, t' = .ret v
  · obtain ⟨v, rfl⟩ := Hret
    imod wpi_tp_elim $$ Hcont Htp with > >%Hφ
    imod (fupd_mask_subseteq (E2 := ∅) (by simp)) with Hclose
    ipureintro
    refine ⟨ITree.ret v, s', HC, fun v' Heq => ?_⟩
    obtain rfl := ITreeF.ret.inj (congrArg ITree.unfold Heq)
    exact Hφ
  · imodintro
    ipureintro
    exact ⟨t', s', HC, fun v Hv => (Hret ⟨v, Hv⟩).elim⟩

theorem heaplang_total_adequacy (e : Exp)
    (σ : heapF Loc (Option Val)) (φ : Val → Prop)
    (C : ITree heaplangE Val → HeaplangState (ITree heaplangE Val) → Prop)
    (Hexec : exec (heaplangEH (fun _ => 0)) e.denote ⟨ConcState.new, σ, 0, 0⟩ C)
    (Hwp : ∀ [InvGS GF] [_G : heaplangHGS GF], ([∗map] l ↦ w ∈ σ, (l ↦? w) : IProp GF) -∗
      WP e @ step[id] ; ⊤ {{ v, ⌜φ v⌝ }}) :
    ∃ t' s', C t' s' ∧ ∀ v, t' = .ret v → φ v := by
  apply pure_soundness (PROP := IProp GF)
  apply fupd_soundness .hasLC 0 (E1 := ⊤) (E2 := ∅)
  iintro %Hinv Hcredits
  imod (fupd_mask_subseteq (E2 := ∅) (by simp)) with Hclose
  imod heapH_init σ with ⟨%Gmod, Hinv, Hsσ, Hσ⟩
  letI G : heaplangHGS GF := ⟨Gmod⟩
  imod Hclose
  ihave Hwp := Hwp $$ Hσ
  imod wpi_adequate (H := heaplangH (GF := GF) id) (Hexec := Hexec) $$ Hwp [Hsσ] with
    ⟨%t', %s', %Ms', %M, %HC, -, Hcont, Htp⟩
  · iapply heaplangEH_total_init $$ Hsσ
  by_cases Hret : ∃ v, t' = .ret v
  · obtain ⟨v, rfl⟩ := Hret
    imod wpi_tp_elim $$ Hcont Htp with > >%Hφ
    imod (fupd_mask_subseteq (E2 := ∅) (by simp)) with Hclose
    ipureintro
    refine ⟨ITree.ret v, s', HC, fun v' Heq => ?_⟩
    obtain rfl := ITreeF.ret.inj (congrArg ITree.unfold Heq)
    exact Hφ
  · imodintro
    ipureintro
    exact ⟨t', s', HC, fun v Hv => (Hret ⟨v, Hv⟩).elim⟩

end IrisITree
