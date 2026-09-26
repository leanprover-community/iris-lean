/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.ProgramLogic.TotalAdequacy

/-! # Total adequacy of HeapLang -/

@[expose] public section
namespace Iris.HeapLang

open ProgramLogic Language Std FromMathlib

/-- A total weakest precondition for `e` makes the thread pool `[e]` strongly normalizing.

Rocq additionally hands the caller `inv_heap_inv`; that premise is dropped here because
`inv_pointsto` is not yet ported. -/
@[rocq_alias heap_lang.heap_total]
theorem heap_total [HeapLangGpreS hlc GF] (s : Stuckness) (e : Exp) (σ : State)
    (φ : Val → Prop) (m : Nat)
    (Hwp : ∀ [HeapLangGS hlc GF], ⊢@{IProp GF} £ m -∗ WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]) :
    Relation.StronglyNormalizing ErasedStep ([e], σ) := by
  refine twp_total (hlc := hlc) (GF := GF) s e σ (fun v => iprop(⌜φ v⌝)) 0 m ?_
  iintro %Hinv
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (H := HeapF) (.own 1)
      (Std.PartialMap.map (fun v : Option Val => toAgree (DiscreteO.mk v)) σ.heap))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (H := HeapF) (.own 1)
      (Std.PartialMap.map (fun g : GName => toAgree (DiscreteO.mk g)) (∅ : HeapF GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  imod (ProphMap.init (H := ProphMapF) ([] : List Observation) σ.usedProphId)
    with ⟨%Gproph, Hproph⟩
  letI instHeapLangGS : HeapLangGS hlc GF := ⟨⟨γh, γm⟩, Gproph⟩
  imodintro
  iexists (fun σ _ κs _ => iprop(genHeapInterp σ.heap ∗ prophMapInterp κs σ.usedProphId))
  iexists (fun _ => 0), (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  simp only []
  ihave #Hwp := @Hwp _
  iframe Hwp Hproph
  simp only [genHeapInterp]
  iexists (∅ : HeapF GName)
  unfold ghost_map_auth
  iframe Hh Hm
  ipureintro
  intro k hk
  simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk

end Iris.HeapLang
