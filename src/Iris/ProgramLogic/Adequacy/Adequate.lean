/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.Preservation

/-! # Adequacy: Adequate Records

Reference: `iris/program_logic/adequacy.v`

This file defines the adequacy record and its basic characterizations.
-/

namespace Iris.ProgramLogic

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

variable {Λ : Language}
variable [inst : IrisGS Λ GF]
variable {W : WsatGS GF}
/-! ## Adequate -/

/-- The adequacy record: a program `e1` starting in state `σ1` is adequate
if (1) whenever it reduces to a value, the postcondition holds, and
(2) it is never stuck (when `s = NotStuck`).
Coq: `adequate` record in `adequacy.v`. -/
structure Adequate (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (φ : Λ.val → Λ.state → Prop) : Prop where
  /-- If the main thread terminates with value `v2` in state `σ2`, then `φ v2 σ2`. -/
  adequate_result : ∀ t2 σ2 v2,
    rtc (erased_step (Λ := Λ)) ([e1], σ1) (Λ.of_val v2 :: t2, σ2) →
    φ v2 σ2
  /-- If `s = NotStuck`, every reachable expression is not stuck. -/
  adequate_not_stuck : ∀ t2 σ2 e2,
    s = .notStuck →
    rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2) →
    e2 ∈ t2 → not_stuck e2 σ2

/-- Alternative characterization of adequacy.
Coq: `adequate_alt` in `adequacy.v`. -/
theorem adequate_alt (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (φ : Λ.val → Λ.state → Prop) :
    Adequate s e1 σ1 φ ↔
    ∀ t2 σ2,
      rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2) →
        (∀ v2 t2', t2 = Λ.of_val v2 :: t2' → φ v2 σ2) ∧
        (∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2) :=
  by
    -- unfold the record and rearrange the quantifiers
    constructor
    · intro had t2 σ2 hrtc
      refine ⟨?_, ?_⟩
      · intro v2 t2' ht2
        exact had.adequate_result t2' σ2 v2 (by simpa [ht2] using hrtc)
      · intro e2 hs hemem
        exact had.adequate_not_stuck t2 σ2 e2 hs hrtc hemem
    · intro h
      refine ⟨?_, ?_⟩
      · intro t2 σ2 v2 hrtc
        have h' := h (Λ.of_val v2 :: t2) σ2 hrtc
        exact (h'.1 v2 t2 rfl)
      · intro t2 σ2 e2 hs hrtc hemem
        exact (h t2 σ2 hrtc).2 e2 hs hemem

/-- Thread pool type safety: an adequate program either all threads
have terminated or the pool can take another step.
Coq: `adequate_tp_safe` in `adequacy.v`. -/
theorem adequate_tp_safe (e1 : Λ.expr) (t2 : List Λ.expr) (σ1 σ2 : Λ.state)
    (φ : Λ.val → Λ.state → Prop)
    (had : Adequate (Λ := Λ) .notStuck e1 σ1 φ)
    (hsteps : rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2)) :
    (∀ e, e ∈ t2 → ∃ v, Λ.to_val e = some v) ∨
    ∃ t3 σ3, erased_step (Λ := Λ) (t2, σ2) (t3, σ3) :=
  by
    -- either all threads are values, or pick a non-value and step it
    classical
    by_cases hval : ∀ e, e ∈ t2 → ∃ v, Λ.to_val e = some v
    · exact Or.inl hval
    · have hnot : ∃ e, e ∈ t2 ∧ ∀ v, Λ.to_val e ≠ some v := by
        -- extract a counterexample to the value predicate
        simpa [Classical.not_forall, not_exists, Decidable.not_imp_iff_and_not] using hval
      rcases hnot with ⟨e2, hemem, hnv⟩
      have hns := had.adequate_not_stuck t2 σ2 e2 rfl hsteps hemem
      rcases hns with ⟨v, hv⟩ | hred
      · exact False.elim (hnv v hv)
      · rcases hred with ⟨κ, e3, σ3, efs, hprim⟩
        rcases mem_split hemem with ⟨t1, t2', ht2⟩
        refine Or.inr ⟨t1 ++ e3 :: t2' ++ efs, σ3, ?_⟩
        refine ⟨κ, ?_⟩
        simpa [ht2, List.append_assoc] using
          (step.step_atomic (Λ := Λ) (e1 := e2) (σ1 := σ2)
            (e2 := e3) (σ2 := σ3) (efs := efs) (t1 := t1) (t2 := t2')
            (κ := κ) hprim)


end Iris.ProgramLogic
