/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.SimplifiedAdequacy

/-! # Adequacy: Invariance

Reference: `iris/program_logic/adequacy.v`

This file provides the state invariance corollary of adequacy.
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
/-! ## Invariance -/

/-- State invariance: if we can prove a WP and extract a property `φ`
from the final state interpretation, then `φ` holds at the meta-level.
Coq: `wp_invariance` in `adequacy.v`. -/
theorem wp_invariance (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF, ∀ κs : List Λ.observation, ∀ ns : Nat,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
            (BIBase.sep
              (wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1
                (fun _ => BIBase.pure True))
              (BIBase.wand
                (state_interp (Λ := Λ) (GF := GF) σ2 ns [] (t2.length - 1))
                (BIBase.«exists» fun (_ : Iris.Set Positive) =>
                  uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
                    (BIBase.pure φ))))))
    (hsteps : rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2)) :
    φ :=
  by
    -- reduce to `nsteps` and apply strong adequacy with invariance continuation
    rcases (erased_steps_nsteps (Λ := Λ) ([e1], σ1) (t2, σ2)).1 hsteps
      with ⟨n, κs, hsteps⟩
    have Hinv := wp_invariance_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e1 := e1) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) (Hwp := fun W => Hwp W κs n)
    exact wp_strong_adequacy (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := [e1]) (σ1 := σ1) (n := n) (κs := κs)
      (t2 := t2) (σ2 := σ2) (φ := φ) Hinv hsteps

end Iris.ProgramLogic
