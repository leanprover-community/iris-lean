/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Lifting

/-! # Adequacy

Reference: `iris/program_logic/adequacy.v`

The adequacy theorem connects the Iris program logic to the operational
semantics at the meta-level. It states that if we can prove a weakest
precondition in Iris, then the program is safe (not stuck) and, when it
terminates, the postcondition holds at the meta-level.

## Simplifications

This port omits later credit support. The `£` parameter and `step_fupdN`
infrastructure from the Coq version are dropped. The `num_laters_per_step`
is fixed to 0 (one later per step), so `steps_sum` is trivially `n`.

## Main Results

- `wptp_step'` — single step preserves thread pool WP
- `wptp_preservation` — n-step preservation
- `wp_not_stuck'` — WP implies not stuck
- `wp_strong_adequacy` — the main strong adequacy theorem
- `Adequate` — adequacy record (result + not stuck)
- `adequate_alt` — alternative characterization
- `adequate_tp_safe` — thread pool type safety
- `wp_adequacy` — simplified adequacy for single expressions
- `wp_invariance` — state invariance theorem
-/

namespace Iris.ProgramLogic

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [DecidableEq Positive]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

variable {Λ : Language}
variable [inst : IrisGS Λ GF]

/-! ## Thread Pool WP

A thread pool weakest precondition `wptp s es Φs` asserts that
each thread `es[i]` satisfies `WP es[i] @ s; ⊤ {{ Φs[i] }}`.
We define it as the big separating conjunction over paired lists. -/

/-- Thread pool weakest precondition: the big separating conjunction of
per-thread WPs over the thread pool.
Coq: `wptp` notation in `adequacy.v`. -/
noncomputable def wptp
    (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) : IProp GF :=
  big_sepL (fun i e =>
    match Φs[i]? with
    | some Φ => wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ
    | none => BIBase.emp) es

/-! ## Single Step -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- A single primitive step preserves the weakest precondition.
Given a step `e1 → e2` producing new threads `efs`, the state
interpretation and WP transfer to the post-state.
Coq: `wp_step` in `adequacy.v`. -/
theorem adq_wp_step (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (nt : Nat)
    (Φ : Λ.val → IProp GF)
    (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
    ⊢ uPred_fupd (M := M) (F := F) (@IrisGS.wsatGS Λ GF inst)
        Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (BIBase.sep
            (IrisGS.state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
              (big_sepL (fun _ ef =>
                wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef
                  (IrisGS.fork_post (Λ := Λ) (GF := GF))) efs)))) :=
  sorry

/-! ## Thread Pool Step -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- A step of the thread pool preserves the thread pool WP.
Coq: `wptp_step` in `adequacy.v`. -/
theorem wptp_step' (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hstep : step (es1, σ1) κ (es2, σ2)) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (M := M) (F := F) (Λ := Λ) s es1 Φs)
    ⊢ uPred_fupd (M := M) (F := F) (@IrisGS.wsatGS Λ GF inst)
        Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (BIBase.«exists» fun nt' =>
            BIBase.sep
              (IrisGS.state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (nt + nt'))
              (wptp (M := M) (F := F) (Λ := Λ) s es2
                (Φs ++ List.replicate nt'
                  (IrisGS.fork_post (Λ := Λ) (GF := GF)))))) :=
  sorry

/-! ## Multi-Step Preservation -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Multi-step preservation: after `n` steps, the thread pool WP
and state interpretation are preserved (modulo fupd and later).
Coq: `wptp_preservation` in `adequacy.v`. -/
theorem wptp_preservation (s : Stuckness) (n : Nat)
    (es1 es2 : List Λ.expr) (κs κs' : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hsteps : nsteps (Λ := Λ) n (es1, σ1) κs (es2, σ2)) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κs ++ κs') nt)
      (wptp (M := M) (F := F) (Λ := Λ) s es1 Φs)
    ⊢ uPred_fupd (M := M) (F := F) (@IrisGS.wsatGS Λ GF inst)
        Iris.Set.univ Iris.Set.univ
        (BIBase.«exists» fun nt' =>
          BIBase.sep
            (IrisGS.state_interp (Λ := Λ) (GF := GF) σ2 (n + ns) κs' (nt + nt'))
            (wptp (M := M) (F := F) (Λ := Λ) s es2
              (Φs ++ List.replicate nt'
                (IrisGS.fork_post (Λ := Λ) (GF := GF))))) :=
  sorry

/-! ## Not Stuck -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- WP at `NotStuck` stuckness implies the expression is not stuck.
Coq: `wp_not_stuck` in `adequacy.v`. -/
theorem wp_not_stuck' (e : Λ.expr) (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat)
    (Φ : Λ.val → IProp GF) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt)
      (wp (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ)
    ⊢ uPred_fupd (M := M) (F := F) (@IrisGS.wsatGS Λ GF inst)
        Iris.Set.univ (fun _ => False) (BIBase.pure (not_stuck e σ)) :=
  sorry

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
  sorry

/-- Thread pool type safety: an adequate program either all threads
have terminated or the pool can take another step.
Coq: `adequate_tp_safe` in `adequacy.v`. -/
theorem adequate_tp_safe (e1 : Λ.expr) (t2 : List Λ.expr) (σ1 σ2 : Λ.state)
    (φ : Λ.val → Λ.state → Prop)
    (had : Adequate (Λ := Λ) .notStuck e1 σ1 φ)
    (hsteps : rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2)) :
    (∀ e, e ∈ t2 → ∃ v, Λ.to_val e = some v) ∨
    ∃ t3 σ3, erased_step (Λ := Λ) (t2, σ2) (t3, σ3) :=
  sorry

/-! ## Strong Adequacy -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- The main strong adequacy theorem of Iris.
Given an Iris proof of the weakest precondition for a thread pool,
any property `φ` that follows from the postconditions holds at the
meta-level after `n` steps of execution.
Coq: `wp_strong_adequacy` in `adequacy.v`. -/
theorem wp_strong_adequacy (s : Stuckness)
    (es : List Λ.expr) (σ1 : Λ.state) (n : Nat)
    (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.«exists» fun (stateI : Λ.state → Nat → List Λ.observation → Nat → IProp GF) =>
           BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
           BIBase.«exists» fun (fork_post : Λ.val → IProp GF) =>
           BIBase.sep (stateI σ1 0 κs 0)
             (BIBase.sep
               (wptp (M := M) (F := F) (Λ := Λ) s es Φs)
               (BIBase.pure φ))))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    φ :=
  sorry

/-! ## Simplified Adequacy -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Simplified adequacy for a single expression. This requires the
`IrisGS` instance to use `num_laters_per_step = 0` and a simple
state interpretation that ignores step count and fork count.
Coq: `wp_adequacy` in `adequacy.v`. -/
theorem wp_adequacy (s : Stuckness) (e : Λ.expr) (σ : Λ.state)
    (φ : Λ.val → Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.«exists» fun (stateI : Λ.state → List Λ.observation → IProp GF) =>
             BIBase.«exists» fun (fork_post : Λ.val → IProp GF) =>
             BIBase.sep (stateI σ κs)
               (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e
                 (fun v => BIBase.pure (φ v))))) :
    Adequate (Λ := Λ) s e σ (fun v _ => φ v) :=
  sorry

/-! ## Invariance -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- State invariance: if we can prove a WP and extract a property `φ`
from the final state interpretation, then `φ` holds at the meta-level.
Coq: `wp_invariance` in `adequacy.v`. -/
theorem wp_invariance (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.«exists» fun (stateI : Λ.state → List Λ.observation → Nat → IProp GF) =>
             BIBase.«exists» fun (fork_post : Λ.val → IProp GF) =>
             BIBase.sep (stateI σ1 κs 0)
               (BIBase.sep
                 (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1
                   (fun _ => BIBase.pure True))
                 (BIBase.wand (stateI σ2 [] (t2.length - 1))
                   (BIBase.«exists» fun (_ : Iris.Set Positive) =>
                     uPred_fupd (M := M) (F := F) W Iris.Set.univ (fun _ => False)
                       (BIBase.pure φ))))))
    (hsteps : rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2)) :
    φ :=
  sorry

end Iris.ProgramLogic
