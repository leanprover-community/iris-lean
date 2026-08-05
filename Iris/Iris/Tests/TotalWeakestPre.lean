/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalAdequacy
public import Iris.ProgramLogic.TotalEctxLifting
public import Iris.ProgramLogic.TotalLifting
public import Iris.Examples.ClosedProofs
public import Iris.HeapLang.Instances

namespace Iris.Tests.TotalWeakestPre

open Iris BI ProgramLogic ProgramLogic.Language ProgramLogic.Language.Notation
open Std LawfulSet

/-! A small language for total-correctness tests. -/

inductive Expr where
  | val : Nat → Expr
  | tick : Nat → Expr
  | put : Nat → Expr
  | branch : Nat → Expr
  | observe : Expr
  | stuck : Expr
deriving DecidableEq, Repr

abbrev Val := Nat
abbrev State := Nat
abbrev Obs := Unit

instance : ToVal Expr Val where
  toVal
    | .val n => some n
    | _ => none
  ofVal := .val
  coe_of_toVal_eq_some := by
    intro e v h
    cases e <;> simp_all
  toVal_coe := by simp

inductive Step : Expr → State → List Obs → Expr → State → List Expr → Prop
  | tickSucc (n σ) : Step (.tick (n + 1)) σ [] (.tick n) σ []
  | tickZero (σ) : Step (.tick 0) σ [] (.val 0) σ []
  | put (n σ) : Step (.put n) σ [] (.val n) n []
  | branchLeft (n σ) : Step (.branch (n + 1)) σ [] (.branch n) σ []
  | branchRight (n σ) : Step (.branch (n + 1)) σ [] (.tick n) σ []
  | branchZero (σ) : Step (.branch 0) σ [] (.val 0) σ []
  | observe (σ) : Step .observe σ [()] (.val 0) σ []

instance : PrimStep Expr State (List Obs) where
  primStep
    | (e₁, σ₁), κ, (e₂, σ₂, efs) => Step e₁ σ₁ κ e₂ σ₂ efs

instance : Language Expr State Obs Val where
  val_stuck := by
    intro e σ κ e' σ' efs H
    cases H <;> rfl

instance : LanguageNoFork Expr State Obs Val where
  no_fork H := by cases H <;> rfl

section Proofs

noncomputable abbrev GF := Iris.Examples.ClosedProofs.GF

variable [InvGS_gen .hasNoLC GF]

noncomputable local instance testIrisGS : IrisGS_gen .hasNoLC Expr GF where
  toStateInterp := ⟨fun _ _ _ _ => iprop(True)⟩
  numLatersPerStep := fun _ => 0
  forkPost := fun _ => iprop(True)
  stateInterp_mono := by
    intro σ ns obs nt
    iintro _
    imodintro
    itrivial

theorem tick_twp (n : Nat) :
    ⊢ WP (Expr.tick n) @ Stuckness.NotStuck ; ⊤ [{
      fun v : Val => (iprop(⌜v = 0⌝) : IProp GF) }] := by
  induction n with
  | zero =>
      iapply twp_lift_pure_det_step_no_fork
        (e₂ := Expr.val 0)
      · intro σ
        exact ⟨.val 0, σ, [], Step.tickZero σ⟩
      · intro σ₁ κ e₂' σ₂ efs H
        cases H
        exact ⟨rfl, rfl, rfl, rfl⟩
      · imodintro
        iapply twp.value rfl
        ipureintro
        rfl
  | succ n IH =>
      iapply twp_lift_pure_det_step_no_fork
        (e₂ := Expr.tick n)
      · intro σ
        exact ⟨.tick n, σ, [], Step.tickSucc n σ⟩
      · intro σ₁ κ e₂' σ₂ efs H
        cases H
        exact ⟨rfl, rfl, rfl, rfl⟩
      · imodintro
        iapply IH

omit [InvGS_gen .hasNoLC GF] in
theorem tick_purePrimStep_succ (n : Nat) :
    Expr.tick (n + 1) -ᵖ-> Expr.tick n where
  safe σ := ⟨.tick n, σ, [], Step.tickSucc n σ⟩
  deterministic H := by
    cases H
    exact ⟨rfl, rfl, rfl, rfl⟩

omit [InvGS_gen .hasNoLC GF] in
theorem tick_purePrimStep_zero :
    Expr.tick 0 -ᵖ-> Expr.val 0 where
  safe σ := ⟨.val 0, σ, [], Step.tickZero σ⟩
  deterministic H := by
    cases H
    exact ⟨rfl, rfl, rfl, rfl⟩

omit [InvGS_gen .hasNoLC GF] in
theorem tick_pureExec (n : Nat) :
    PureExec True (n + 1) (Expr.tick n) (Expr.val 0) where
  pureExec _ := by
    induction n with
    | zero =>
        exact .once tick_purePrimStep_zero
    | succ n IH =>
        exact .head (tick_purePrimStep_succ n) IH

theorem tick_twp_via_pureExec (n : Nat) :
    ⊢ WP (Expr.tick n) @ Stuckness.NotStuck ; ⊤ [{
      fun v : Val => (iprop(⌜v = 0⌝) : IProp GF) }] := by
  iapply twp_pure_step (tick_pureExec n) trivial
  iapply twp.value rfl
  ipureintro
  rfl

theorem put_twp (n : Nat) :
    ⊢ WP (Expr.put n) @ Stuckness.NotStuck ; ⊤ [{
      fun v : Val => (iprop(⌜v = n⌝) : IProp GF) }] := by
  iapply twp_lift_atomic_step_no_fork (e₁ := Expr.put n) rfl
  iintro %σ %ns %obs %nt _
  imodintro
  isplit
  · ipureintro
    exact ⟨.val n, n, [], Step.put n σ⟩
  · iintro %κ %e₂ %σ₂ %efs %Hstep
    cases Hstep
    imodintro
    isplit
    · ipureintro
      rfl
    · isplit
      · ipureintro
        rfl
      · isplit
        · itrivial
        · iexists n
          isplit
          · ipureintro
            rfl
          · ipureintro
            rfl

theorem branch_twp (n : Nat) :
    ⊢ WP (Expr.branch n) @ Stuckness.NotStuck ; ⊤ [{
      fun v : Val => (iprop(⌜v = 0⌝) : IProp GF) }] := by
  induction n with
  | zero =>
      iapply twp_lift_pure_det_step_no_fork
        (e₂ := Expr.val 0)
      · intro σ
        exact ⟨.val 0, σ, [], Step.branchZero σ⟩
      · intro σ₁ κ e₂' σ₂ efs H
        cases H
        exact ⟨rfl, rfl, rfl, rfl⟩
      · imodintro
        iapply twp.value rfl
        ipureintro
        rfl
  | succ n IH =>
      iapply twp_lift_step_no_fork (e₁ := Expr.branch (n + 1)) rfl
      iintro %σ %ns %obs %nt _
      iapply fupd_mask_intro empty_subset
      iintro Hclose
      isplit
      · ipureintro
        exact ⟨.branch n, σ, [], Step.branchLeft n σ⟩
      · iintro %κ %e₂ %σ₂ %efs %Hstep
        cases Hstep
        · imod Hclose
          imodintro
          isplit
          · ipureintro
            rfl
          · isplit
            · ipureintro
              rfl
            · isplitl []
              · change ⊢ iprop(True)
                itrivial
              · iapply IH
        · imod Hclose
          imodintro
          isplit
          · ipureintro
            rfl
          · isplit
            · ipureintro
              rfl
            · isplitl []
              · change ⊢ iprop(True)
                itrivial
              · iapply tick_twp n

end Proofs

section CoreRuleChecks

variable {E : CoPset} {e : Expr} {v : Val}
variable {Φ : Val → IProp GF} {P Q : IProp GF}
variable [IrisGS_gen .hasNoLC Expr GF]

example :
    WP e @ Stuckness.NotStuck ; ⊤ [{ Φ }] ⊢
      WP e @ Stuckness.NotStuck ; ⊤ {{ Φ }} :=
  twp.to_wp

example :
    P ∗ WP e @ Stuckness.NotStuck ; ⊤ [{ Φ }] ⊢
      WP e @ Stuckness.NotStuck ; ⊤ [{ v, P ∗ Φ v }] :=
  twp.frame_l

example :
    WP (id e) @ Stuckness.NotStuck ; ⊤ [{ Φ }] ⊢
      TotalWp.totalWp Stuckness.NotStuck ⊤ e
        (fun v : Val => iprop(
          WP (id (v : Expr)) @ Stuckness.NotStuck ; ⊤ [{ Φ }])) :=
  twp.bind_inv id

example :
    TotalWp.totalWp Stuckness.NotStuck ⊤ e
      (fun v : Val => iprop(
        WP (id (v : Expr)) @ Stuckness.NotStuck ; ⊤ [{ Φ }])) ⊢
      WP (id e) @ Stuckness.NotStuck ; ⊤ [{ Φ }] :=
  twp.bind id

example [inst : Language.IntoVal e v] :
    P ∗ Φ v ⊢ WP e @ Stuckness.NotStuck ; ⊤ [{ w, P ∗ Φ w }] := by
  iintro ⟨HP, HΦ⟩
  iframe HP
  iapply twp.value $$ HΦ
  exact inst.into_val.symm

/-- error: iframe: cannot frame R 0 -/
#guard_msgs in
example (R : Nat → IProp GF) :
    R 0 ∗ WP e @ Stuckness.NotStuck ; E [{ fun _ => emp }] ⊢
      WP e @ Stuckness.NotStuck ; E [{ fun _ => iprop(∃ n, R n) }] := by
  iintro ⟨HR, Hwp⟩
  iframe HR

example :
    (|={E}=> P) ∗ (P -∗ WP e @ Stuckness.NotStuck ; E [{ Φ }]) ⊢
      WP e @ Stuckness.NotStuck ; E [{ Φ }] := by
  iintro ⟨HP, Hwp⟩
  imod HP
  iapply Hwp $$ HP

example :
    (|==> Q) ∗ (Q -∗ WP e @ Stuckness.NotStuck ; E [{ Φ }]) ⊢
      WP e @ Stuckness.NotStuck ; E [{ Φ }] := by
  iintro ⟨HQ, Hwp⟩
  imod HQ
  iapply Hwp $$ HQ

end CoreRuleChecks

section TotalEctxRuleChecks

example := @twp_lift_base_step
example := @twp_lift_base_step_no_fork
example := @twp_lift_pure_base_step_no_fork
example := @twp_lift_atomic_base_step
example := @twp_lift_atomic_base_step_no_fork
example := @twp_lift_pure_det_base_step_no_fork

end TotalEctxRuleChecks

section HeapLangPureSmoke

open Iris.HeapLang

variable [InvGS_gen .hasNoLC GF]

noncomputable local instance heapIrisGS :
    IrisGS_gen .hasNoLC Iris.HeapLang.Exp GF where
  toStateInterp := ⟨fun _ _ _ _ => iprop(True)⟩
  numLatersPerStep := fun _ => 0
  forkPost := fun _ => iprop(True)
  stateInterp_mono := by
    intro σ ns obs nt
    iintro _
    imodintro
    itrivial

theorem heapLang_add_twp :
    ⊢ WP hl(#1 + #2) @ Stuckness.NotStuck ; ⊤ [{
      fun v : Iris.HeapLang.Val =>
        (iprop(⌜v = hl_val(#3)⌝) : IProp GF) }] := by
  iapply twp_lift_pure_det_base_step_no_fork (e₂ := hl(#3)) rfl
  · intro σ
    refine ⟨hl(#3), σ, [], ?_⟩
    constructor <;> rfl
  · intro σ κ e₂' σ₂ eₜ Hstep
    cases Hstep <;> simp_all [Iris.HeapLang.BinOp.eval]
  · iapply twp.value rfl
    ipureintro
    rfl

end HeapLangPureSmoke

theorem branch_stronglyNormalizing (n initialState : Nat) :
    StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([Expr.branch n], initialState) := by
  apply twp_total (hlc := .hasNoLC) (GF := GF)
    Stuckness.NotStuck (Expr.branch n) initialState
    (fun v : Val => (iprop(⌜v = 0⌝) : IProp GF)) 0 0
  iintro %Hinv
  imodintro
  iexists
    (fun (_ : State) (_ : Nat) (_ : List Obs) (_ : Nat) =>
      (iprop(True) : IProp GF)),
    (fun _ => 0),
    (fun _ : Val => (iprop(True) : IProp GF)),
    (fun _ _ _ _ => by
      iintro _
      imodintro
      itrivial)
  dsimp only
  isplitl []
  · itrivial
  · iintro _
    iapply branch_twp n

theorem branch_singleMachine_stronglyNormalizing (n initialState : Nat) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      (Expr.branch n, initialState) :=
  stronglyNormalizing_expr_of_threadPool
    (branch_stronglyNormalizing n initialState)

theorem put_stronglyNormalizing (n initialState : Nat) :
    StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([Expr.put n], initialState) := by
  apply twp_total (hlc := .hasNoLC) (GF := GF)
    Stuckness.NotStuck (Expr.put n) initialState
    (fun v : Val => (iprop(⌜v = n⌝) : IProp GF)) 0 0
  iintro %Hinv
  imodintro
  iexists
    (fun (_ : State) (_ : Nat) (_ : List Obs) (_ : Nat) =>
      (iprop(True) : IProp GF)),
    (fun _ => 0),
    (fun _ : Val => (iprop(True) : IProp GF)),
    (fun _ _ _ _ => by
      iintro _
      imodintro
      itrivial)
  dsimp only
  isplitl []
  · itrivial
  · iintro _
    iapply put_twp n

/-! Negative semantic boundary checks. -/

example : toVal Expr.stuck = (none : Option Val) := rfl

example (σ : State) : PrimStep.Irreducible (Expr.stuck, σ) := by
  intro κ e₂ σ₂ efs H
  cases H

example (σ : State) : PrimStep.Reducible (Expr.observe, σ) :=
  ⟨[()], .val 0, σ, [], Step.observe σ⟩

example (σ : State) : ¬ PrimStep.ReducibleNoObs (Expr.observe, σ) := by
  rintro ⟨e₂, σ₂, efs, H⟩
  cases H

end Iris.Tests.TotalWeakestPre
