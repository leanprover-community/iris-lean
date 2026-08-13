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

namespace IrisTest.TotalWeakestPre

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
  coe_of_toVal_eq_some := by grind
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
  val_stuck H := by
    cases H <;> rfl

instance : LanguageNoFork Expr State Obs Val where
  no_fork H := by
    cases H <;> rfl

section Proofs

noncomputable abbrev GF := Iris.Examples.ClosedProofs.GF

noncomputable abbrev trivialIrisGS {Expr State Obs Val}
    [Language Expr State Obs Val] [InvGS_gen .hasNoLC GF] : IrisGS_gen .hasNoLC Expr GF where
  toStateInterp := ⟨fun _ _ _ _ => iprop(True)⟩
  numLatersPerStep := fun _ => 0
  forkPost := fun _ => iprop(True)
  stateInterp_mono := fun _ _ _ _ => fupd_intro

theorem tick_pureExec (n : Nat) :
    PureExec True (n + 1) (Expr.tick n) (Expr.val 0) where
  pureExec _ := Nat.rec (.once {
      safe σ := ⟨.val 0, σ, [], Step.tickZero σ⟩
      deterministic | .tickZero _ => ⟨rfl, rfl, rfl, rfl⟩ })
    (fun n IH => .head {
      safe σ := ⟨.tick n, σ, [], Step.tickSucc n σ⟩
      deterministic | .tickSucc _ _ => ⟨rfl, rfl, rfl, rfl⟩ } IH) n

variable [InvGS_gen .hasNoLC GF]

noncomputable local instance testIrisGS : IrisGS_gen .hasNoLC Expr GF :=
  trivialIrisGS (State := State) (Obs := Obs) (Val := Val)

private noncomputable abbrev eqPost (n : Nat) : Val → IProp GF := fun v => iprop(⌜v = n⌝)
private abbrev zeroTwpSpec (e : Expr) : Prop := ⊢ WP e @ Stuckness.NotStuck ; ⊤ [{ eqPost 0 }]

theorem tick_twp (n : Nat) : zeroTwpSpec (.tick n) :=
  (pure_intro rfl).trans (twp.value' (v := 0) (Φ := eqPost 0)) |>.trans (twp_pure_step (tick_pureExec n) trivial)

theorem put_twp (n : Nat) : ⊢ WP (Expr.put n) @ Stuckness.NotStuck ; ⊤ [{ eqPost n }] := by
  iapply twp_lift_atomic_step_no_fork (e₁ := Expr.put n) rfl
  iintro %σ %ns %obs %nt _ !>
  isplit
  · exact BI.pure_intro ⟨.val n, n, [], Step.put n σ⟩
  · iintro %κ %e₂ %σ₂ %efs %⟨⟩
    exact (sep_intro_emp_valid_left (by itrivial) <| sep_intro_emp_valid_left (by itrivial) <| sep_intro_emp_valid_right
      .rfl (exists_intro_trans n <| (pure_intro ⟨rfl, rfl⟩).trans pure_and.2)).trans fupd_intro

theorem branch_twp (n : Nat) : zeroTwpSpec (.branch n) := by
  induction n with
  | zero =>
      exact (pure_intro rfl).trans (twp.value (Φ := eqPost 0) rfl) |>.trans fupd_intro |>.trans <|
        twp_lift_pure_det_step_no_fork (e₂ := Expr.val 0) (fun σ => ⟨.val 0, σ, [], Step.branchZero σ⟩)
          (fun _ _ _ _ _ (.branchZero _) => ⟨rfl, rfl, rfl, rfl⟩)
  | succ n IH =>
      iapply twp_lift_step_no_fork (e₁ := Expr.branch (n + 1)) rfl
      iintro %σ %ns %obs %nt _
      iapply fupd_mask_intro empty_subset
      iintro Hclose
      isplit
      · exact BI.pure_intro ⟨.branch n, σ, [], Step.branchLeft n σ⟩
      · iintro %κ %e₂ %σ₂ %efs %⟨⟩
        all_goals
          imod Hclose with -
          exact (BI.sep_intro_emp_valid_left (BI.pure_intro rfl) <| BI.sep_intro_emp_valid_left (BI.pure_intro rfl) <|
            BI.sep_intro_emp_valid_right .rfl (by first | exact IH | exact tick_twp n)).trans fupd_intro

omit [InvGS_gen .hasNoLC GF] in
private theorem stronglyNormalizing_of_twp {Expr State Obs Val}
    [Language Expr State Obs Val] {e : Expr} {initialState : State} {Φ : Val → IProp GF}
    (Hwp : ∀ [InvGS_gen .hasNoLC GF],
      let _ : IrisGS_gen .hasNoLC Expr GF :=
        trivialIrisGS (State := State) (Obs := Obs) (Val := Val);
      ⊢ WP e @ Stuckness.NotStuck ; ⊤ [{ Φ }]) :
    StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([e], initialState) := by
  apply twp_total (hlc := .hasNoLC) (GF := GF) Stuckness.NotStuck e initialState Φ 0 0
  iintro %Hinv !>
  iexists (fun _ _ _ _ => iprop(True)), (fun _ => 0), (fun _ => iprop(True)), fun _ _ _ _ => fupd_intro
  exact BI.sep_intro_emp_valid_left BI.true_intro <| BI.wand_intro_left (BI.true_intro.trans Hwp)

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
    P ∗ Φ v ⊢ WP e @ Stuckness.NotStuck ; ⊤ [{ w, P ∗ Φ w }] :=
  twp.value (Φ := fun w => iprop(P ∗ Φ w)) inst.into_val.symm

/-- error: iframe: cannot frame R 0 -/
#guard_msgs in
example (R : Nat → IProp GF) :
    R 0 ∗ WP e @ Stuckness.NotStuck ; E [{ fun _ => emp }] ⊢
      WP e @ Stuckness.NotStuck ; E [{ fun _ => iprop(∃ n, R n) }] := by
  iintro ⟨HR, Hwp⟩
  iframe HR

example :
    (|={E}=> P) ∗ (P -∗ WP e @ Stuckness.NotStuck ; E [{ Φ }]) ⊢
      WP e @ Stuckness.NotStuck ; E [{ Φ }] :=
  fupd_wand_right.trans twp.fupd_twp

example :
    (|==> Q) ∗ (Q -∗ WP e @ Stuckness.NotStuck ; E [{ Φ }]) ⊢
      WP e @ Stuckness.NotStuck ; E [{ Φ }] :=
  bupd_wand_right.trans (BIUpdateFUpdate.fupd_of_bupd.trans twp.fupd_twp)

end CoreRuleChecks

section HeapLangPureSmoke

open Iris.HeapLang

variable [InvGS_gen .hasNoLC GF]

noncomputable local instance heapIrisGS : IrisGS_gen .hasNoLC Iris.HeapLang.Exp GF :=
  trivialIrisGS (State := Iris.HeapLang.State) (Obs := Iris.HeapLang.Observation)
    (Val := Iris.HeapLang.Val)

private noncomputable abbrev addPost : Iris.HeapLang.Val → IProp GF := fun v => iprop(⌜v = hl_val(#3)⌝)

theorem heapLang_add_twp : ⊢ WP hl(#1 + #2) @ Stuckness.NotStuck ; ⊤ [{ addPost }] :=
  (pure_intro rfl).trans (twp.value' (v := hl_val(#3)) (Φ := addPost)) |>.trans
    (twp_pure_step Iris.HeapLang.instPureExecBinOp rfl)

end HeapLangPureSmoke

namespace Forking

inductive Expr where
  | done
  | fork

abbrev Val := Unit
abbrev State := Unit
abbrev Obs := Unit

instance : ToVal Expr Val where
  toVal
    | .done => some ()
    | .fork => none
  ofVal _ := .done
  coe_of_toVal_eq_some := by grind
  toVal_coe := by simp

inductive Step : Expr → State → List Obs → Expr → State → List Expr → Prop
  | fork : Step .fork () [] .done () [.done]

instance : PrimStep Expr State (List Obs) where
  primStep
    | (e₁, σ₁), κ, (e₂, σ₂, efs) => Step e₁ σ₁ κ e₂ σ₂ efs

instance : Language Expr State Obs Val where
  val_stuck | .fork => rfl

section

variable [InvGS_gen .hasNoLC GF]

noncomputable local instance forkIrisGS : IrisGS_gen .hasNoLC Expr GF :=
  trivialIrisGS (State := State) (Obs := Obs) (Val := Val)

theorem fork_twp :
    ⊢ WP Expr.fork @ Stuckness.NotStuck ; ⊤ [{
      fun _ : Val => (iprop(True) : IProp GF) }] := by
  iapply twp_lift_atomic_step (e₁ := Expr.fork) rfl
  iintro %⟨⟩ %ns %obs %nt _ !>
  isplit
  · exact BI.pure_intro ⟨.done, (), [.done], Step.fork⟩
  · iintro %κ %e₂ %σ₂ %efs %⟨⟩
    exact (sep_intro_emp_valid_left (PROP := IProp GF) (pure_intro rfl) <| sep_intro_emp_valid_right .rfl <|
      sep_intro_emp_valid_left (exists_intro_trans () <| and_intro (pure_intro rfl) true_intro)
      ((true_intro.trans (twp.value' (v := ()) (Φ := fun _ => iprop(True)))).trans sep_emp.mpr)).trans fupd_intro

end

theorem fork_stronglyNormalizing :
    StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([Expr.fork], ()) :=
  stronglyNormalizing_of_twp (fun [_] => fork_twp)

end Forking

theorem branch_stronglyNormalizing (n initialState : Nat) :
    StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([Expr.branch n], initialState) :=
  stronglyNormalizing_of_twp (fun [_] => branch_twp n)

theorem branch_singleMachine_stronglyNormalizing (n initialState : Nat) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      (Expr.branch n, initialState) :=
  stronglyNormalizing_expr_of_threadPool (branch_stronglyNormalizing n initialState)

theorem put_stronglyNormalizing (n initialState : Nat) :
    StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([Expr.put n], initialState) :=
  stronglyNormalizing_of_twp (fun [_] => put_twp n)

end IrisTest.TotalWeakestPre
