/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Examples.Refinements.Tactics

/-! # Examples of refinements

This file ports `theories/examples/refinements/examples.v` of Transfinite Iris: refinements
between search functions (`first`), and between the exponential and the linear implementation of
the Fibonacci function, in both directions.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement.Examples

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language

/-! ## Code -/

/-- Rocq: `first`. -/
def first : Val := hl_val% rec first p x := if p x then x else first p (x + #1)

/-- Rocq: `f_ex`. -/
def fEx : Val := hl_val% λ x, #(41 : Int) ≤ x - #1

/-- Rocq: `g_ex`. -/
def gEx : Val := hl_val% λ x, #(42 : Int) ≤ x

/-- Rocq: `fib_exp`. -/
def fibExp : Val := hl_val%
  rec fib n := if n ≤ #(1 : Int) then n else fib (n - #1) + fib (n - #2)

/-- Rocq: `fibl`. -/
def fibl : Val := hl_val%
  rec f n := if n = #(0 : Int) then (#(0 : Int), #(1 : Int)) else
    let r := f (n - #1); let x := fst(r); let y := snd(r); (y, x + y)

/-- Rocq: `fib_lin`. -/
def fibLin : Val := hl_val% λ x, fst(&fibl x)

/-- Rocq: `fib_spec`. -/
def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec (n + 1) + fibSpec n

variable {GF : BundledGFunctors} [G : RHeapG GF] [N : NatSourceG GF] [S : SeqG GF]

/-- The refinement weakest precondition of the refinement logic. -/
abbrev rwpR (e : Exp) (Φ : Val → IProp GF) : IProp GF :=
  rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) .NotStuck ⊤ e Φ

theorem rwpR_wand {e : Exp} {Φ Ψ : Val → IProp GF} :
    ⊢ rwpR e Φ -∗ (∀ v, Φ v -∗ Ψ v) -∗ rwpR e Ψ :=
  rwp_wand (src := refSrc (GF := GF)) (ι := heapRefIrisGS)

/-- Rocq: `fib_exp_wp`. -/
theorem fib_exp_wp (n : Nat) :
    ⊢ rwpR (GF := GF) hl(v(&fibExp) #(n : Int)) fun v => iprop(⌜v = hl_val(#(fibSpec n : Int))⌝) := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
    match n with
    | 0 =>
      unfold fibExp
      twp_pures
      rw [decide_eq_true (show ((0 : Nat) : Int) ≤ 1 by omega)]
      twp_pures
      ipureintro; rfl
    | 1 =>
      unfold fibExp
      twp_pures
      rw [decide_eq_true (show ((1 : Nat) : Int) ≤ 1 by omega)]
      twp_pures
      ipureintro; rfl
    | n + 2 =>
      twp_rec
      twp_pures
      rw [decide_eq_false (show ¬ ((n + 2 : Nat) : Int) ≤ 1 by omega)]
      twp_pures
      rw [show ((n + 2 : Nat) : Int) - 2 = ((n : Nat) : Int) by omega]
      ihave H := IH n (by omega)
      twp_apply rwpR_wand $$ H
      iintro %v %rfl
      twp_pures
      rw [show ((n + 2 : Nat) : Int) - 1 = ((n + 1 : Nat) : Int) by omega]
      ihave H := IH (n + 1) (by omega)
      twp_apply rwpR_wand $$ H
      iintro %v %rfl
      twp_pures
      ipureintro
      simp [fibSpec]

/-- Rocq: `fibl_wp`. -/
theorem fibl_wp (n : Nat) :
    ⊢ rwpR (GF := GF) hl(v(&fibl) #(n : Int))
      fun v => iprop(⌜v = hl_val((#(fibSpec n : Int), #(fibSpec (n + 1) : Int)))⌝) := by
  induction n with
  | zero =>
    twp_rec
    twp_pures
    rw [show (hl_val(#((0 : Nat) : Int)) == hl_val(#(0 : Int))) = true by simp]
    twp_pures
    ipureintro; rfl
  | succ n ih =>
    twp_rec
    twp_pures
    rw [show (hl_val(#((n + 1 : Nat) : Int)) == hl_val(#(0 : Int))) = false by simp; omega]
    twp_pures
    rw [show ((n + 1 : Nat) : Int) - 1 = ((n : Nat) : Int) by omega]
    ihave H := ih
    twp_apply rwpR_wand $$ H
    iintro %v %rfl
    twp_pures
    ipureintro
    simp [fibSpec]; omega

/-- Rocq: `fib_lin_wp`. -/
theorem fib_lin_wp (n : Nat) :
    ⊢ rwpR (GF := GF) hl(v(&fibLin) #(n : Int)) fun v => iprop(⌜v = hl_val(#(fibSpec n : Int))⌝) := by
  twp_rec
  ihave H := fibl_wp (GF := GF) n
  twp_apply rwpR_wand $$ H
  iintro %v %rfl
  twp_pures
  ipureintro; rfl

/-- Evaluation in the source (Rocq: `eval`). -/
def eval (e : Exp) (v : Val) : IProp GF :=
  iprop(∀ K : List ECtxItem, src (fill K e) -∗ weakSrcUpd ⊤ (src (fill K (v : Exp))))

/-- Rocq: `fib_exp_upd`. -/
theorem fib_exp_upd (n : Nat) : ⊢ eval (GF := GF) hl(v(&fibExp) #(n : Int)) hl_val(#(fibSpec n : Int)) := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
    unfold eval
    iintro %K Hsrc
    match n with
    | 0 =>
      src_rec Hsrc
      src_pures Hsrc
      rw [decide_eq_true (show ((0 : Nat) : Int) ≤ 1 by omega)]
      src_pures Hsrc
      iapply weakSrcUpd_return
      rw [show fibSpec 0 = 0 from rfl]
      iexact Hsrc
    | 1 =>
      src_rec Hsrc
      src_pures Hsrc
      rw [decide_eq_true (show ((1 : Nat) : Int) ≤ 1 by omega)]
      src_pures Hsrc
      iapply weakSrcUpd_return
      rw [show fibSpec 1 = 1 from rfl]
      iexact Hsrc
    | n + 2 =>
      src_rec Hsrc
      src_pures Hsrc
      rw [decide_eq_false (show ¬ ((n + 2 : Nat) : Int) ≤ 1 by omega)]
      src_pures Hsrc
      rw [show ((n + 2 : Nat) : Int) - 2 = ((n : Nat) : Int) by omega]
      src_bind (v(&fibExp) #((n : Nat) : Int)) in Hsrc
      ihave H := IH n (by omega)
      unfold eval
      ihave H := H $$ Hsrc
      iapply weakSrcUpd_bind
      iframe H
      iintro Hsrc
      src_pures Hsrc
      rw [show ((n + 2 : Nat) : Int) - 1 = ((n + 1 : Nat) : Int) by omega]
      src_bind (v(&fibExp) #((n + 1 : Nat) : Int)) in Hsrc
      ihave H := IH (n + 1) (by omega)
      unfold eval
      ihave H := H $$ Hsrc
      iapply weakSrcUpd_bind
      iframe H
      iintro Hsrc
      src_pures Hsrc
      iapply weakSrcUpd_return
      rw [show fibSpec (n + 2) = fibSpec (n + 1) + fibSpec n from rfl]
      push_cast
      rw [Int.add_comm]
      iexact Hsrc

end Iris.Transfinite.Refinement.Examples
