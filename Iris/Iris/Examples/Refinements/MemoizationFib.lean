/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Examples.Refinements.MemoizationNat

/-! # Memoized Fibonacci

This file ports the section `fibonacci` of `theories/examples/refinements/memoization.v` of
Transfinite Iris: the memoized Fibonacci function (`memoize` of `fib`, and `mem_rec` of the
template `fib_template`) refines the exponential Fibonacci function.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement.Memoization

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation Iris.Transfinite.Refinement.Examples

set_option linter.unusedSectionVars false

/-- The body of the Fibonacci function (Rocq: `Fib`). -/
def Fib (fib : Val) (n : Exp) : Exp := hl(
  if &n = #(0 : Int) then #(0 : Int)
  else if &n = #(1 : Int) then #(1 : Int)
  else let n' := &n - #1; let n'' := &n - #2; v(&fib) n' + v(&fib) n'')

/-- Rocq: `fib`. -/
def fib : Val := hl_val%
  rec fib n :=
    if n = #(0 : Int) then #(0 : Int)
    else if n = #(1 : Int) then #(1 : Int)
    else let n' := n - #1; let n'' := n - #2; fib n' + fib n''

/-- Rocq: `fib_template`. -/
def fibTemplate : Val := hl_val%
  λ fib n,
    if n = #(0 : Int) then #(0 : Int)
    else if n = #(1 : Int) then #(1 : Int)
    else let n' := n - #1; let n'' := n - #2; fib n' + fib n''

theorem rexec_exec {e₁ e₂ : Exp} (h : RExec e₁ e₂) (hne : e₁ ≠ e₂) : Exec e₁ e₂ := by
  rcases FromMathlib.Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, hrest⟩
  · exact absurd heq hne
  · exact FromMathlib.Relation.ReflTransGen.head_induction_on (motive := fun a _ =>
      ∀ b, PurePrimStep b a → Exec b e₂) hrest
      (fun b hb => .single hb)
      (fun h' _ ih b hb => _root_.Relation.TransGen.trans (.single hb) (ih _ h')) _ hc

theorem exec_trans {e₁ e₂ e₃ : Exp} (h₁ : Exec e₁ e₂) (h₂ : Exec e₂ e₃) : Exec e₁ e₃ :=
  _root_.Relation.TransGen.trans h₁ h₂

/-- Rocq: `Fib_zero`. -/
theorem Fib_zero (fib : Val) : Exec (Fib fib hl(#(0 : Int))) hl(#(0 : Int)) := by
  refine rexec_exec ?_ (by simp [Fib])
  unfold Fib
  rexec_pures

/-- Rocq: `Fib_one`. -/
theorem Fib_one (fib : Val) : Exec (Fib fib hl(#(1 : Int))) hl(#(1 : Int)) := by
  refine rexec_exec ?_ (by simp [Fib])
  unfold Fib
  rexec_pures

/-- Rocq: `fib_Fib`. -/
theorem fib_Fib (v : Val) : Exec hl(v(&fib) v(&v)) (Fib fib (v : Exp)) := by
  refine rexec_exec ?_ (by simp [Fib])
  rexec_rec
  exact .refl

/-- Rocq: `Fib_rec`. -/
theorem Fib_rec (fib : Val) (n : Nat) :
    Exec (Fib fib hl(#((n + 2 : Nat) : Int)))
      hl(v(&fib) #((n + 1 : Nat) : Int) + v(&fib) #((n : Nat) : Int)) := by
  refine rexec_exec ?_ (by simp [Fib])
  unfold Fib
  rexec_pures
  rw [decide_eq_false (show ¬ ((n + 2 : Nat) : Int) = 0 by omega)]
  rexec_pures
  rw [decide_eq_false (show ¬ ((n + 2 : Nat) : Int) = 1 by omega)]
  rexec_pures
  rw [show ((n + 2 : Nat) : Int) - 1 = ((n + 1 : Nat) : Int) by omega,
    show ((n + 2 : Nat) : Int) - 2 = ((n : Nat) : Int) by omega]
  exact .refl

theorem plus_exec (a b : Nat) :
    Exec hl(#(a : Int) + #(b : Int)) hl(#((a + b : Nat) : Int)) := by
  refine rexec_exec ?_ (by simp)
  rexec_pures

variable {GF : BundledGFunctors} [G : RHeapG GF] [N : NatSourceG GF] [S : SeqG GF]

/-- Pure executions as a relation between expressions and values (Rocq: `execV`). -/
def execV (e : Exp) (v : Val) : IProp GF := iprop(⌜Exec e (v : Exp)⌝)

instance execV_timeless (e : Exp) (v : Val) : Timeless (execV (GF := GF) e v) := by
  unfold execV; infer_instance

instance execV_persistent (e : Exp) (v : Val) : Persistent (execV (GF := GF) e v) := by
  unfold execV; infer_instance

/-- Rocq: `fib_fundamental_core`. -/
theorem fib_fundamental_core (g : Val) (K : List ECtxItem) (n : Nat) :
    ▷ implements execV natRel natRel g fib ∗ src (fill K hl(v(&fib) #(n : Int))) ⊢
      rseq ⊤ (Fib g hl(#(n : Int))) fun v => iprop(∃ m : Nat, ⌜v = hl_val(#(m : Int))⌝ ∗
        src (fill K hl(#(m : Int))) ∗ □ execV (GF := GF) hl(v(&fib) #(n : Int)) hl_val(#(m : Int))) := by
  unfold rseq seq
  iintro ⟨#IH, Hsrc⟩ Hna
  match n with
  | 0 =>
    iapply rwp_take_step (src := refSrc (GF := GF)) (P := src (fill K hl(#((0 : Nat) : Int)))) rfl
      $$ [Hna] [Hsrc]
    · iintro Hsrc
      iapply rswp_do_step (src := refSrc (GF := GF))
      inext
      unfold Fib
      twp_pure
      rw [decide_eq_true (show ((0 : Nat) : Int) = 0 by omega)]
      twp_pures
      iframe Hna
      iexists 0
      iframe Hsrc
      isplitr
      · ipureintro; rfl
      iintro !>
      unfold execV
      ipureintro
      exact exec_trans (fib_Fib _) (Fib_zero fib)
    · iapply exec_src_update 0 ⊤ (exec_frame K (exec_trans (fib_Fib _) (Fib_zero fib))) $$ Hsrc
  | 1 =>
    iapply rwp_take_step (src := refSrc (GF := GF)) (P := src (fill K hl(#((1 : Nat) : Int)))) rfl
      $$ [Hna] [Hsrc]
    · iintro Hsrc
      iapply rswp_do_step (src := refSrc (GF := GF))
      inext
      unfold Fib
      twp_pure
      rw [decide_eq_false (show ¬ ((1 : Nat) : Int) = 0 by omega)]
      twp_pures
      rw [decide_eq_true (show ((1 : Nat) : Int) = 1 by omega)]
      twp_pures
      iframe Hna
      iexists 1
      iframe Hsrc
      isplitr
      · ipureintro; rfl
      iintro !>
      unfold execV
      ipureintro
      exact exec_trans (fib_Fib _) (Fib_one fib)
    · iapply exec_src_update 0 ⊤ (exec_frame K (exec_trans (fib_Fib _) (Fib_one fib))) $$ Hsrc
  | n + 2 =>
    iapply rwp_take_step (src := refSrc (GF := GF))
      (P := src (fill K hl(v(&fib) #((n + 1 : Nat) : Int) + v(&fib) #((n : Nat) : Int)))) rfl
      $$ [Hna] [Hsrc]
    · iintro Hsrc
      iapply rswp_do_step (src := refSrc (GF := GF))
      inext
      unfold Fib
      twp_pure
      rw [decide_eq_false (show ¬ ((n + 2 : Nat) : Int) = 0 by omega)]
      twp_pures
      rw [decide_eq_false (show ¬ ((n + 2 : Nat) : Int) = 1 by omega)]
      twp_pures
      rw [show ((n + 2 : Nat) : Int) - 2 = ((n : Nat) : Int) by omega]
      -- the recursive call for `n`
      twp_bind (v(&g) #((n : Nat) : Int))
      src_bind (v(&fib) #((n : Nat) : Int)) in Hsrc
      unfold implements rseq seq
      ihave H₁ := IH $$ %(hl_val(#((n : Nat) : Int))) %(hl_val(#((n : Nat) : Int))) %_ [] Hsrc Hna
      · unfold natRel
        iexists n
        ipureintro; exact ⟨rfl, rfl⟩
      twp_apply rwpR_wand $$ H₁
      iintro %v ⟨Hna, %v₁, Hrel₁, Hsrc, #Hev₁⟩
      unfold natRel
      icases Hrel₁ with ⟨%m, %⟨rfl, rfl⟩⟩
      twp_pures
      rw [show ((n + 2 : Nat) : Int) - 1 = ((n + 1 : Nat) : Int) by omega]
      -- the recursive call for `n + 1`
      twp_bind (v(&g) #((n + 1 : Nat) : Int))
      src_bind (v(&fib) #((n + 1 : Nat) : Int)) in Hsrc
      ihave H₂ := IH $$ %(hl_val(#((n + 1 : Nat) : Int))) %(hl_val(#((n + 1 : Nat) : Int))) %_ []
        Hsrc Hna
      · iexists n + 1
        ipureintro; exact ⟨rfl, rfl⟩
      twp_apply rwpR_wand $$ H₂
      iintro %v ⟨Hna, %v₂, Hrel₂, Hsrc, #Hev₂⟩
      icases Hrel₂ with ⟨%m', %⟨rfl, rfl⟩⟩
      src_pure Hsrc
      twp_pures
      iframe Hna
      iexists m' + m
      isplitr
      · ipureintro; rfl
      rw [← Int.natCast_add m' m]
      iframe Hsrc
      ihave ⟨%w₁, #He₁, %⟨k₁, hk₁, rfl⟩⟩ := Hev₁ $$ %(hl_val(#((n : Nat) : Int))) []
      · iexists n
        ipureintro; exact ⟨rfl, rfl⟩
      ihave ⟨%w₂, #He₂, %⟨k₂, hk₂, rfl⟩⟩ := Hev₂ $$ %(hl_val(#((n + 1 : Nat) : Int))) []
      · iexists n + 1
        ipureintro; exact ⟨rfl, rfl⟩
      unfold execV
      icases He₁ with %he₁
      icases He₂ with %he₂
      iintro !>
      ipureintro
      have hk₁' : k₁ = m := by simp only [Val.lit.injEq, BaseLit.int.injEq] at hk₁; omega
      have hk₂' : k₂ = m' := by simp only [Val.lit.injEq, BaseLit.int.injEq] at hk₂; omega
      subst hk₁' hk₂'
      exact exec_trans (fib_Fib _) (exec_trans (Fib_rec fib n)
        (exec_trans (exec_frame [.binOpR .plus hl(v(&fib) #((n + 1 : Nat) : Int))] he₁)
          (exec_trans (exec_frame [.binOpL .plus hl_val(#((k₁ : Nat) : Int))] he₂)
            (plus_exec k₂ k₁))))
    · iapply exec_src_update 0 ⊤ (exec_frame K (exec_trans (fib_Fib _) (Fib_rec fib n))) $$ Hsrc

/-- The postcondition of `fib_fundamental_core` implies the one of `implements`. -/
theorem fib_post (n : Nat) (K : List ECtxItem) (v : Val) :
    (∃ m : Nat, ⌜v = hl_val(#(m : Int))⌝ ∗ src (fill K hl(#(m : Int))) ∗
      □ execV (GF := GF) hl(v(&fib) #(n : Int)) hl_val(#(m : Int))) ⊢
      ∃ v' : Val, natRel v v' ∗ src (fill K (v' : Exp)) ∗
        □ (∀ x', natRel hl_val(#(n : Int)) x' -∗
          ∃ v', □ execV hl(v(&fib) v(&x')) v' ∗ natRel v v') := by
  iintro ⟨%m, %rfl, Hsrc, #Hex⟩
  iexists hl_val(#(m : Int))
  isplitr [Hsrc]
  · unfold natRel
    iexists m
    ipureintro; exact ⟨rfl, rfl⟩
  iframe Hsrc
  iintro !> %x' Hrel
  unfold natRel
  icases Hrel with ⟨%k, %⟨hk, rfl⟩⟩
  have : k = n := by simp only [Val.lit.injEq, BaseLit.int.injEq] at hk; omega
  subst this
  iexists hl_val(#(m : Int))
  isplitr
  · iexact Hex
  iexists m
  ipureintro; exact ⟨rfl, rfl⟩

/-- Rocq: `fib_sound`. -/
theorem fib_sound : ⊢ implements (GF := GF) execV natRel natRel fib fib := by
  iloeb as IH
  unfold implements
  iintro !> %v %v' %K #HPre Hsrc
  unfold rseq seq
  iintro Hna
  unfold natRel
  icases HPre with ⟨%n, %⟨rfl, rfl⟩⟩
  have Hcore := fib_fundamental_core (GF := GF) fib K n
  unfold rseq seq Fib at Hcore
  twp_rec
  ihave H := Hcore $$ [Hsrc] Hna
  · iframe Hsrc
    unfold implements rseq seq natRel
    iexact IH
  iapply rwpR_wand $$ H
  iintro %w ⟨Hna, Hpost⟩
  iframe Hna
  ihave Hp := fib_post n K w $$ Hpost
  unfold natRel
  dsimp only
  iexact Hp

/-- Rocq: `fib_template_sound`. -/
theorem fib_template_sound (g : Val) :
    ▷ implements (GF := GF) execV natRel natRel g fib ⊢
      rseq ⊤ hl(v(&fibTemplate) v(&g)) fun h => implements execV natRel natRel h fib := by
  unfold rseq seq
  iintro #H Hna
  unfold fibTemplate
  twp_pures
  iframe Hna
  unfold implements
  iintro !> %v %v' %K #HPre Hsrc
  unfold rseq seq
  iintro Hna
  unfold natRel
  icases HPre with ⟨%n, %⟨rfl, rfl⟩⟩
  have Hcore := fib_fundamental_core (GF := GF) g K n
  unfold rseq seq Fib at Hcore
  twp_pure
  ihave H := Hcore $$ [Hsrc] Hna
  · iframe Hsrc
    unfold implements rseq seq natRel
    iexact H
  iapply rwpR_wand $$ H
  iintro %w ⟨Hna, Hpost⟩
  iframe Hna
  ihave Hp := fib_post n K w $$ Hpost
  unfold natRel
  dsimp only
  iexact Hp

theorem execV_eval (e : Exp) (v : Val) : execV (GF := GF) e v ⊢ evalS e v := by
  unfold execV evalS
  iintro %hex %K Hsrc
  iapply exec_src_update 0 ⊤ (exec_frame K hex) $$ Hsrc

/-- Rocq: `fib_memoized`. -/
theorem fib_memoized :
    ⊢ rseq ⊤ hl(v(&memoize) v(&eqHeaplang) v(&fib))
      fun h => implements (GF := GF) execV natRel natRel h fib := by
  iapply memoize_spec execV natRel natRel unboxed valEq natRel_unboxed natRel_proper
  isplitl []
  · iapply eqHeaplang_spec
  isplitl []
  · iapply fib_sound
  iintro !> %e %v H
  iapply execV_eval e v $$ H

/-- Rocq: `fib_deep_memoized`. -/
theorem fib_deep_memoized :
    ⊢ rseq ⊤ hl(v(&memRec) v(&eqHeaplang) v(&fibTemplate))
      fun h => implements (GF := GF) execV natRel natRel h fib := by
  iapply mem_rec_spec execV natRel natRel unboxed valEq natRel_unboxed natRel_proper
  isplitl []
  · iapply eqHeaplang_spec
  isplitl []
  · iintro !> %g Hg
    iapply fib_template_sound g $$ Hg
  iintro !> %e %v H
  iapply execV_eval e v $$ H

/-- Rocq: `fib_deep_memoized_instantiate`. -/
theorem fib_deep_memoized_instantiate (n : Nat) (K : List ECtxItem) :
    src (GF := GF) (fill K hl(v(&fib) #(n : Int))) ⊢
      rseq ⊤ hl(v(&memRec) v(&eqHeaplang) v(&fibTemplate) #(n : Int))
        fun w => iprop(∃ m : Nat, ⌜w = hl_val(#(m : Int))⌝ ∗ src (fill K hl(#(m : Int)))) := by
  unfold rseq seq
  iintro Hsrc Hna
  twp_bind (v(&memRec) v(&eqHeaplang) v(&fibTemplate))
  ihave H := fib_deep_memoized (GF := GF)
  unfold rseq seq
  ihave H := H $$ Hna
  twp_apply rwpR_wand $$ H
  iintro %f ⟨Hna, Himpl⟩
  unfold implements rseq seq
  ihave Himpl := Himpl $$ %(hl_val(#(n : Int))) %(hl_val(#(n : Int))) %K [] Hsrc Hna
  · unfold natRel
    iexists n
    ipureintro; exact ⟨rfl, rfl⟩
  iapply rwpR_wand $$ Himpl
  iintro %v ⟨Hna, %w, Hrel, Hsrc, -⟩
  unfold natRel
  icases Hrel with ⟨%m, %⟨rfl, rfl⟩⟩
  iframe Hna
  iexists m
  iframe Hsrc
  ipureintro; rfl

end Iris.Transfinite.Refinement.Memoization
