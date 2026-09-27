/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Examples.Refinements.Memoization

/-! # Memoization of pure functions on natural numbers

This file ports the section `pure_nat_memoization` of
`theories/examples/refinements/memoization.v` of Transfinite Iris: memoizing a recursive function
on natural numbers whose source is pure (`natfun_mem_rec_spec`). The purity of the source is used
through the execution trace of the source (`src_log`, `src_get_trace'`).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement.Memoization

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation Iris.Transfinite.Refinement.Examples

set_option linter.unusedSectionVars false

/-- Pure executions (Rocq: `exec`). -/
abbrev Exec (e₁ e₂ : Exp) : Prop := _root_.Relation.TransGen PurePrimStep e₁ e₂

/-- Rocq: `pure_exec_exec`. -/
theorem pureExec_exec {e₁ e₂ : Exp} {n : Nat} {φ : Prop} (hp : PureExec φ (n + 1) e₁ e₂)
    (hφ : φ) : Exec e₁ e₂ := by
  have h := hp.pureExec hφ
  clear hp
  induction n generalizing e₁ with
  | zero =>
    obtain ⟨b, hb, hrest⟩ := Relation.Iterate.succ_head_inv h
    cases hrest
    exact .single hb
  | succ n ih =>
    obtain ⟨b, hb, hrest⟩ := Relation.Iterate.succ_head_inv h
    exact _root_.Relation.TransGen.trans (.single hb) (ih hrest)

/-- Rocq: `exec_frame`. -/
theorem exec_frame {e₁ e₂ : Exp} (K : List ECtxItem) (h : Exec e₁ e₂) :
    Exec (fill K e₁) (fill K e₂) := by
  induction h with
  | single h => exact .single (purePrimStep_fill (fill K) h)
  | tail _ h ih => exact .tail ih (purePrimStep_fill (fill K) h)

variable {GF : BundledGFunctors} [G : RHeapG GF] [N : NatSourceG GF] [S : SeqG GF]

/-- Rocq: `exec_src_update`. -/
theorem exec_src_update {e₁ e₂ : Exp} (j : Nat) (E : CoPset) (h : Exec e₁ e₂) :
    tpoolPointsTo (GF := GF) j e₁ ⊢ srcUpd E (tpoolPointsTo j e₂) := by
  induction h with
  | single h => exact step_pure E j _ _ h
  | tail _ h ih =>
    iintro Hj
    iapply srcUpdate_bind (src := refSrc (GF := GF))
    isplitl [Hj]
    · iapply ih $$ Hj
    · iintro Hj
      iapply step_pure E j _ _ h $$ Hj

/-- Rocq: `natRel`. -/
def natRel (v₁ v₂ : Val) : IProp GF := iprop(∃ n : Nat, ⌜v₁ = hl_val(#(n : Int)) ∧ v₂ = hl_val(#(n : Int))⌝)

instance natRel_persistent (v₁ v₂ : Val) : Persistent (natRel (GF := GF) v₁ v₂) := by
  unfold natRel; infer_instance

instance natRel_timeless (v₁ v₂ : Val) : Timeless (natRel (GF := GF) v₁ v₂) := by
  unfold natRel
  exact @UPred.exists_timeless' _ _ _ _ _ _ fun _ => inferInstance

/-- Rocq: `natfun_refines`. -/
def natfunRefines (g f : Val) : IProp GF :=
  iprop(□ ∀ n : Nat, ∀ K : List ECtxItem, src (fill K hl(v(&f) #(n : Int))) -∗
    rseq ⊤ hl(v(&g) #(n : Int)) fun v =>
      iprop(∃ n' : Nat, ⌜v = hl_val(#(n' : Int))⌝ ∗ src (fill K (v : Exp))))

instance natfunRefines_persistent (g f : Val) : Persistent (natfunRefines (GF := GF) g f) := by
  unfold natfunRefines; infer_instance

/-- Rocq: `natfun_pure`. -/
def NatfunPure (f : Val) : Prop :=
  ∀ (n₁ n₂ : Nat) (tp₁ tp₂ : List Exp) (σ₁ σ₂ : State) (K : List ECtxItem),
    FromMathlib.Relation.ReflTransGen ErasedStep
      (fill K hl(v(&f) #(n₁ : Int)) :: tp₁, σ₁) (fill K hl(#(n₂ : Int)) :: tp₂, σ₂) →
    ∀ K', FromMathlib.Relation.ReflTransGen PurePrimStep
      (fill K' hl(v(&f) #(n₁ : Int))) (fill K' hl(#(n₂ : Int)))

/-- The results recorded for a pure function (the relation `R` of the proof of
`natfun_mem_rec_spec`). -/
def natR (f : Val) (e : Exp) (v : Val) : IProp GF :=
  iprop(⌜∃ (K : List ECtxItem) (n₁ n₂ : Nat) (tp₁ tp₂ : List Exp) (σ₁ σ₂ : State),
    e = hl(v(&f) #(n₁ : Int)) ∧ v = hl_val(#(n₂ : Int)) ∧
    FromMathlib.Relation.ReflTransGen ErasedStep
      (fill K hl(v(&f) #(n₁ : Int)) :: tp₁, σ₁) (fill K hl(#(n₂ : Int)) :: tp₂, σ₂)⌝)

/-- Comparable values: unboxed values. -/
def unboxed (v : Val) : IProp GF := iprop(⌜v.isUnboxed = true⌝)

/-- Equality of values. -/
def valEq (v₁ v₂ : Val) : IProp GF := iprop(⌜v₁ = v₂⌝)

theorem natRel_unboxed (v v' : Val) : natRel (GF := GF) v v' ⊢ unboxed v := by
  unfold natRel unboxed
  iintro ⟨%n, %⟨rfl, -⟩⟩
  ipureintro; rfl

theorem natRel_proper (v₁ v₁' v₂ : Val) : valEq (GF := GF) v₁ v₁' ∗ natRel v₁' v₂ ⊢ natRel v₁ v₂ := by
  unfold valEq
  iintro ⟨%rfl, H⟩
  iexact H

theorem eqHeaplang_spec :
    ⊢ eqfun (src := refSrc (GF := GF)) unboxed eqHeaplang valEq := by
  unfold eqfun texan unboxed valEq
  iintro %n₁ %n₂ !> %Φ ⟨%h₁, %h₂⟩ Hpost
  have hcs : n₁.compareSafe n₂ = true := by simp [Val.compareSafe, h₁]
  unfold eqHeaplang
  twp_pures
  iapply Hpost
  iexists (n₁ == n₂)
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact h₁
  isplitr
  · ipureintro; exact h₂
  cases h : (n₁ == n₂) with
  | true =>
    simp only [↓reduceIte]
    ipureintro
    exact beq_iff_eq.mp h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro %heq
    subst heq
    simp at h

instance natR_timeless (f : Val) (e : Exp) (v : Val) : Timeless (natR (GF := GF) f e v) := by
  unfold natR; infer_instance

instance unboxed_timeless (v : Val) : Timeless (unboxed (GF := GF) v) := by
  unfold unboxed; infer_instance

instance valEq_persistent (v₁ v₂ : Val) : Persistent (valEq (GF := GF) v₁ v₂) := by
  unfold valEq; infer_instance

/-- The source results of a pure function are reached by pure steps. -/
theorem natR_eval (f : Val) (hpure : NatfunPure f) (e : Exp) (v : Val) :
    natR (GF := GF) f e v ⊢ evalS e v := by
  unfold natR evalS
  iintro %⟨K, n₁, n₂, tp₁, tp₂, σ₁, σ₂, rfl, rfl, hrtc⟩ %K' Hsrc
  have h := hpure n₁ n₂ tp₁ tp₂ σ₁ σ₂ K hrtc K'
  rcases FromMathlib.Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, hrest⟩
  · exfalso
    have := EvContext.fill_inj heq
    cases this
  · iapply exec_src_update 0 ⊤ _ $$ Hsrc
    exact FromMathlib.Relation.ReflTransGen.head_induction_on (motive := fun a _ =>
      ∀ b, PurePrimStep b a → Exec b (fill K' hl(#(n₂ : Int)))) hrest
      (fun b hb => .single hb)
      (fun h' _ ih b hb => _root_.Relation.TransGen.trans (.single hb) (ih _ h')) _ hc

/-- Rocq: `natfun_mem_rec_spec`. -/
theorem natfun_mem_rec_spec (F f : Val) (hpure : NatfunPure f) :
    (□ ∀ g, ▷ natfunRefines g f -∗ rseq ⊤ hl(v(&F) v(&g)) fun h => natfunRefines h f) ⊢
      rseq ⊤ hl(v(&memRec) v(&eqHeaplang) v(&F)) fun h => natfunRefines (GF := GF) h f := by
  iintro #Href
  ihave H := mem_rec_spec (natR f) natRel natRel unboxed valEq natRel_unboxed natRel_proper
    eqHeaplang F f $$ []
  · isplitl []
    · iapply eqHeaplang_spec
    isplitl []
    · iintro !> %g Himpl
      unfold rseq seq
      iintro Hna
      ihave Href' := Href $$ %g [Himpl] Hna
      · inext
        icases Himpl with #Himpl
        unfold natfunRefines implements rseq seq
        iintro !> %n %K Hsrc Hna
        ihave H := Himpl $$ %(hl_val(#(n : Int))) %(hl_val(#(n : Int))) %K [] Hsrc Hna
        · unfold natRel
          iexists n
          ipureintro; exact ⟨rfl, rfl⟩
        iapply rwpR_wand $$ H
        iintro %v ⟨Hna, %v', Hrel, Hsrc, -⟩
        unfold natRel
        icases Hrel with ⟨%n', %⟨rfl, rfl⟩⟩
        iframe Hna
        iexists n'
        iframe Hsrc
        ipureintro; rfl
      iapply rwpR_wand $$ Href'
      iintro %h ⟨Hna, #Hnatfun⟩
      iframe Hna
      unfold implements natfunRefines rseq seq
      iintro !> %x %x' %K #HPre Hsrc Hna
      unfold natRel
      icases HPre with ⟨%n, %⟨rfl, rfl⟩⟩
      iapply rwp_weaken_src' rfl
      iapply weakSrcUpd_bind
      isplitl [Hsrc]
      · iapply src_log ⊤ 0 _ $$ Hsrc
      iintro ⟨Hsrc, %tp, %σ, %i, %hlook, #Hidx⟩
      iapply weakSrcUpd_return
      ihave Hn := Hnatfun $$ %n %K Hsrc Hna
      iapply rwp_strong_mono' (src := refSrc (GF := GF)) (ι := heapRefIrisGS)
        (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ Hn
      iintro %σ' %m %a %v ⟨Hinterp, Hstate, Hna, %n', %rfl, Hsrc⟩
      ihave H := src_get_trace' 0 _ i (tp, σ) a $$ Hsrc Hidx Hinterp
      icases H with ⟨Hsrc, Hinterp, %⟨tp', σ'', hlook', hrtc⟩⟩
      imodintro
      iframe Hinterp Hstate Hna
      iexists hl_val(#(n' : Int))
      isplitr [Hsrc]
      · iexists n'
        ipureintro; exact ⟨rfl, rfl⟩
      iframe Hsrc
      iintro !> %x'' #HPre''
      icases HPre'' with ⟨%n'', %⟨heq, rfl⟩⟩
      cases tp with
      | nil => simp at hlook
      | cons e₀ tp₁ =>
        cases tp' with
        | nil => simp at hlook'
        | cons e₁ tp₂ =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook hlook'
          subst hlook hlook'
          have hnn : n = n'' := by
            injections heq
          subst hnn
          iexists hl_val(#(n' : Int))
          isplitr
          · iintro !>
            unfold natR
            ipureintro
            exact ⟨K, n, n', tp₁, tp₂, σ, σ'', rfl, rfl, hrtc⟩
          iexists n'
          ipureintro; exact ⟨rfl, rfl⟩
    · iintro !> %e %v HR
      iapply natR_eval f hpure e v $$ HR
  unfold rseq seq
  iintro Hna
  ihave H := H $$ Hna
  iapply rwpR_wand $$ H
  iintro %h ⟨Hna, #Himpl⟩
  iframe Hna
  unfold natfunRefines implements rseq seq
  iintro !> %n %K Hsrc Hna
  ihave H := Himpl $$ %(hl_val(#(n : Int))) %(hl_val(#(n : Int))) %K [] Hsrc Hna
  · unfold natRel
    iexists n
    ipureintro; exact ⟨rfl, rfl⟩
  iapply rwpR_wand $$ H
  iintro %v ⟨Hna, %v', Hrel, Hsrc, -⟩
  unfold natRel
  icases Hrel with ⟨%n', %⟨rfl, rfl⟩⟩
  iframe Hna
  iexists n'
  iframe Hsrc
  ipureintro; rfl

end Iris.Transfinite.Refinement.Memoization
