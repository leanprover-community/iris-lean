/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Examples.Refinements.MemoizationTf
public import Iris.Examples.Refinements.MemoizationFib
public import Iris.Instances.Lib.InvariantsTransfinite

/-! # Memoized Levenshtein distance

This file ports the section `levenshtein` of `theories/examples/refinements/memoization.v` of
Transfinite Iris: the memoized Levenshtein distance on C-style null-terminated strings refines the
exponential implementation. Strings are immutable and shared through invariants
(`imm_stringRel`).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement.Memoization

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation Iris.Transfinite.Refinement.Examples

set_option linter.unusedSectionVars false

/-! ## Code -/

/-- Rocq: `strlen_template`. -/
def strlenTemplate : Val := hl_val%
  λ strlen l,
    let c := !l;
    if c = #(0 : Int) then #(0 : Int)
    else let r := strlen (l +ₗ #(1 : Int)); #(1 : Int) + r

/-- Rocq: `strlen`. -/
def strlen : Val := hl_val% rec strlen l := &strlenTemplate strlen l

/-- The body of `strlen` (Rocq: `Strlen`). -/
def Strlen (strlen : Val) (l : Exp) : Exp := hl(
  let c := !(&l);
  if c = #(0 : Int) then #(0 : Int)
  else let r := v(&strlen) (&l +ₗ #(1 : Int)); #(1 : Int) + r)

/-- Rocq: `min2`. -/
def min2 : Val := hl_val% λ n1 n2, if n1 ≤ n2 then n1 else n2

/-- Rocq: `min3`. -/
def min3 : Val := hl_val% λ n1 n2 n3, &min2 (&min2 n1 n2) n3

/-- Rocq: `lev_template`. -/
def levTemplate : Val := hl_val%
  λ strlen lev s12,
    let s1 := fst(s12);
    let s2 := snd(s12);
    let c1 := !s1;
    if c1 = #(0 : Int) then strlen s2 else
    let c2 := !s2;
    if c2 = #(0 : Int) then strlen s1 else
    if c1 = c2 then lev ((s1 +ₗ #(1 : Int), s2 +ₗ #(1 : Int)))
    else
      let r1 := lev ((s1, s2 +ₗ #(1 : Int)));
      let r2 := lev ((s1 +ₗ #(1 : Int), s2));
      let r3 := lev ((s1 +ₗ #(1 : Int), s2 +ₗ #(1 : Int)));
      #(1 : Int) + &min3 r1 r2 r3

/-- Rocq: `lev`. -/
def lev : Val := hl_val% rec lev s12 := &levTemplate &strlen lev s12

/-- The body of `lev` (Rocq: `Lev`). -/
def Lev (strlen lev : Val) (s12 : Exp) : Exp := hl(
  let s1 := fst(&s12);
  let s2 := snd(&s12);
  let c1 := !s1;
  if c1 = #(0 : Int) then v(&strlen) s2 else
  let c2 := !s2;
  if c2 = #(0 : Int) then v(&strlen) s1 else
  if c1 = c2 then v(&lev) ((s1 +ₗ #(1 : Int), s2 +ₗ #(1 : Int)))
  else
    let r1 := v(&lev) ((s1, s2 +ₗ #(1 : Int)));
    let r2 := v(&lev) ((s1 +ₗ #(1 : Int), s2));
    let r3 := v(&lev) ((s1 +ₗ #(1 : Int), s2 +ₗ #(1 : Int)));
    #(1 : Int) + v(&min3) r1 r2 r3)

/-- Rocq: `strlen_Strlen`. -/
theorem strlen_Strlen (v : Val) : Exec hl(v(&strlen) v(&v)) (Strlen strlen (v : Exp)) := by
  refine rexec_exec ?_ (by simp [Strlen])
  rexec_rec
  rexec_rec
  rexec_pures

/-- Rocq: `lev_Lev`. -/
theorem lev_Lev (v : Val) : Exec hl(v(&lev) v(&v)) (Lev strlen lev (v : Exp)) := by
  refine rexec_exec ?_ (by simp [Lev])
  rexec_rec
  rexec_rec
  rexec_pures

/-! ## Strings -/

variable {GF : BundledGFunctors} [G : RHeapG GF] [N : NatSourceG GF] [S : SeqG GF]

/-- C-style null terminated strings in the target (Rocq: `string_is`). -/
def stringIs : Loc → List Nat → IProp GF
  | l, [] => iprop(∃ q : Qp, l ↦{.own q} some hl_val(#(0 : Int)))
  | l, n :: s => iprop(⌜n ≠ 0⌝ ∗ (∃ q : Qp, l ↦{.own q} some hl_val(#(n : Int))) ∗
      stringIs (l + (1 : Int)) s)

/-- C-style null terminated strings in the source (Rocq: `src_string_is`). -/
def srcStringIs : Loc → List Nat → IProp GF
  | l, [] => iprop(∃ q : Qp, heapSPointsTo l (.own q) hl_val(#(0 : Int)))
  | l, n :: s => iprop(⌜n ≠ 0⌝ ∗ (∃ q : Qp, heapSPointsTo l (.own q) hl_val(#(n : Int))) ∗
      srcStringIs (l + (1 : Int)) s)

theorem stringIs_cons (l : Loc) (n : Nat) (s : List Nat) :
    stringIs (GF := GF) l (n :: s) = iprop(⌜n ≠ 0⌝ ∗
      (∃ q : Qp, l ↦{.own q} some hl_val(#(n : Int))) ∗ stringIs (l + (1 : Int)) s) := by
  rw [stringIs]

theorem srcStringIs_cons (l : Loc) (n : Nat) (s : List Nat) :
    srcStringIs (GF := GF) l (n :: s) = iprop(⌜n ≠ 0⌝ ∗
      (∃ q : Qp, heapSPointsTo l (.own q) hl_val(#(n : Int))) ∗ srcStringIs (l + (1 : Int)) s) := by
  rw [srcStringIs]

theorem stringIs_nil (l : Loc) :
    stringIs (GF := GF) l [] = iprop(∃ q : Qp, l ↦{.own q} some hl_val(#(0 : Int))) := by
  rw [stringIs]

theorem srcStringIs_nil (l : Loc) :
    srcStringIs (GF := GF) l [] = iprop(∃ q : Qp, heapSPointsTo l (.own q) hl_val(#(0 : Int))) := by
  rw [srcStringIs]

theorem pointsTo_halves (l : Loc) (q : Qp) (v : Val) :
    l ↦{.own q} some v ⊢@{IProp GF} l ↦{.own q.half} some v ∗ l ↦{.own q.half} some v := by
  conv => lhs; rw [← Qp.half_add_half q]
  exact (Fractional.fractional (Φ := fun q : Qp => iprop(l ↦{.own q} some v)) _ _).1

theorem heapSPointsTo_halves (l : Loc) (q : Qp) (v : Val) :
    heapSPointsTo (GF := GF) l (.own q) v ⊢ heapSPointsTo l (.own q.half) v ∗
      heapSPointsTo l (.own q.half) v := by
  unfold heapSPointsTo
  conv => lhs; rw [← Qp.half_add_half q]
  exact (Fractional.fractional (Φ := fun q : Qp =>
    ghost_map_elem G.heapSName (.own q) l (SrcVal.mk (some v))) _ _).1

/-- Rocq: `string_is_dup`. -/
theorem stringIs_dup (l : Loc) (s : List Nat) :
    stringIs (GF := GF) l s ⊢ stringIs l s ∗ stringIs l s := by
  induction s generalizing l with
  | nil =>
    unfold stringIs
    iintro ⟨%q, H⟩
    ihave ⟨H₁, H₂⟩ := pointsTo_halves l q _ $$ H
    isplitl [H₁]
    · iexists q.half; iexact H₁
    · iexists q.half; iexact H₂
  | cons n s ih =>
    unfold stringIs
    iintro ⟨%hn, ⟨%q, H⟩, Htl⟩
    ihave ⟨H₁, H₂⟩ := pointsTo_halves l q _ $$ H
    ihave ⟨T₁, T₂⟩ := ih (l + (1 : Int)) $$ Htl
    isplitl [H₁ T₁]
    · isplitr
      · ipureintro; exact hn
      isplitl [H₁]
      · iexists q.half; iexact H₁
      iexact T₁
    · isplitr
      · ipureintro; exact hn
      isplitl [H₂]
      · iexists q.half; iexact H₂
      iexact T₂

/-- Rocq: `src_string_is_dup`. -/
theorem srcStringIs_dup (l : Loc) (s : List Nat) :
    srcStringIs (GF := GF) l s ⊢ srcStringIs l s ∗ srcStringIs l s := by
  induction s generalizing l with
  | nil =>
    unfold srcStringIs
    iintro ⟨%q, H⟩
    ihave ⟨H₁, H₂⟩ := heapSPointsTo_halves l q _ $$ H
    isplitl [H₁]
    · iexists q.half; iexact H₁
    · iexists q.half; iexact H₂
  | cons n s ih =>
    unfold srcStringIs
    iintro ⟨%hn, ⟨%q, H⟩, Htl⟩
    ihave ⟨H₁, H₂⟩ := heapSPointsTo_halves l q _ $$ H
    ihave ⟨T₁, T₂⟩ := ih (l + (1 : Int)) $$ Htl
    isplitl [H₁ T₁]
    · isplitr
      · ipureintro; exact hn
      isplitl [H₁]
      · iexists q.half; iexact H₁
      iexact T₁
    · isplitr
      · ipureintro; exact hn
      isplitl [H₂]
      · iexists q.half; iexact H₂
      iexact T₂

instance stringIs_timeless (l : Loc) (s : List Nat) : Timeless (stringIs (GF := GF) l s) := by
  induction s generalizing l with
  | nil =>
    unfold stringIs
    exact @UPred.exists_timeless' _ _ _ _ _ _ fun _ => inferInstance
  | cons n s ih =>
    unfold stringIs
    exact @UPred.sep_timeless' _ _ _ _ _ _ inferInstance
      (@UPred.sep_timeless' _ _ _ _ _ _
        (@UPred.exists_timeless' _ _ _ _ _ _ fun _ => inferInstance) (ih _))

instance srcStringIs_timeless (l : Loc) (s : List Nat) :
    Timeless (srcStringIs (GF := GF) l s) := by
  induction s generalizing l with
  | nil =>
    unfold srcStringIs
    exact @UPred.exists_timeless' _ _ _ _ _ _ fun _ => inferInstance
  | cons n s ih =>
    unfold srcStringIs
    exact @UPred.sep_timeless' _ _ _ _ _ _ inferInstance
      (@UPred.sep_timeless' _ _ _ _ _ _
        (@UPred.exists_timeless' _ _ _ _ _ _ fun _ => inferInstance) (ih _))

/-- Rocq: `stringRel_is`. -/
def stringRelIs (v₁ v₂ : Val) (s : List Nat) : IProp GF :=
  iprop(∃ l₁ l₂ : Loc, ⌜v₁ = hl_val(#l₁) ∧ v₂ = hl_val(#l₂)⌝ ∗ stringIs l₁ s ∗ srcStringIs l₂ s)

instance stringRelIs_timeless (v₁ v₂ : Val) (s : List Nat) :
    Timeless (stringRelIs (GF := GF) v₁ v₂ s) := by
  unfold stringRelIs
  refine @UPred.exists_timeless' _ _ _ _ _ _ (fun l₁ => ?_)
  refine @UPred.exists_timeless' _ _ _ _ _ _ (fun l₂ => ?_)
  exact @UPred.sep_timeless' _ _ _ _ _ _ inferInstance
    (@UPred.sep_timeless' _ _ _ _ _ _ inferInstance inferInstance)

/-- Rocq: `strN`. -/
def strN : Namespace := nroot.@"str"

/-- Immutable related strings (Rocq: `imm_stringRel`). -/
def immStringRel (v₁ v₂ : Val) : IProp GF := iprop(∃ s, inv strN (stringRelIs v₁ v₂ s))

instance immStringRel_persistent (v₁ v₂ : Val) : Persistent (immStringRel (GF := GF) v₁ v₂) := by
  unfold immStringRel; infer_instance

/-- Rocq: `pairRel`. -/
def pairRel (Pa Pb : Val → Val → IProp GF) (v₁ v₂ : Val) : IProp GF :=
  iprop(∃ v₁a v₁b v₂a v₂b : Val, ⌜v₁ = hl_val((&v₁a, &v₁b))⌝ ∗ ⌜v₂ = hl_val((&v₂a, &v₂b))⌝ ∗
    Pa v₁a v₂a ∗ Pb v₁b v₂b)

/-- Rocq: `pair_imm_stringRel`. -/
abbrev pairImmStringRel : Val → Val → IProp GF := pairRel immStringRel immStringRel

instance pairImmStringRel_persistent (v₁ v₂ : Val) :
    Persistent (pairImmStringRel (GF := GF) v₁ v₂) := by
  unfold pairImmStringRel pairRel; infer_instance

theorem strN_top : (↑strN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full

/-- Rocq: `stringRel_inv_acc`. -/
theorem stringRel_inv_acc (v₁ v₂ : Val) (s : List Nat) :
    inv strN (stringRelIs (GF := GF) v₁ v₂ s) ⊢ |={⊤}=> stringRelIs v₁ v₂ s := by
  iintro #Hinv
  imod inv_acc_timeless strN_top $$ Hinv with ⟨H, Hclo⟩
  unfold stringRelIs
  icases H with ⟨%l₁, %l₂, %heq, H₁, H₂⟩
  ihave ⟨H₁, H₁'⟩ := stringIs_dup l₁ s $$ H₁
  ihave ⟨H₂, H₂'⟩ := srcStringIs_dup l₂ s $$ H₂
  imod Hclo $$ [H₁' H₂'] with -
  · iexists l₁, l₂
    iframe
    ipureintro; exact heq
  imodintro
  iexists l₁, l₂
  iframe
  ipureintro; exact heq

/-- Rocq: `rwp_strlen`. -/
theorem rwp_strlen (l : Loc) (s : List Nat) :
    stringIs (GF := GF) l s ⊢
      rwpR hl(v(&strlen) #l) fun v => iprop(⌜v = hl_val(#(s.length : Int))⌝) := by
  induction s generalizing l with
  | nil =>
    unfold stringIs
    iintro ⟨%q, H⟩
    twp_rec
    twp_rec
    twp_pures
    twp_apply rwp_load (src := refSrc (GF := GF)) $$ H
    iintro H
    twp_pures
    ipureintro; rfl
  | cons n s ih =>
    unfold stringIs
    iintro ⟨%hn, ⟨%q, H⟩, Htl⟩
    twp_rec
    twp_rec
    twp_pures
    twp_apply rwp_load (src := refSrc (GF := GF)) $$ H
    iintro H
    twp_pures
    rw [decide_eq_false (show ¬ ((n : Nat) : Int) = 0 by omega)]
    twp_pures
    ihave IH := ih (l + (1 : Int)) $$ Htl
    twp_apply rwpR_wand $$ IH
    iintro %v %rfl
    twp_pures
    ipureintro
    simp only [List.length_cons]
    congr 2
    omega

/-- Rocq: `eval_strlen`. -/
theorem eval_strlen (l : Loc) (s : List Nat) :
    srcStringIs (GF := GF) l s ⊢ evalS hl(v(&strlen) #l) hl_val(#(s.length : Int)) := by
  unfold evalS
  induction s generalizing l with
  | nil =>
    unfold srcStringIs
    iintro ⟨%q, Hl⟩ %K H
    src_rec H
    src_rec H
    src_pures H
    src_load H Hl
    src_pures H
    iapply weakSrcUpd_return
    iexact H
  | cons n s ih =>
    unfold srcStringIs
    iintro ⟨%hn, ⟨%q, Hl⟩, Htl⟩ %K H
    src_rec H
    src_rec H
    src_pures H
    src_load H Hl
    src_pures H
    rw [decide_eq_false (show ¬ ((n : Nat) : Int) = 0 by omega)]
    src_pures H
    src_bind (v(&strlen) #(l + (1 : Int))) in H
    iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
    iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
    isplitl [H Htl]
    · iapply ih (l + (1 : Int)) $$ Htl %_ H
    iintro H
    src_pures H
    iapply weakSrcUpd_return
    simp only [List.length_cons]
    rw [show ((s.length + 1 : Nat) : Int) = 1 + (s.length : Int) by omega]
    iexact H

/-- Rocq: `stringRel_is_tl`. -/
theorem stringRel_is_tl (l₁ l₂ : Loc) (n : Nat) (s : List Nat) :
    stringRelIs (GF := GF) hl_val(#l₁) hl_val(#l₂) (n :: s) ⊢
      stringRelIs hl_val(#(l₁ + (1 : Int))) hl_val(#(l₂ + (1 : Int))) s ∗
      (stringRelIs hl_val(#(l₁ + (1 : Int))) hl_val(#(l₂ + (1 : Int))) s -∗
        stringRelIs hl_val(#l₁) hl_val(#l₂) (n :: s)) := by
  unfold stringRelIs
  iintro ⟨%l₁', %l₂', %⟨h₁, h₂⟩, H₁, H₂⟩
  cases h₁
  cases h₂
  rw [stringIs_cons, srcStringIs_cons]
  icases H₁ with ⟨%hn, Hp₁, T₁⟩
  icases H₂ with ⟨-, Hp₂, T₂⟩
  isplitl [T₁ T₂]
  · iexists l₁ + (1 : Int), l₂ + (1 : Int)
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  iintro ⟨%l₁'', %l₂'', %⟨h₁, h₂⟩, T₁, T₂⟩
  simp only [Val.lit.injEq, BaseLit.loc.injEq] at h₁ h₂
  subst h₁ h₂
  iexists l₁, l₂
  rw [stringIs_cons, srcStringIs_cons]
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hp₁ T₁]
  · iframe
    ipureintro; exact hn
  · iframe
    ipureintro; exact hn

/-- Rocq: `inv_stringRel_is_tl`. -/
theorem inv_stringRel_is_tl (N : Namespace) (l₁ l₂ : Loc) (n : Nat) (s : List Nat) :
    inv N (stringRelIs (GF := GF) hl_val(#l₁) hl_val(#l₂) (n :: s)) ⊢
      inv N (stringRelIs hl_val(#(l₁ + (1 : Int))) hl_val(#(l₂ + (1 : Int))) s) := by
  iintro #Hinv
  iapply inv_alter_timeless $$ Hinv
  iintro !> H
  ihave ⟨H₁, H₂⟩ := stringRel_is_tl l₁ l₂ n s $$ H
  iframe H₁
  inext
  iexact H₂

/-- Rocq: `min2_spec`. -/
theorem min2_spec (n₁ n₂ : Nat) :
    ⊢ texan (src := refSrc (GF := GF)) iprop(True) hl(v(&min2) #(n₁ : Int) #(n₂ : Int))
      fun r => iprop(⌜r = hl_val(#((min n₁ n₂ : Nat) : Int))⌝) := by
  unfold texan
  iintro !> %Φ - HΦ
  unfold min2
  twp_pures
  by_cases h : n₁ ≤ n₂
  · rw [decide_eq_true (show ((n₁ : Nat) : Int) ≤ n₂ by omega)]
    twp_pures
    iapply HΦ
    ipureintro
    rw [Nat.min_eq_left h]
  · rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) ≤ n₂ by omega)]
    twp_pures
    iapply HΦ
    ipureintro
    rw [Nat.min_eq_right (by omega)]

/-- Rocq: `min3_spec`. -/
theorem min3_spec (n₁ n₂ n₃ : Nat) :
    ⊢ texan (src := refSrc (GF := GF)) iprop(True)
      hl(v(&min3) #(n₁ : Int) #(n₂ : Int) #(n₃ : Int))
      fun r => iprop(⌜r = hl_val(#((min (min n₁ n₂) n₃ : Nat) : Int))⌝) := by
  unfold texan
  iintro !> %Φ - HΦ
  unfold min3
  twp_pures
  ihave H₁ := min2_spec (GF := GF) n₁ n₂
  unfold texan
  twp_apply H₁
  · itrivial
  iintro %r %rfl
  ihave H₂ := min2_spec (GF := GF) (min n₁ n₂) n₃
  unfold texan
  twp_apply H₂
  · itrivial
  iintro %r %rfl
  iapply HΦ
  ipureintro; rfl

/-- Rocq: `eval_min2`. -/
theorem eval_min2 (n₁ n₂ : Nat) :
    ⊢ evalS (GF := GF) hl(v(&min2) #(n₁ : Int) #(n₂ : Int)) hl_val(#((min n₁ n₂ : Nat) : Int)) := by
  unfold evalS
  iintro %K H
  src_rec H
  src_pures H
  by_cases h : n₁ ≤ n₂
  · rw [decide_eq_true (show ((n₁ : Nat) : Int) ≤ n₂ by omega)]
    src_pures H
    iapply weakSrcUpd_return
    rw [Nat.min_eq_left h]
    iexact H
  · rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) ≤ n₂ by omega)]
    src_pures H
    iapply weakSrcUpd_return
    rw [Nat.min_eq_right (by omega)]
    iexact H

/-- Rocq: `eval_min3`. -/
theorem eval_min3 (n₁ n₂ n₃ : Nat) :
    ⊢ evalS (GF := GF) hl(v(&min3) #(n₁ : Int) #(n₂ : Int) #(n₃ : Int))
      hl_val(#((min (min n₁ n₂) n₃ : Nat) : Int)) := by
  unfold evalS
  iintro %K H
  src_rec H
  src_pures H
  src_bind (v(&min2) #((n₁ : Nat) : Int) #((n₂ : Nat) : Int)) in H
  iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
  iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
  isplitl [H]
  · ihave He := eval_min2 (GF := GF) n₁ n₂
    unfold evalS
    iapply He $$ %_ H
  iintro H
  src_bind (v(&min2) #((min n₁ n₂ : Nat) : Int) #((n₃ : Nat) : Int)) in H
  ihave He := eval_min2 (GF := GF) (min n₁ n₂) n₃
  unfold evalS
  iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
  ihave He' := He $$ %_ H
  simp only [List.nil_append]
  iexact He'

/-- Rocq: `string_is_functional`. -/
theorem string_is_functional (l : Loc) (s s' : List Nat) :
    ⊢ stringIs (GF := GF) l s -∗ stringIs l s' -∗ ⌜s = s'⌝ := by
  induction s generalizing l s' with
  | nil =>
    cases s' with
    | nil => iintro - -; ipureintro; rfl
    | cons n' s' =>
      unfold stringIs
      iintro ⟨%q, H⟩ ⟨%hn, ⟨%q', H'⟩, -⟩
      icases pointsTo_agree $$ [H H'] with %h
      · iframe
      simp at h
      omega
  | cons n s ih =>
    cases s' with
    | nil =>
      unfold stringIs
      iintro ⟨%hn, ⟨%q, H⟩, -⟩ ⟨%q', H'⟩
      icases pointsTo_agree $$ [H H'] with %h
      · iframe
      simp at h
      omega
    | cons n' s' =>
      unfold stringIs
      iintro ⟨%hn, ⟨%q, H⟩, T⟩ ⟨%hn', ⟨%q', H'⟩, T'⟩
      icases pointsTo_agree $$ [H H'] with %h
      · iframe
      icases ih (l + (1 : Int)) s' $$ T T' with %h'
      ipureintro
      simp only [Option.some.injEq, Val.lit.injEq, BaseLit.int.injEq] at h
      subst h'
      congr 1
      omega

/-- Rocq: `stringRel_is_functional`. -/
theorem stringRel_is_functional (va vb vb' : Val) (s s' : List Nat) :
    ⊢ stringRelIs (GF := GF) va vb s -∗ stringRelIs va vb' s' -∗ ⌜s = s'⌝ := by
  unfold stringRelIs
  iintro ⟨%l₁, %l₂, %⟨rfl, rfl⟩, H₁, -⟩ ⟨%l₁', %l₂', %⟨h, -⟩, H₁', -⟩
  simp only [Val.lit.injEq, BaseLit.loc.injEq] at h
  subst h
  iapply string_is_functional $$ H₁ H₁'

/-! ## Fundamental properties -/

theorem stringRelIs_elim (v₁ v₂ : Val) (s : List Nat) :
    stringRelIs (GF := GF) v₁ v₂ s ⊢ ∃ l₁ l₂ : Loc, ⌜v₁ = hl_val(#l₁) ∧ v₂ = hl_val(#l₂)⌝ ∗
      stringIs l₁ s ∗ srcStringIs l₂ s := by
  unfold stringRelIs; exact .rfl

theorem immStringRel_intro (v₁ v₂ : Val) :
    (∃ s, inv strN (stringRelIs v₁ v₂ s)) ⊢ immStringRel (GF := GF) v₁ v₂ := by
  unfold immStringRel; exact .rfl

theorem immStringRel_elim (v₁ v₂ : Val) :
    immStringRel (GF := GF) v₁ v₂ ⊢ ∃ s, inv strN (stringRelIs v₁ v₂ s) := by
  unfold immStringRel; exact .rfl

/-- Rocq: `strlen_fundamental_core`. -/
theorem strlen_fundamental_core (slen : Val) (c : Nat) (K : List ECtxItem) (va vb : Val) :
    ▷ tfImplements (GF := GF) immStringRel natRel slen strlen ∗ immStringRel va vb ∗
      src (fill K hl(v(&strlen) v(&vb))) ⊢
      rseq ⊤ (Strlen slen (va : Exp)) fun v => iprop(∃ m : Nat, ⌜v = hl_val(#(m : Int))⌝ ∗
        stutter c ∗ src (fill K hl(#(m : Int))) ∗
        □ (∀ vb', immStringRel va vb' -∗ evalS hl(v(&strlen) v(&vb')) hl_val(#(m : Int)))) := by
  unfold rseq seq
  iintro ⟨#IH, #HPre, Hsrc⟩ Hna
  icases immStringRel_elim va vb $$ HPre with ⟨%s, #Hinv⟩
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop((∃ _ : Unit, src (fill K (Strlen strlen (vb : Exp))) ∗ emp) ∗ stutter c)) rfl
    $$ [Hna] [Hsrc]
  · iintro ⟨⟨%_, Hsrc, -⟩, Hc⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply fupd_rswp (src := refSrc (GF := GF))
    imod stringRel_inv_acc va vb s $$ Hinv with Hstr
    imodintro
    icases stringRelIs_elim va vb s $$ Hstr with ⟨%l₁, %l₂, %⟨rfl, rfl⟩, H₁, H₂⟩
    cases s with
    | nil =>
      rw [stringIs_nil, srcStringIs_nil]
      icases H₁ with ⟨%q₁, H₁⟩
      icases H₂ with ⟨%q₂, H₂⟩
      unfold Strlen
      twp_apply rswp_load (src := refSrc (GF := GF)) $$ H₁
      iintro H₁
      src_load Hsrc H₂
      src_pures Hsrc
      twp_pures
      iframe Hna
      iexists 0
      isplitr
      · ipureintro; rfl
      isplitl [Hc]
      · iexact Hc
      isplitl [Hsrc]
      · iexact Hsrc
      iintro !> %vb' #HPre'
      icases immStringRel_elim _ _ $$ HPre' with ⟨%s', #Hinv'⟩
      unfold evalS
      iintro %K' H
      iapply fupd_srcUpdate (src := refSrc (GF := GF))
      imod stringRel_inv_acc _ _ _ $$ Hinv with Hstr
      imod stringRel_inv_acc _ _ _ $$ Hinv' with Hstr'
      icases stringRel_is_functional _ _ _ _ _ $$ Hstr' Hstr with %rfl
      imodintro
      icases stringRelIs_elim _ _ _ $$ Hstr' with ⟨%l₁', %l₂', %⟨-, rfl⟩, -, H₂'⟩
      rw [srcStringIs_nil]
      icases H₂' with ⟨%q, H₂'⟩
      src_rec H
      src_rec H
      src_pures H
      src_load H H₂'
      src_pures H
      iapply weakSrcUpd_return
      iexact H
    | cons n s =>
      rw [stringIs_cons, srcStringIs_cons]
      icases H₁ with ⟨%hn, ⟨%q₁, H₁⟩, -⟩
      icases H₂ with ⟨-, ⟨%q₂, H₂⟩, -⟩
      unfold Strlen
      twp_apply rswp_load (src := refSrc (GF := GF)) $$ H₁
      iintro H₁
      src_load Hsrc H₂
      src_pures Hsrc
      twp_pures
      rw [decide_eq_false (show ¬ ((n : Nat) : Int) = 0 by omega)]
      twp_pures
      src_pures Hsrc
      src_bind (v(&strlen) #(l₂ + (1 : Int))) in Hsrc
      twp_bind (v(&slen) #(l₁ + (1 : Int)))
      unfold tfImplements rseq seq
      ihave H := IH $$ %(hl_val(#(l₁ + (1 : Int)))) %(hl_val(#(l₂ + (1 : Int)))) %0 %_ [] Hsrc Hna
      · iapply immStringRel_intro
        iexists s
        iapply inv_stringRel_is_tl $$ Hinv
      twp_apply rwpR_wand $$ H
      iintro %v ⟨Hna, %v', Hrel, -, Hsrc, #Hev⟩
      unfold natRel
      icases Hrel with ⟨%m, %⟨rfl, rfl⟩⟩
      src_pures Hsrc
      twp_pures
      rw [show (1 + (m : Int)) = ((m + 1 : Nat) : Int) by omega]
      iframe Hna
      iexists m + 1
      isplitr
      · ipureintro; rfl
      isplitl [Hc]
      · iexact Hc
      isplitl [Hsrc]
      · iexact Hsrc
      iintro !> %vb' #HPre'
      icases immStringRel_elim _ _ $$ HPre' with ⟨%s', #Hinv'⟩
      unfold evalS
      iintro %K' H
      iapply fupd_srcUpdate (src := refSrc (GF := GF))
      imod stringRel_inv_acc _ _ _ $$ Hinv with Hstr
      imod stringRel_inv_acc _ _ _ $$ Hinv' with Hstr'
      icases stringRel_is_functional _ _ _ _ _ $$ Hstr' Hstr with %rfl
      imodintro
      icases stringRelIs_elim _ _ _ $$ Hstr' with ⟨%l₁', %l₂', %⟨-, rfl⟩, -, H₂'⟩
      ihave ⟨%w, #He, Hrel⟩ := Hev $$ %(hl_val(#(l₂' + (1 : Int)))) []
      · iapply immStringRel_intro
        iexists s
        iapply inv_stringRel_is_tl $$ Hinv'
      icases Hrel with ⟨%m', %⟨hm, rfl⟩⟩
      rw [srcStringIs_cons]
      icases H₂' with ⟨-, ⟨%q, H₂'⟩, -⟩
      src_rec H
      src_rec H
      src_pures H
      src_load H H₂'
      src_pures H
      rw [decide_eq_false (show ¬ ((n : Nat) : Int) = 0 by omega)]
      src_pures H
      src_bind (v(&strlen) #(l₂' + (1 : Int))) in H
      iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
      iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
      isplitl [H]
      · iapply He $$ %_ H
      iintro H
      src_pures H
      iapply weakSrcUpd_return
      have : m' = m := by simp only [Val.lit.injEq, BaseLit.int.injEq] at hm; omega
      subst this
      rw [show (1 + (m' : Int)) = ((m' + 1 : Nat) : Int) by omega]
      iexact H
  · ihave H := step_inv_alloc c ⊤ 0 (fill K hl(v(&strlen) v(&vb)))
      (fun _ : Unit => fill K (Strlen strlen (vb : Exp))) (fun _ => iprop(emp))
      (fun _ => Derived.fill_ne (by simp [Strlen])) $$ []
    · iintro Hsrc
      ihave H := exec_src_update 0 ⊤ (exec_frame K (strlen_Strlen vb)) $$ Hsrc
      iapply srcUpdate_mono (src := refSrc (GF := GF))
      isplitl [H]
      · iexact H
      iintro Hsrc
      iexists ()
      iframe
    iapply H $$ Hsrc

theorem natRel_elim (v₁ v₂ : Val) :
    natRel (GF := GF) v₁ v₂ ⊢ ∃ n : Nat, ⌜v₁ = hl_val(#(n : Int)) ∧ v₂ = hl_val(#(n : Int))⌝ := by
  unfold natRel; exact .rfl

theorem pairImm_intro (x₁ x₂ y₁ y₂ : Val) (s₁ s₂ : List Nat) :
    inv strN (stringRelIs (GF := GF) x₁ y₁ s₁) ∗ inv strN (stringRelIs x₂ y₂ s₂) ⊢
      pairImmStringRel hl_val((&x₁, &x₂)) hl_val((&y₁, &y₂)) := by
  iintro ⟨#H₁, #H₂⟩
  unfold pairImmStringRel pairRel
  iexists x₁, x₂, y₁, y₂
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  isplit
  · iapply immStringRel_intro
    iexists s₁
    iexact H₁
  · iapply immStringRel_intro
    iexists s₂
    iexact H₂

theorem pairImm_elim (va vb : Val) :
    pairImmStringRel (GF := GF) va vb ⊢ ∃ x₁ x₂ y₁ y₂ : Val, ∃ s₁ s₂ : List Nat,
      ⌜va = hl_val((&x₁, &x₂)) ∧ vb = hl_val((&y₁, &y₂))⌝ ∗
      inv strN (stringRelIs x₁ y₁ s₁) ∗ inv strN (stringRelIs x₂ y₂ s₂) := by
  unfold pairImmStringRel pairRel
  iintro ⟨%x₁, %x₂, %y₁, %y₂, %h₁, %h₂, H₁, H₂⟩
  icases immStringRel_elim _ _ $$ H₁ with ⟨%s₁, #H₁⟩
  icases immStringRel_elim _ _ $$ H₂ with ⟨%s₂, #H₂⟩
  iexists x₁, x₂, y₁, y₂, s₁, s₂
  isplitr
  · ipureintro; exact ⟨h₁, h₂⟩
  isplit
  · iexact H₁
  · iexact H₂

/-- Reopen the invariants of the strings for a new source pair. -/
theorem pair_src_acc (x₁ y₁ x₂ y₂ : Loc) (s₁ s₂ : List Nat) (vb' : Val) :
    inv strN (stringRelIs (GF := GF) hl_val(#x₁) hl_val(#y₁) s₁) ∗
      inv strN (stringRelIs hl_val(#x₂) hl_val(#y₂) s₂) ∗
      pairImmStringRel hl_val((#x₁, #x₂)) vb' ⊢
      |={⊤}=> ∃ y₁' y₂' : Loc, ⌜vb' = hl_val((#y₁', #y₂'))⌝ ∗
        srcStringIs y₁' s₁ ∗ srcStringIs y₂' s₂ ∗
        inv strN (stringRelIs hl_val(#x₁) hl_val(#y₁') s₁) ∗
        inv strN (stringRelIs hl_val(#x₂) hl_val(#y₂') s₂) := by
  iintro ⟨#H₁, #H₂, HP⟩
  icases pairImm_elim _ _ $$ HP with ⟨%x₁', %x₂', %y₁', %y₂', %s₁', %s₂', %⟨hva, rfl⟩, #H₁', #H₂'⟩
  cases hva
  imod stringRel_inv_acc _ _ _ $$ H₁ with S₁
  imod stringRel_inv_acc _ _ _ $$ H₁' with S₁'
  icases stringRel_is_functional _ _ _ _ _ $$ S₁' S₁ with %rfl
  imod stringRel_inv_acc _ _ _ $$ H₂ with S₂
  imod stringRel_inv_acc _ _ _ $$ H₂' with S₂'
  icases stringRel_is_functional _ _ _ _ _ $$ S₂' S₂ with %rfl
  icases stringRelIs_elim _ _ _ $$ S₁' with ⟨%l₁, %b₁, %⟨-, rfl⟩, -, T₁⟩
  icases stringRelIs_elim _ _ _ $$ S₂' with ⟨%l₂, %b₂, %⟨-, rfl⟩, -, T₂⟩
  imodintro
  iexists b₁, b₂
  isplitr
  · ipureintro; rfl
  iframe T₁ T₂
  isplit
  · iexact H₁'
  · iexact H₂'

theorem evalS_intro (e : Exp) (v : Val) :
    (∀ K : List ECtxItem, src (fill K e) -∗ srcUpd ⊤ (src (fill K (v : Exp)))) ⊢ evalS (GF := GF) e v := by
  unfold evalS; exact .rfl

theorem evalS_elim (e : Exp) (v : Val) :
    evalS (GF := GF) e v ⊢ ∀ K : List ECtxItem, src (fill K e) -∗ srcUpd ⊤ (src (fill K (v : Exp))) := by
  unfold evalS; exact .rfl

theorem eval_natRel (e : Exp) (m : Nat) :
    (∃ v', □ evalS (GF := GF) e v' ∗ natRel hl_val(#(m : Int)) v') ⊢ evalS e hl_val(#(m : Int)) := by
  iintro ⟨%v', #He, Hr⟩
  icases natRel_elim _ _ $$ Hr with ⟨%k, %⟨hk, rfl⟩⟩
  have : k = m := by simp only [Val.lit.injEq, BaseLit.int.injEq] at hk; omega
  subst this
  iexact He

/-- Rocq: `lev_fundamental_core`. -/
theorem lev_fundamental_core (g slen : Val) (c : Nat) (K : List ECtxItem) (va vb : Val) :
    ▷ tfImplements (GF := GF) immStringRel natRel slen strlen ∗
      ▷ tfImplements pairImmStringRel natRel g lev ∗ pairImmStringRel va vb ∗
      src (fill K hl(v(&lev) v(&vb))) ⊢
      rseq ⊤ (Lev slen g (va : Exp)) fun v => iprop(∃ m : Nat, ⌜v = hl_val(#(m : Int))⌝ ∗
        stutter c ∗ src (fill K hl(#(m : Int))) ∗
        □ (∀ vb', pairImmStringRel va vb' -∗ evalS hl(v(&lev) v(&vb')) hl_val(#(m : Int)))) := by
  unfold rseq seq
  iintro ⟨#Hstrlen, #IH, #HPre, Hsrc⟩ Hna
  icases pairImm_elim _ _ $$ HPre with ⟨%x₁, %x₂, %y₁, %y₂, %s₁, %s₂, %⟨rfl, rfl⟩, #Hinv1, #Hinv2⟩
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop((∃ _ : Unit, src (fill K (Lev strlen lev hl_val((&y₁, &y₂)))) ∗ emp) ∗ stutter c))
    rfl $$ [Hna] [Hsrc]
  · iintro ⟨⟨%_, Hsrc, -⟩, Hc⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply fupd_rswp (src := refSrc (GF := GF))
    imod stringRel_inv_acc _ _ _ $$ Hinv1 with S₁
    imod stringRel_inv_acc _ _ _ $$ Hinv2 with S₂
    imodintro
    icases stringRelIs_elim _ _ _ $$ S₁ with ⟨%a₁, %b₁, %⟨rfl, rfl⟩, A₁, B₁⟩
    icases stringRelIs_elim _ _ _ $$ S₂ with ⟨%a₂, %b₂, %⟨rfl, rfl⟩, A₂, B₂⟩
    unfold Lev
    twp_pures
    src_pures Hsrc
    cases s₁ with
    | nil =>
      rw [stringIs_nil, srcStringIs_nil]
      icases A₁ with ⟨%q₁, A₁⟩
      icases B₁ with ⟨%q₁', B₁⟩
      src_load Hsrc B₁
      src_pures Hsrc
      twp_apply rwp_load (src := refSrc (GF := GF)) $$ A₁
      iintro A₁
      twp_pures
      unfold tfImplements rseq seq
      ihave H := Hstrlen $$ %(hl_val(#a₂)) %(hl_val(#b₂)) %0 %_ [] Hsrc Hna
      · iapply immStringRel_intro
        iexists s₂
        iexact Hinv2
      iapply rwpR_wand $$ H
      iintro %v ⟨Hna, %v', Hrel, -, Hsrc, #Hev⟩
      icases natRel_elim _ _ $$ Hrel with ⟨%m, %⟨rfl, rfl⟩⟩
      iframe Hna
      iexists m
      isplitr
      · ipureintro; rfl
      isplitl [Hc]
      · iexact Hc
      isplitl [Hsrc]
      · iexact Hsrc
      iintro !> %vb' #HPre'
      iapply evalS_intro
      iintro %K' H
      iapply fupd_srcUpdate (src := refSrc (GF := GF))
      imod pair_src_acc a₁ b₁ a₂ b₂ [] s₂ vb' $$ [Hinv1 Hinv2 HPre'] with ⟨%b₁', %b₂', %rfl, B₁', -, #Hinv1', #Hinv2'⟩
      · isplit
        · iexact Hinv1
        isplit
        · iexact Hinv2
        · iexact HPre'
      imodintro
      rw [srcStringIs_nil]
      icases B₁' with ⟨%q, B₁'⟩
      src_rec H
      src_rec H
      src_pures H
      src_load H B₁'
      src_pures H
      ihave He0 := Hev $$ %(hl_val(#b₂')) []
      · iapply immStringRel_intro
        iexists s₂
        iexact Hinv2'
      ihave He := eval_natRel _ m $$ He0
      ihave He := evalS_elim _ _ $$ He
      iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
      iapply He $$ %_ H
    | cons n₁ s₁ =>
      rw [stringIs_cons, srcStringIs_cons]
      icases A₁ with ⟨%hn₁, ⟨%q₁, A₁⟩, -⟩
      icases B₁ with ⟨-, ⟨%q₁', B₁⟩, -⟩
      src_load Hsrc B₁
      src_pures Hsrc
      twp_apply rwp_load (src := refSrc (GF := GF)) $$ A₁
      iintro A₁
      twp_pures
      rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) = 0 by omega)]
      twp_pures
      src_pures Hsrc
      cases s₂ with
      | nil =>
        rw [stringIs_nil, srcStringIs_nil]
        icases A₂ with ⟨%q₂, A₂⟩
        icases B₂ with ⟨%q₂', B₂⟩
        src_load Hsrc B₂
        src_pures Hsrc
        twp_apply rwp_load (src := refSrc (GF := GF)) $$ A₂
        iintro A₂
        twp_pures
        unfold tfImplements rseq seq
        ihave H := Hstrlen $$ %(hl_val(#a₁)) %(hl_val(#b₁)) %0 %_ [] Hsrc Hna
        · iapply immStringRel_intro
          iexists n₁ :: s₁
          iexact Hinv1
        iapply rwpR_wand $$ H
        iintro %v ⟨Hna, %v', Hrel, -, Hsrc, #Hev⟩
        icases natRel_elim _ _ $$ Hrel with ⟨%m, %⟨rfl, rfl⟩⟩
        iframe Hna
        iexists m
        isplitr
        · ipureintro; rfl
        isplitl [Hc]
        · iexact Hc
        isplitl [Hsrc]
        · iexact Hsrc
        iintro !> %vb' #HPre'
        iapply evalS_intro
        iintro %K' H
        iapply fupd_srcUpdate (src := refSrc (GF := GF))
        imod pair_src_acc a₁ b₁ a₂ b₂ (n₁ :: s₁) [] vb' $$ [Hinv1 Hinv2 HPre'] with
          ⟨%b₁', %b₂', %rfl, B₁', B₂', #Hinv1', #Hinv2'⟩
        · isplit
          · iexact Hinv1
          isplit
          · iexact Hinv2
          · iexact HPre'
        imodintro
        rw [srcStringIs_cons, srcStringIs_nil]
        icases B₁' with ⟨-, ⟨%q, B₁'⟩, -⟩
        icases B₂' with ⟨%q', B₂'⟩
        src_rec H
        src_rec H
        src_pures H
        src_load H B₁'
        src_pures H
        rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) = 0 by omega)]
        src_pures H
        src_load H B₂'
        src_pures H
        ihave He0 := Hev $$ %(hl_val(#b₁')) []
        · iapply immStringRel_intro
          iexists n₁ :: s₁
          iexact Hinv1'
        ihave He := eval_natRel _ m $$ He0
        ihave He := evalS_elim _ _ $$ He
        iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
        iapply He $$ %_ H
      | cons n₂ s₂ =>
        rw [stringIs_cons, srcStringIs_cons]
        icases A₂ with ⟨%hn₂, ⟨%q₂, A₂⟩, -⟩
        icases B₂ with ⟨-, ⟨%q₂', B₂⟩, -⟩
        src_load Hsrc B₂
        src_pures Hsrc
        twp_apply rwp_load (src := refSrc (GF := GF)) $$ A₂
        iintro A₂
        twp_pures
        rw [decide_eq_false (show ¬ ((n₂ : Nat) : Int) = 0 by omega)]
        twp_pures
        src_pures Hsrc
        by_cases h : n₁ = n₂
        · subst h
          rw [decide_eq_true (show ((n₁ : Nat) : Int) = n₁ from rfl)]
          twp_pures
          src_pures Hsrc
          unfold tfImplements rseq seq
          ihave H := IH $$ %(hl_val((#(a₁ + (1 : Int)), #(a₂ + (1 : Int))))) %(hl_val((#(b₁ + (1 : Int)), #(b₂ + (1 : Int))))) %0 %_ [] Hsrc Hna
          · iapply pairImm_intro (s₁ := s₁) (s₂ := s₂)
            isplit
            · iapply inv_stringRel_is_tl $$ Hinv1
            · iapply inv_stringRel_is_tl $$ Hinv2
          iapply rwpR_wand $$ H
          iintro %v ⟨Hna, %v', Hrel, -, Hsrc, #Hev⟩
          icases natRel_elim _ _ $$ Hrel with ⟨%m, %⟨rfl, rfl⟩⟩
          iframe Hna
          iexists m
          isplitr
          · ipureintro; rfl
          isplitl [Hc]
          · iexact Hc
          isplitl [Hsrc]
          · iexact Hsrc
          iintro !> %vb' #HPre'
          iapply evalS_intro
          iintro %K' H
          iapply fupd_srcUpdate (src := refSrc (GF := GF))
          imod pair_src_acc a₁ b₁ a₂ b₂ (n₁ :: s₁) (n₁ :: s₂) vb' $$ [Hinv1 Hinv2 HPre'] with
            ⟨%b₁', %b₂', %rfl, B₁', B₂', #Hinv1', #Hinv2'⟩
          · isplit
            · iexact Hinv1
            isplit
            · iexact Hinv2
            · iexact HPre'
          imodintro
          rw [srcStringIs_cons, srcStringIs_cons]
          icases B₁' with ⟨-, ⟨%q, B₁'⟩, -⟩
          icases B₂' with ⟨-, ⟨%q', B₂'⟩, -⟩
          src_rec H
          src_rec H
          src_pures H
          src_load H B₁'
          src_pures H
          rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) = 0 by omega)]
          src_pures H
          src_load H B₂'
          src_pures H
          rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) = 0 by omega)]
          src_pures H
          ihave He0 := Hev $$ %(hl_val((#(b₁' + (1 : Int)), #(b₂' + (1 : Int))))) []
          · iapply pairImm_intro (s₁ := s₁) (s₂ := s₂)
            isplit
            · iapply inv_stringRel_is_tl $$ Hinv1'
            · iapply inv_stringRel_is_tl $$ Hinv2'
          ihave He := eval_natRel _ m $$ He0
          ihave He := evalS_elim _ _ $$ He
          iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
          iapply He $$ %_ H
        · rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) = n₂ by omega)]
          twp_pures
          src_pures Hsrc
          unfold tfImplements rseq seq
          src_bind (v(&lev) v(&(hl_val((#b₁, #(b₂ + (1 : Int))))))) in Hsrc
          twp_bind (v(&g) v(&(hl_val((#a₁, #(a₂ + (1 : Int)))))))
          ihave H := IH $$ %(hl_val((#a₁, #(a₂ + (1 : Int))))) %(hl_val((#b₁, #(b₂ + (1 : Int))))) %0 %_ [] Hsrc Hna
          · iapply pairImm_intro (s₁ := n₁ :: s₁) (s₂ := s₂)
            isplit
            · iexact Hinv1
            · iapply inv_stringRel_is_tl $$ Hinv2
          twp_apply rwpR_wand $$ H
          iintro %v ⟨Hna, %v', Hrel, -, Hsrc, #Hev1⟩
          icases natRel_elim _ _ $$ Hrel with ⟨%m₁, %⟨rfl, rfl⟩⟩
          twp_pures
          src_pures Hsrc

          src_bind (v(&lev) v(&(hl_val((#(b₁ + (1 : Int)), #b₂))))) in Hsrc
          twp_bind (v(&g) v(&(hl_val((#(a₁ + (1 : Int)), #a₂)))))
          ihave H := IH $$ %(hl_val((#(a₁ + (1 : Int)), #a₂))) %(hl_val((#(b₁ + (1 : Int)), #b₂))) %0 %_ [] Hsrc Hna
          · iapply pairImm_intro (s₁ := s₁) (s₂ := n₂ :: s₂)
            isplit
            · iapply inv_stringRel_is_tl $$ Hinv1
            · iexact Hinv2
          twp_apply rwpR_wand $$ H
          iintro %v ⟨Hna, %v', Hrel, -, Hsrc, #Hev2⟩
          icases natRel_elim _ _ $$ Hrel with ⟨%m₂, %⟨rfl, rfl⟩⟩
          twp_pures
          src_pures Hsrc

          src_bind (v(&lev) v(&(hl_val((#(b₁ + (1 : Int)), #(b₂ + (1 : Int))))))) in Hsrc
          twp_bind (v(&g) v(&(hl_val((#(a₁ + (1 : Int)), #(a₂ + (1 : Int)))))))
          ihave H := IH $$ %(hl_val((#(a₁ + (1 : Int)), #(a₂ + (1 : Int))))) %(hl_val((#(b₁ + (1 : Int)), #(b₂ + (1 : Int))))) %0 %_ [] Hsrc Hna
          · iapply pairImm_intro (s₁ := s₁) (s₂ := s₂)
            isplit
            · iapply inv_stringRel_is_tl $$ Hinv1
            · iapply inv_stringRel_is_tl $$ Hinv2
          twp_apply rwpR_wand $$ H
          iintro %v ⟨Hna, %v', Hrel, -, Hsrc, #Hev3⟩
          icases natRel_elim _ _ $$ Hrel with ⟨%m₃, %⟨rfl, rfl⟩⟩
          twp_pures
          src_pures Hsrc
          src_bind (v(&min3) #((m₁ : Nat) : Int) #((m₂ : Nat) : Int) #((m₃ : Nat) : Int)) in Hsrc
          ihave Hm := eval_min3 (GF := GF) m₁ m₂ m₃
          ihave Hm := evalS_elim _ _ $$ Hm
          ihave Hs := Hm $$ %_ Hsrc
          iapply rwp_weaken_src rfl
          iapply srcUpdate_mono (src := refSrc (GF := GF))
          isplitl [Hs]
          · iexact Hs
          iintro Hsrc
          src_pures Hsrc
          twp_bind (v(&min3) #((m₁ : Nat) : Int) #((m₂ : Nat) : Int) #((m₃ : Nat) : Int))
          ihave M := min3_spec (GF := GF) m₁ m₂ m₃
          unfold texan
          twp_apply M
          · itrivial
          iintro %r %rfl
          twp_pures
          rw [show (1 + ((min (min m₁ m₂) m₃ : Nat) : Int)) = ((min (min m₁ m₂) m₃ + 1 : Nat) : Int) by omega]
          iframe Hna
          iexists min (min m₁ m₂) m₃ + 1
          isplitr
          · ipureintro; rfl
          isplitl [Hc]
          · iexact Hc
          isplitl [Hsrc]
          · iexact Hsrc
          iintro !> %vb' #HPre'
          iapply evalS_intro
          iintro %K' H
          iapply fupd_srcUpdate (src := refSrc (GF := GF))
          imod pair_src_acc a₁ b₁ a₂ b₂ (n₁ :: s₁) (n₂ :: s₂) vb' $$ [Hinv1 Hinv2 HPre'] with
            ⟨%b₁', %b₂', %rfl, B₁', B₂', #Hinv1', #Hinv2'⟩
          · isplit
            · iexact Hinv1
            isplit
            · iexact Hinv2
            · iexact HPre'
          imodintro
          rw [srcStringIs_cons, srcStringIs_cons]
          icases B₁' with ⟨-, ⟨%q, B₁'⟩, -⟩
          icases B₂' with ⟨-, ⟨%q', B₂'⟩, -⟩
          src_rec H
          src_rec H
          src_pures H
          src_load H B₁'
          src_pures H
          rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) = 0 by omega)]
          src_pures H
          src_load H B₂'
          src_pures H
          rw [decide_eq_false (show ¬ ((n₂ : Nat) : Int) = 0 by omega)]
          src_pures H
          rw [decide_eq_false (show ¬ ((n₁ : Nat) : Int) = n₂ by omega)]
          src_pures H
          src_bind (v(&lev) v(&(hl_val((#b₁', #(b₂' + (1 : Int))))))) in H
          ihave He0 := Hev1 $$ %(hl_val((#b₁', #(b₂' + (1 : Int))))) []
          · iapply pairImm_intro (s₁ := n₁ :: s₁) (s₂ := s₂)
            isplit
            · iexact Hinv1'
            · iapply inv_stringRel_is_tl $$ Hinv2'
          ihave He := eval_natRel _ m₁ $$ He0
          ihave He := evalS_elim _ _ $$ He
          iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
          iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
          isplitl [H He]
          · iapply He $$ %_ H
          iintro H
          src_pures H

          src_bind (v(&lev) v(&(hl_val((#(b₁' + (1 : Int)), #b₂'))))) in H
          ihave He0 := Hev2 $$ %(hl_val((#(b₁' + (1 : Int)), #b₂'))) []
          · iapply pairImm_intro (s₁ := s₁) (s₂ := n₂ :: s₂)
            isplit
            · iapply inv_stringRel_is_tl $$ Hinv1'
            · iexact Hinv2'
          ihave He := eval_natRel _ m₂ $$ He0
          ihave He := evalS_elim _ _ $$ He
          iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
          iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
          isplitl [H He]
          · iapply He $$ %_ H
          iintro H
          src_pures H

          src_bind (v(&lev) v(&(hl_val((#(b₁' + (1 : Int)), #(b₂' + (1 : Int))))))) in H
          ihave He0 := Hev3 $$ %(hl_val((#(b₁' + (1 : Int)), #(b₂' + (1 : Int))))) []
          · iapply pairImm_intro (s₁ := s₁) (s₂ := s₂)
            isplit
            · iapply inv_stringRel_is_tl $$ Hinv1'
            · iapply inv_stringRel_is_tl $$ Hinv2'
          ihave He := eval_natRel _ m₃ $$ He0
          ihave He := evalS_elim _ _ $$ He
          iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
          iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
          isplitl [H He]
          · iapply He $$ %_ H
          iintro H
          src_pures H
          src_bind (v(&min3) #((m₁ : Nat) : Int) #((m₂ : Nat) : Int) #((m₃ : Nat) : Int)) in H
          ihave Hm := eval_min3 (GF := GF) m₁ m₂ m₃
          ihave Hm := evalS_elim _ _ $$ Hm
          iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
          iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
          isplitl [H Hm]
          · iapply Hm $$ %_ H
          iintro H
          src_pures H
          iapply weakSrcUpd_return
          rw [show (1 + ((min (min m₁ m₂) m₃ : Nat) : Int)) = ((min (min m₁ m₂) m₃ + 1 : Nat) : Int) by omega]
          iexact H
  · ihave H := step_inv_alloc c ⊤ 0 (fill K hl(v(&lev) v(&(hl_val((&y₁, &y₂))))))
      (fun _ : Unit => fill K (Lev strlen lev hl_val((&y₁, &y₂)))) (fun _ => iprop(emp))
      (fun _ => Derived.fill_ne (by simp [Lev])) $$ []
    · iintro Hsrc
      ihave H := exec_src_update 0 ⊤ (exec_frame K (lev_Lev hl_val((&y₁, &y₂)))) $$ Hsrc
      iapply srcUpdate_mono (src := refSrc (GF := GF))
      isplitl [H]
      · iexact H
      iintro Hsrc
      iexists ()
      iframe
    iapply H $$ Hsrc

/-! ## Soundness -/

/-- The postcondition of the fundamental lemmas implies the one of `tfImplements`. -/
theorem tf_post (P : Val → Val → IProp GF) [∀ a b, Persistent (P a b)] (f va : Val) (c : Nat)
    (K : List ECtxItem) (w : Val) :
    (∃ m : Nat, ⌜w = hl_val(#(m : Int))⌝ ∗ stutter c ∗ src (fill K hl(#(m : Int))) ∗
      □ (∀ vb', P va vb' -∗ evalS hl(v(&f) v(&vb')) hl_val(#(m : Int)))) ⊢
      ∃ v' : Val, natRel w v' ∗ stutter c ∗ src (fill K (v' : Exp)) ∗
        □ (∀ x', P va x' -∗ ∃ v', □ evalS hl(v(&f) v(&x')) v' ∗ natRel w v') := by
  iintro ⟨%m, %rfl, Hc, Hsrc, #Hex⟩
  iexists hl_val(#(m : Int))
  isplitr [Hc Hsrc]
  · unfold natRel
    iexists m
    ipureintro; exact ⟨rfl, rfl⟩
  iframe Hc Hsrc
  iintro !> %x' #Hx
  iexists hl_val(#(m : Int))
  isplitr
  · iintro !>
    iapply Hex $$ Hx
  unfold natRel
  iexists m
  ipureintro; exact ⟨rfl, rfl⟩

/-- Rocq: `strlen_sound`. -/
theorem strlen_sound : ⊢ tfImplements (GF := GF) immStringRel natRel strlen strlen := by
  iloeb as IH
  unfold tfImplements
  iintro !> %v %v' %c %K #HPre Hsrc
  unfold rseq seq
  iintro Hna
  have Hcore := strlen_fundamental_core (GF := GF) strlen c K v v'
  unfold rseq seq Strlen at Hcore
  twp_rec
  twp_rec
  twp_pure
  twp_pure
  ihave H := Hcore $$ [Hsrc] Hna
  · iframe Hsrc HPre
    unfold tfImplements rseq seq
    iexact IH
  iapply rwpR_wand $$ H
  iintro %w ⟨Hna, Hpost⟩
  iframe Hna
  iapply tf_post $$ Hpost

/-- Rocq: `strlen_template_sound`. -/
theorem strlen_template_sound (g : Val) :
    ▷ tfImplements (GF := GF) immStringRel natRel g strlen ⊢
      rseq ⊤ hl(v(&strlenTemplate) v(&g)) fun h => tfImplements immStringRel natRel h strlen := by
  unfold rseq seq
  iintro #IH Hna
  unfold strlenTemplate
  twp_pures
  iframe Hna
  unfold tfImplements
  iintro !> %v %v' %c %K #HPre Hsrc
  unfold rseq seq
  iintro Hna
  have Hcore := strlen_fundamental_core (GF := GF) g c K v v'
  unfold rseq seq Strlen at Hcore
  twp_pure
  ihave H := Hcore $$ [Hsrc] Hna
  · iframe Hsrc HPre
    unfold tfImplements rseq seq
    iexact IH
  iapply rwpR_wand $$ H
  iintro %w ⟨Hna, Hpost⟩
  iframe Hna
  iapply tf_post $$ Hpost

/-- Rocq: `lev_sound`. -/
theorem lev_sound : ⊢ tfImplements (GF := GF) pairImmStringRel natRel lev lev := by
  iloeb as IH
  unfold tfImplements
  iintro !> %v %v' %c %K #HPre Hsrc
  unfold rseq seq
  iintro Hna
  have Hcore := lev_fundamental_core (GF := GF) lev strlen c K v v'
  unfold rseq seq Lev at Hcore
  twp_rec
  twp_rec
  twp_pures
  ihave H := Hcore $$ [Hsrc] Hna
  · iframe Hsrc HPre
    isplitl []
    · inext
      iapply strlen_sound
    unfold tfImplements rseq seq
    iexact IH
  iapply rwpR_wand $$ H
  iintro %w ⟨Hna, Hpost⟩
  iframe Hna
  iapply tf_post $$ Hpost

end Iris.Transfinite.Refinement.Memoization
