/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Michael Sammler, Klaus Kraßnitzer
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic List

@[expose] public section

namespace Quicksort

def nil : Val := hl_val% λ _, none()

def cons : Val := hl_val% λ hd tl, some(ref((hd, tl)))

def append : Val := hl_val%
  rec append l1 l2 :=
    match l1 with
    | none() => l2
    | some(x) =>
      let p := !x;
      let head := fst(p);
      let tail := snd(p);
      &cons head (append tail l2)

def partition : Val := hl_val%
  rec partition x l :=
    match l with
    | none() => (none(), none())
    | some(lx) =>
      let p := !lx;
      let head := fst(p);
      let tail := snd(p);
      let part := partition x tail;
      if head ≤ x then
        (&cons head (fst(part)), snd(part))
      else
        (fst(part), &cons head (snd(part)))

def quicksort : Val := hl_val%
  rec quicksort l :=
    match l with
    | none() => l
    | some(x) =>
      let p := !x;
      let head := fst(p);
      let tail := snd(p);
      let part := &partition head tail;
      let a := quicksort (fst(part));
      let b := quicksort (snd(part));
      let e := &cons head b;
      &append a e

/-- Construct a HeapLang version of a Lean list -/
def makeList : List Int → Exp
  | [] => hl% &nil #()
  | l::ls => hl%
    let vls := &(makeList ls);
    &cons #l vls

/-- Returns a boolean witnessing the sortedness of a HeapLang list.
`acc` is an option of the last value in the list. -/
def checkSorted : Val := hl_val%
  rec check acc l :=
    match l with
    | none() => #true
    | some(x) =>
      let p := !x;
      let head := fst(p);
      let tail := snd(p);
      let ok :=
        (match acc with
         | none() => #true
         | some(v) => v ≤ head);
      ok && check (some(head)) tail

section Predicates

variable [HeapLangGS hlc GF]

def isList (v : Val) : List Int → IProp GF
  | [] => iprop% ⌜v = hl_val(none())⌝
  | x :: xs => iprop% ∃ l tl, ⌜v = hl_val(some(#(.loc l)))⌝ ∗
    l ↦ some hl_val((#x, &tl)) ∗ isList tl xs

theorem isList_nil {v} :
  isList (GF:=GF) v [] ⊣⊢ iprop(⌜v = hl_val(none())⌝) := .rfl

theorem isList_cons {v x xs} :
  isList (GF:=GF) v (x :: xs) ⊣⊢ iprop(∃ l tl, ⌜v = hl_val(some(#(.loc l)))⌝ ∗
    l ↦ some hl_val((#x, &tl)) ∗ isList tl xs) := .rfl

end Predicates

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

theorem nil_spec :
    {{ (emp : IProp GF) }}
      hl(v(&nil) #())
    {{ v, RET v; isList v [] }} := by
  iintro %Φ - Hl
  wp_rec
  wp_pures
  imodintro
  iapply Hl
  iapply isList_nil
  itrivial

theorem cons_spec x l ls :
    {{ isList (GF:=GF) l ls }}
      hl(&cons #x &l)
    {{v, RET v; isList v (x :: ls)}} := by
  iintro %Φ Hl HΦ
  wp_rec; wp_pures
  wp_alloc l
  wp_pures
  imodintro
  iapply HΦ
  rw [isList]
  iexists _, _; iframe
  itrivial

theorem append_spec l1 ls1 l2 ls2 :
    {{ isList (GF:=GF) l1 ls1 ∗ isList l2 ls2 }}
      hl(&append &l1 &l2)
    {{v, RET v; isList v (ls1 ++ ls2) }} := by
  iintro %Φ ⟨Hl1, Hl2⟩ HΦ
  iloeb as IH generalizing %l1 %ls1 %Φ
  wp_rec; wp_pures
  cases ls1 with
  | nil =>
    simp [isList_nil.to_eq]
    icases Hl1 with %heq; subst heq
    wp_pures; imodintro
    iapply HΦ $$ [$]
  | cons x xs =>
    icases isList_cons $$ Hl1 with ⟨%l, %tl, %heq, Hpt, Hl⟩
    subst heq; wp_pures
    wp_load
    wp_smart_apply IH $$ Hl Hl2 with %_ Hl
    wp_smart_apply cons_spec $$ [$] with %_ _
    iapply HΦ
    simp
    itrivial

theorem partition_spec x l ls :
    {{ isList (GF:=GF) l ls }}
      hl(&partition #x &l)
    {{ l1 l2, RET hl_val((&l1, &l2));
      isList l1 (ls.filter (· ≤ x)) ∗
      isList l2 (ls.filter (x < ·)) }} := by
  iintro %Φ
  iloeb as IH generalizing %l %ls %Φ
  iintro Hl HΦ; wp_rec; rw [isList.eq_def]
  cases ls with dsimp only
  | nil =>
    icases Hl with %rfl
    wp_pures; imodintro
    iapply HΦ <;> simp [isList] <;> itrivial
  | cons hd ls =>
    icases Hl with ⟨%_, %tl, %rfl, Hpt, Hl⟩
    wp_load
    wp_smart_apply IH $$ Hl with %l1 %l2 ⟨Hl1, Hl2⟩
    wp_pures
    by_cases hd ≤ x <;> simp [*]
    · wp_smart_apply cons_spec $$ Hl1 with %_ _
      wp_pures
      imodintro
      iapply HΦ $$ [$]
    · wp_smart_apply cons_spec $$ Hl2 with %_ _
      wp_pures
      imodintro
      iapply HΦ
      have : x < hd := by grind
      simp [*]
      iframe

theorem quicksort_spec l ls :
    {{ isList (GF:=GF) l ls }}
      hl(&quicksort &l)
    {{ l' ls', RET l'; isList l' ls' ∗
      ⌜Pairwise LE.le ls'⌝ ∗
      ⌜ls ~ ls'⌝}} := by
  iloeb as IH generalizing %l %ls
  iintro %Φ Hl HΦ; wp_rec; rw [isList.eq_def]
  cases ls with dsimp only
  | nil =>
    icases Hl with %rfl
    wp_pures; imodintro
    iapply HΦ $$ %_ %([]) <;> simp [isList] <;> itrivial
  | cons head tail =>
    icases Hl with ⟨%l, %tl, %rfl, Hpt, Hl⟩
    wp_load
    wp_smart_apply partition_spec $$ [$] with %l1 %l2 ⟨Hl1, Hl2⟩
    wp_smart_apply IH $$ [$Hl1] with %l1' %ls1' ⟨Hl1, %_, %_⟩
    wp_smart_apply IH $$ [$Hl2] with %l2' %ls2' ⟨Hl2, %_, %_⟩
    wp_smart_apply cons_spec $$ Hl2 with %_ Hcons
    wp_smart_apply append_spec $$ [$Hl1 $Hcons] with %_ _
    iapply HΦ; iframe; isplit <;> ipureintro
    · have : ls2'.all (head < ·) := by grind
      grind [pairwise_cons]
    · grind [filter_append_perm]

theorem wp_makeList (l : List Int) :
    {{ (emp : IProp GF) }}
      hl(&(makeList l))
    {{ v, RET v;  isList v l }} := by
  iintro %Φ - HΦ
  iinduction l generalizing %Φ HΦ with
  | nil =>
    unfold makeList
    iapply nil_spec $$ [//] HΦ
  | cons l ls ih =>
    rw [makeList]
    wp_pures
    wp_apply ih with %v Hv
    wp_pures
    iapply cons_spec $$ Hv [$HΦ]

/- When a HeapLang list is sorted, checkSorted returns true -/
theorem wp_checkSorted (v vacc : Val) (l : List Int) :
    {{ isList (GF := GF) v l ∗
    ⌜List.Pairwise (· ≤ ·) l⌝ ∗
    ⌜vacc = hl_val(none()) ∨ ∃ va : Int, vacc = hl_val(some(#va)) ∧ ∀ lv ∈ l, va ≤ lv⌝ }}
      hl(&checkSorted &vacc &v)
    {{ bv, RET bv;  isList v l ∗ ⌜bv = hl_val(#true)⌝}} := by
  iintro %Φ ⟨H, %hsorted, %hinv⟩ HΦ
  iloeb as IH generalizing %vacc %l %v %hsorted %hinv
  wp_rec; wp_pures
  cases l with
  | nil =>
    icases isList_nil $$ H with %heq; subst heq
    wp_pures
    imodintro
    iapply HΦ $$ [$H]
    itrivial
  | cons hd tl =>
    icases isList_cons $$ H with ⟨%loc, %tlv, %heq, Hpt, Htl⟩
    subst heq
    wp_pures
    wp_load
    rcases hinv with rfl | ⟨va, rfl, hva⟩
    · wp_pures
      wp_apply IH $$ %_ %tl %_ %((List.pairwise_cons.mp hsorted).2)
        %(Or.inr ⟨hd, rfl, fun lv h => (List.pairwise_cons.mp hsorted).1 lv h⟩) Htl with %bv ⟨Hl, %hb⟩
      iapply HΦ $$ [Hpt Hl]
      isplit
      · rw [isList]
        iframe
        itrivial
      itrivial
    · wp_pures
      rw [decide_eq_true (hva hd List.mem_cons_self)]
      wp_pures
      iapply IH $$ %_ %tl %_ %((List.pairwise_cons.mp hsorted).2)
        %(.inr ⟨hd, rfl, (List.pairwise_cons.mp hsorted).1⟩) Htl
      iintro %bv !> ⟨Hl, %hb⟩
      iapply HΦ $$ [Hpt Hl]
      isplit
      · rw [isList]
        iframe
        itrivial
      itrivial

end Specs

section Closed

/-- Construct a HeapLang list, quicksort it, and check that it is sorted. -/
def sortAndCheck (l : List Int) : Exp := hl%
  let v := &(makeList l);
  let v' := &quicksort v;
  &checkSorted (none()) v'

theorem sortAndCheck_spec [HeapLangGS hlc GF] (l : List Int) :
    {{ (True : IProp GF) }} (sortAndCheck l) {{ RET hl_val(#true); True}} := by
  unfold sortAndCheck
  iintro %Φ - HΦ
  wp_apply wp_makeList $$ [//] with %v Hv
  wp_pures
  wp_bind &quicksort _
  iapply quicksort_spec $$ Hv
  iintro !> %v %l' ⟨Hv, %Hsorted, %Heqv⟩
  wp_pures
  wp_apply wp_checkSorted $$ [$Hv] with %bv ⟨Hv', %rfl⟩
  · itrivial
  iapply HΦ $$ [//]

/-- Full application of adequacy: sortAndCheck is safe in any state and only ever return true. -/
theorem sortAndCheckAdequate (l : List Int) (σ : State) :
    adequate .NotStuck (sortAndCheck l) σ (fun v _ => v = hl_val(#true)) := by
  apply heap_adequacy (GF := HeapLangS); intro _
  iapply sortAndCheck_spec <;> itrivial

end Closed
