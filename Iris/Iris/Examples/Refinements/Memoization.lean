/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Examples.Refinements.Derived

/-! # Memoization

This file ports the first part of `theories/examples/refinements/memoization.v` of Transfinite
Iris: an association-list map in the heap, memoizing combinators (`memoize` for a function and
`mem_rec` for recursive functions given by a template), and the refinement proof that the
memoized functions implement their specification (`memoize_spec`, `mem_rec_spec`).

The maps are described by their association lists (instead of `gmap val val`): lookups return the
first binding of a key.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement.Memoization

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation

set_option linter.unusedSectionVars false

/-- The namespace of the memoization invariant (Rocq: `refN`). -/
def refN : Namespace := nroot.@"ref"

/-- Equality on values (Rocq: `eq_heaplang`). -/
def eqHeaplang : Val := hl_val% λ n1 n2, n1 = n2

/-! ## Maps -/

/-- Rocq: `map`. -/
def map : Val := hl_val% λ _, ref(ref(none()))

/-- Rocq: `get`. -/
def get : Val := hl_val%
  λ m eq a,
    (rec get h a :=
      match !h with
      | none() => none()
      | some(p) =>
        let kv := fst(p); let next := snd(p);
        if eq (fst(kv)) a then some(snd(kv)) else get next a) (!m) a

/-- Rocq: `set`. -/
def set : Val := hl_val% λ h a v, h ← ref(some(((a, v), !h)))

/-- The loop of `get`, for a given equality function. -/
abbrev getLoop (eq : Val) : Val := hl_val%
  rec get h a :=
    match !h with
    | none() => none()
    | some(p) =>
      let kv := fst(p); let next := snd(p);
      if &eq (fst(kv)) a then some(snd(kv)) else get next a

/-- The first binding of a key in an association list. -/
def lookupKV (kvs : List (Val × Val)) (k : Val) : Option Val :=
  (kvs.find? (·.1 = k)).map (·.2)

/-- Rocq: `embed`. -/
abbrev embed : Option Val → Val
  | none => hl_val(none())
  | some k => hl_val(some(&k))

section MapSimple

variable {GF : BundledGFunctors} [Hheap : HeapLangTGS GF] {A : Type _} [src : Source GF A]
variable (Comparable : Val → IProp GF) [∀ v, Timeless (Comparable v)]

/-- Refinement weakest preconditions for the heap_lang programs of the map. -/
abbrev rwpH (e : Exp) (Φ : Val → IProp GF) : IProp GF :=
  rwp (src := src) (ι := heapRefIrisGS) .NotStuck ⊤ e Φ

/-- Texan triples for `rwpH` (Rocq: `⟨⟨⟨ P ⟩⟩⟩ e ⟨⟨⟨ v, RET v; Q ⟩⟩⟩`). -/
def texan (P : IProp GF) (e : Exp) (Q : Val → IProp GF) : IProp GF :=
  iprop(□ ∀ Φ : Val → IProp GF, P -∗ (∀ v, Q v -∗ Φ v) -∗ rwpH (src := src) e Φ)

/-- The linked list of an association list (Rocq: `contents`). -/
def contents : List (Val × Val) → Loc → IProp GF
  | [], l => iprop(l ↦ some hl_val(none()))
  | (k, n) :: kvs, l => iprop(∃ l' : Loc, Comparable k ∗
      l ↦ some hl_val(some(((&k, &n), #l'))) ∗ contents kvs l')

theorem contents_nil (l : Loc) : contents Comparable [] l = iprop(l ↦ some hl_val(none())) := rfl

theorem contents_cons (k n : Val) (kvs : List (Val × Val)) (l : Loc) :
    contents Comparable ((k, n) :: kvs) l = iprop(∃ l' : Loc, Comparable k ∗
      l ↦ some hl_val(some(((&k, &n), #l'))) ∗ contents Comparable kvs l') := rfl

/-- A map with the association list `kvs` (Rocq: `Map`). -/
def Map (v : Val) (kvs : List (Val × Val)) : IProp GF :=
  iprop(∃ (l l' : Loc), ⌜v = hl_val(#l)⌝ ∗ l ↦ some hl_val(#l') ∗ contents Comparable kvs l')

/-- Rocq: `map_spec`. -/
theorem map_spec : ⊢ texan (src := src) iprop(True) hl(v(&map) #()) fun v => Map Comparable v [] := by
  unfold texan
  iintro !> %Φ - Hpost
  unfold map
  twp_pures
  twp_apply rwp_alloc
  iintro %r Hr
  twp_apply rwp_alloc
  iintro %h Hh
  iapply Hpost
  unfold Map
  iexists h, r
  isplitr
  · ipureintro; rfl
  iframe
  rw [contents_nil]
  iexact Hr

/-- Rocq: `eqfun`. -/
def eqfun (eq : Val) (Q : Val → Val → IProp GF) : IProp GF :=
  iprop(∀ n₁ : Val, ∀ n₂ : Val, (texan (src := src) iprop(Comparable n₁ ∗ Comparable n₂)
    hl(v(&eq) v(&n₁) v(&n₂))
    (fun r => iprop(∃ b : Bool, ⌜r = hl_val(#b)⌝ ∗ Comparable n₁ ∗ Comparable n₂ ∗
      (if b then Q n₁ n₂ else iprop(Q n₁ n₂ -∗ False)))) : IProp GF))

instance eqfun_persistent (eq : Val) (Q : Val → Val → IProp GF) :
    Persistent (eqfun (src := src) Comparable eq Q) := by
  unfold eqfun texan; infer_instance

/-- The postcondition of `get`. -/
def getPost (Q : Val → Val → IProp GF) (kvs : List (Val × Val)) (n : Val) :
    Option Val → IProp GF
  | some v => iprop(∃ n', ⌜lookupKV kvs n' = some v⌝ ∗ Q n' n)
  | none => iprop(∀ n', ⌜(lookupKV kvs n').isSome⌝ -∗ Q n' n -∗ False)

theorem get_loop (eq : Val) (Q : Val → Val → IProp GF) (n : Val) (Φ : Val → IProp GF)
    (kvs : List (Val × Val)) (r : Loc) :
    ⊢ eqfun (src := src) Comparable eq Q -∗ Comparable n -∗ contents Comparable kvs r -∗
      (∀ o, contents Comparable kvs r -∗ getPost Q kvs n o -∗ Φ (embed o)) -∗
      rwpH (src := src) hl(v(&(getLoop eq)) #r v(&n)) Φ := by
  induction kvs generalizing r with
  | nil =>
    iintro #Heq Hn Hc Hpost
    rw [contents_nil]
    twp_rec
    twp_pures
    twp_apply rwp_load $$ Hc
    iintro Hc
    twp_pures
    iapply Hpost $$ %none [Hc]
    · iexact Hc
    unfold getPost
    iintro %n' %h
    simp [lookupKV] at h
  | cons kv kvs ih =>
    obtain ⟨k, n'⟩ := kv
    iintro #Heq Hn Hc Hpost
    rw [contents_cons]
    icases Hc with ⟨%l', Hk, Hr, Hc⟩
    twp_rec
    twp_pures
    twp_apply rwp_load $$ Hr
    iintro Hr
    twp_pures
    ihave IH := ih l'
    unfold eqfun texan
    ihave Heq' := Heq $$ %k %n
    twp_apply Heq' $$ [Hk Hn]
    · iframe
    iintro %v ⟨%b, %rfl, Hk, Hn, Hif⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      twp_pure
      iapply IH $$ Heq Hn Hc
      iintro %o Hc Ho
      iapply Hpost $$ %o [Hk Hr Hc] [Ho Hif]
      · iexists l'
        iframe
      · cases o with
        | some w =>
          unfold getPost
          icases Ho with ⟨%k', %hk', HQ⟩
          iexists k'
          by_cases hkk : k = k'
          · subst hkk
            iexfalso
            iapply Hif $$ HQ
          · iframe
            ipureintro
            simp [lookupKV, hkk] at hk' ⊢
            exact hk'
        | none =>
          unfold getPost
          iintro %k' %hk' HQ
          by_cases hkk : k = k'
          · subst hkk
            iapply Hif $$ HQ
          · iapply Ho $$ %k' %(by simpa [lookupKV, List.find?_cons, hkk] using hk') HQ
    · simp only [↓reduceIte]
      twp_pures
      iapply Hpost $$ %(some n') [Hk Hr Hc] [Hif]
      · iexists l'
        iframe
      · unfold getPost
        iexists k
        iframe
        ipureintro
        simp [lookupKV]

/-- Rocq: `get_spec`. -/
theorem get_spec (kvs : List (Val × Val)) (eq : Val) (Q : Val → Val → IProp GF) (m n : Val) :
    ⊢ texan (src := src) iprop(Map Comparable m kvs ∗ eqfun (src := src) Comparable eq Q ∗ Comparable n)
      hl(v(&get) v(&m) v(&eq) v(&n))
      fun r => iprop(∃ o, ⌜r = embed o⌝ ∗ getPost Q kvs n o ∗ Map Comparable m kvs) := by
  unfold texan
  iintro !> %Φ ⟨HM, #Heq, Hn⟩ Hpost
  unfold Map
  icases HM with ⟨%l, %r, %rfl, Hr, Hc⟩
  unfold get
  twp_pures
  twp_apply rwp_load $$ Hr
  iintro Hr
  twp_pure
  iapply get_loop $$ Heq Hn Hc
  iintro %o Hc Ho
  iapply Hpost
  iexists o
  isplitr
  · ipureintro; rfl
  iframe
  ipureintro; rfl

/-- Rocq: `set_spec`. -/
theorem set_spec (kvs : List (Val × Val)) (m n k : Val) :
    ⊢ texan (src := src) iprop(Map Comparable m kvs ∗ Comparable k) hl(v(&set) v(&m) v(&k) v(&n))
      fun r => iprop(⌜r = hl_val(#())⌝ ∗ Map Comparable m ((k, n) :: kvs)) := by
  unfold texan
  iintro !> %Φ ⟨HM, Hk⟩ Hpost
  unfold Map
  icases HM with ⟨%l, %r, %rfl, Hr, Hc⟩
  unfold set
  twp_pures
  twp_apply rwp_load $$ Hr
  iintro Hr
  twp_pures
  twp_apply rwp_alloc
  iintro %r' Hr'
  twp_pures
  twp_apply rwp_store $$ Hr
  iintro Hr
  iapply Hpost
  isplitr
  · ipureintro; rfl
  iexists l, r'
  isplitr
  · ipureintro; rfl
  iframe
  rw [contents_cons]
  iexists r
  iframe

end MapSimple

end Iris.Transfinite.Refinement.Memoization
