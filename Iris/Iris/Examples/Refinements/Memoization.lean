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

theorem lookupKV_getElem? {kvs : List (Val × Val)} {k v : Val} (h : lookupKV kvs k = some v) :
    ∃ i : Nat, kvs[i]? = some (k, v) := by
  induction kvs with
  | nil => simp [lookupKV] at h
  | cons kv kvs ih =>
    obtain ⟨k', v'⟩ := kv
    by_cases hk : k' = k
    · subst hk
      simp [lookupKV] at h
      subst h
      exact ⟨0, rfl⟩
    · have h' : lookupKV kvs k = some v := by simpa [lookupKV, hk] using h
      obtain ⟨i, hi⟩ := ih h'
      exact ⟨i + 1, by simpa using hi⟩

/-- Rocq: `embed`. -/
abbrev embed : Option Val → Val
  | none => hl_val(none())
  | some k => hl_val(some(&k))

theorem bigSepL_timeless' {GF : BundledGFunctors} {α : Type _} (l : List α)
    (Φ : Nat → α → IProp GF) (h : ∀ i a, Timeless (Φ i a)) :
    Timeless ([∗list] i ↦ a ∈ l, Φ i a) := by
  induction l generalizing Φ with
  | nil => exact inferInstanceAs (Timeless (PROP := IProp GF) iprop(emp))
  | cons x xs ih =>
    exact @UPred.sep_timeless' _ _ _ _ (Φ 0 x) _ (h 0 x)
      (ih (fun i v => Φ (i + 1) v) (fun _ _ => h _ _))

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

instance contents_timeless (kvs : List (Val × Val)) (l : Loc) :
    Timeless (contents Comparable kvs l) := by
  induction kvs generalizing l with
  | nil => rw [contents_nil]; infer_instance
  | cons kv kvs ih =>
    obtain ⟨k, n⟩ := kv
    rw [contents_cons]
    refine @UPred.exists_timeless' _ _ _ _ _ _ (fun l' => ?_)
    exact @UPred.sep_timeless' _ _ _ _ _ _ inferInstance
      (@UPred.sep_timeless' _ _ _ _ _ _ inferInstance (ih l'))

/-- A map with the association list `kvs` (Rocq: `Map`). -/
def Map (v : Val) (kvs : List (Val × Val)) : IProp GF :=
  iprop(∃ (l l' : Loc), ⌜v = hl_val(#l)⌝ ∗ l ↦ some hl_val(#l') ∗ contents Comparable kvs l')

instance Map_timeless (v : Val) (kvs : List (Val × Val)) : Timeless (Map Comparable v kvs) := by
  unfold Map
  refine @UPred.exists_timeless' _ _ _ _ _ _ (fun l => ?_)
  refine @UPred.exists_timeless' _ _ _ _ _ _ (fun l' => ?_)
  exact @UPred.sep_timeless' _ _ _ _ _ _ inferInstance
    (@UPred.sep_timeless' _ _ _ _ _ _ inferInstance inferInstance)

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

/-! ## Memoization functions -/

/-- Rocq: `memoize`. -/
def memoize : Val := hl_val%
  λ eq f,
    let h := &map #();
    λ a,
      match &get h eq a with
      | none() => (let y := f a; &set h a y; y)
      | some(y) => y

/-- Rocq: `mem_rec`. -/
def memRec : Val := hl_val%
  λ eq F,
    let h := &map #();
    rec memRec a :=
      match &get h eq a with
      | none() => (let y := F memRec a; &set h a y; y)
      | some(y) => y

/-- The body of the memoized function, after the function `e` computing the results is known. -/
def memoBody (e : Exp) (m eq n : Val) : Exp := hl(
  match v(&get) v(&m) v(&eq) v(&n) with
  | none() => (let y := &e v(&n); v(&set) v(&m) v(&n) y; y)
  | some(y) => y)

/-! ## Timeless memoization -/

section TimelessMemoization

variable {GF : BundledGFunctors} [G : RHeapG GF] [N : NatSourceG GF] [S : SeqG GF]
variable (R : Exp → Val → IProp GF) (Pre Post : Val → Val → IProp GF)
  (Comparable : Val → IProp GF) (Eq : Val → Val → IProp GF)
variable [∀ e v, Timeless (R e v)] [∀ v v', Timeless (Post v v')]
  [∀ v v', Persistent (Pre v v')] [∀ v v', Persistent (Post v v')] [∀ v v', Persistent (Eq v v')]
  [∀ v, Timeless (Comparable v)]
variable (Pre_Comparable : ∀ v v', Pre v v' ⊢ Comparable v)
  (Pre_Eq_Proper : ∀ v₁ v₁' v₂, Eq v₁ v₁' ∗ Pre v₁' v₂ ⊢ Pre v₁ v₂)

open Iris.Transfinite.Refinement.Examples

/-- Rocq: `eval` (with arbitrary stuttering). -/
def evalS (e : Exp) (v : Val) : IProp GF :=
  iprop(∀ K : List ECtxItem, src (fill K e) -∗ srcUpd ⊤ (src (fill K (v : Exp))))

/-- The persistent knowledge about the results stored in the table. -/
def memEntry (f : Val) (kv : Val × Val) : IProp GF :=
  iprop(□ (∀ k', Pre kv.1 k' -∗ ∃ v', □ R hl(v(&f) v(&k')) v' ∗ Post kv.2 v'))

/-- Rocq: `mem_inv`. -/
def memInv (m f : Val) : IProp GF :=
  iprop(∃ kvs : List (Val × Val), Map Comparable m kvs ∗
    [∗list] kv ∈ kvs, memEntry R Pre Post f kv)

instance memEntry_persistent (f : Val) (kv : Val × Val) :
    Persistent (memEntry R Pre Post f kv) := by
  unfold memEntry; infer_instance

instance memEntry_timeless (f : Val) (kv : Val × Val) :
    Timeless (memEntry R Pre Post f kv) := by
  unfold memEntry
  haveI : ∀ k', Timeless iprop(∃ v', □ R hl(v(&f) v(&k')) v' ∗ Post kv.2 v') := fun k' =>
    @UPred.exists_timeless' _ _ _ _ _ _ (fun _ =>
      @UPred.sep_timeless' _ _ _ _ _ _ inferInstance inferInstance)
  infer_instance

instance memInv_timeless (m f : Val) : Timeless (memInv R Pre Post Comparable m f) := by
  unfold memInv
  refine @UPred.exists_timeless' _ _ _ _ _ _ (fun kvs => ?_)
  exact @UPred.sep_timeless' _ _ _ _ _ _ inferInstance
    (bigSepL_timeless' kvs _ fun _ _ => inferInstance)

/-- Rocq: `implements`. -/
def implements (g f : Val) : IProp GF :=
  iprop(□ ∀ x : Val, ∀ x' : Val, ∀ K : List ECtxItem, Pre x x' -∗ src (fill K hl(v(&f) v(&x'))) -∗
    rseq ⊤ hl(v(&g) v(&x)) fun v => iprop(∃ v' : Val, Post v v' ∗ src (fill K (v' : Exp)) ∗
      □ (∀ x', Pre x x' -∗ ∃ v', □ R hl(v(&f) v(&x')) v' ∗ Post v v')))

instance implements_persistent (g f : Val) :
    Persistent (implements R Pre Post g f) := by
  unfold implements; infer_instance

theorem nclose_top (N : Namespace) : (↑N : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full

include Pre_Comparable Pre_Eq_Proper in
/-- Rocq: `memoization_core`. -/
theorem memoization_core (eq f : Val) (e : Exp) (n n' m : Val) (K : List ECtxItem) :
    rseq ⊤ e (fun h => implements R Pre Post h f) ∗
      NonAtomicInvariant.inv S.name refN (memInv R Pre Post Comparable m f) ∗
      □ (∀ e v, R e v -∗ evalS e v) ∗ Pre n n' ∗
      eqfun (src := refSrc (GF := GF)) Comparable eq Eq ∗ src (fill K hl(v(&f) v(&n'))) ⊢
      rseq ⊤ (memoBody e m eq n) fun v => iprop(∃ v' : Val, Post v v' ∗ src (fill K (v' : Exp)) ∗
        □ (∀ n', Pre n n' -∗ ∃ v', □ R hl(v(&f) v(&n')) v' ∗ Post v v')) := by
  unfold rseq seq
  iintro ⟨Spec, #I, #IEval, #HPre, #Heqfun, Hsrc⟩ Hna
  iapply fupd_rwp (src := refSrc (GF := GF))
  imod NonAtomicInvariant.inv_acc_open_timeless (nclose_top refN) (nclose_top refN) $$ I Hna
    with ⟨Hc, Hna, Hclose⟩
  imodintro
  unfold memInv
  icases Hc with ⟨%kvs, HM, #Hupd⟩
  unfold memoBody
  twp_bind (v(&get) v(&m) v(&eq) v(&n))
  ihave Hcomp := Pre_Comparable n n' $$ HPre
  ihave Hget := get_spec (src := refSrc (GF := GF)) Comparable kvs eq Eq m n
  unfold texan
  iapply Hget $$ [HM Hcomp]
  · isplitl [HM]
    · iexact HM
    isplitr [Hcomp]
    · iexact Heqfun
    iexact Hcomp
  iintro %v ⟨%o, %rfl, Ho, HM⟩
  cases o with
  | some k =>
    -- the result was stored before
    unfold getPost
    icases Ho with ⟨%n₀, %hlook, #Heq⟩
    obtain ⟨i, hi⟩ := lookupKV_getElem? hlook
    ihave #Hk := BigSepL.bigSepL_lookup hi $$ Hupd
    ihave #HPre' := Pre_Eq_Proper n₀ n n' $$ [Heq HPre]
    · iframe Heq HPre
    unfold memEntry
    ihave ⟨%v', #HR, #HP⟩ := Hk $$ %n' HPre'
    ihave Hev := IEval $$ %_ %_ HR
    unfold evalS
    ihave Hev := Hev $$ %K Hsrc
    iapply rwp_weaken_src rfl
    iapply srcUpdate_mono (src := refSrc (GF := GF)) (P := src (fill K (v' : Exp)))
    isplitl [Hev]
    · iexact Hev
    iintro Hsrc
    iapply fupd_rwp (src := refSrc (GF := GF))
    imod Hclose $$ [HM Hna] with Hna
    · iframe Hna
      inext
      iexists kvs
      iframe HM Hupd
    imodintro
    simp only [embed]
    twp_pures
    iframe Hna
    iexists v'
    iframe HP Hsrc
    iintro !> %n'' #HPre''
    iapply Hk $$ %n''
    iapply Pre_Eq_Proper n₀ n n''
    iframe Heq HPre''
  | none =>
    -- close the invariant again for the recursive call
    unfold getPost
    iapply fupd_rwp (src := refSrc (GF := GF))
    imod Hclose $$ [HM Hna] with Hna
    · iframe Hna
      inext
      iexists kvs
      iframe HM Hupd
    imodintro
    simp only [embed]
    twp_pures
    twp_bind (&e)
    ihave Spec := Spec $$ Hna
    twp_apply rwpR_wand $$ Spec
    iintro %g ⟨Hna, #Himpl⟩
    unfold implements
    ihave Hres := Himpl $$ %n %n' %K HPre Hsrc
    unfold rseq seq
    ihave Hres := Hres $$ Hna
    twp_bind (v(&g) v(&n))
    twp_apply rwpR_wand $$ Hres
    iintro %v ⟨Hna, %k, #HPost, Hsrc, #Hk⟩
    have hT : Timeless (memInv R Pre Post Comparable m f) := inferInstance
    unfold memInv at hT
    iapply fupd_rwp (src := refSrc (GF := GF))
    imod NonAtomicInvariant.inv_acc_open_timeless (nclose_top refN) (nclose_top refN) $$ I Hna
      with ⟨Hc, Hna, Hclose⟩
    imodintro
    icases Hc with ⟨%kvs₂, HM, #Hupd'⟩
    twp_pures
    ihave Hset := set_spec (src := refSrc (GF := GF)) Comparable kvs₂ m v n
    unfold texan
    twp_apply Hset $$ [HM Hcomp]
    · isplitl [HM]
      · iexact HM
      iexact Hcomp
    iintro %r ⟨%rfl, HM⟩
    iapply fupd_rwp (src := refSrc (GF := GF))
    imod Hclose $$ [HM Hna] with Hna
    · iframe Hna
      inext
      iexists (n, v) :: kvs₂
      iframe HM
      iapply BigSepL.bigSepL_cons.mpr
      iframe Hupd'
      unfold memEntry
      iexact Hk
    imodintro
    twp_pures
    iframe Hna
    iexists k
    iframe HPost Hsrc Hk

end TimelessMemoization

end Iris.Transfinite.Refinement.Memoization
