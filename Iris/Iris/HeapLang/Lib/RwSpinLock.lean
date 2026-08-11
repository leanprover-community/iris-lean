/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.LeibnizMultiSet
public import Iris.HeapLang.Lib.RwLock
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.Instances.Lib.Invariants
public import Iris.Std.GenMultiSetsInstances
public import Iris.Std.Namespaces

namespace Iris.HeapLang

open BI Iris Std ProgramLogic CMRA OFE LeibnizMultiSet FiniteMultiSet

@[expose] public section

namespace RwSpinLock

@[rocq_alias heap_lang.newlock]
def newlock : Val := hl_val(
  λ _, ref(#0))

@[rocq_alias heap_lang.try_acquire_reader]
def tryAcquireReader : Val := hl_val(
  λ l,
    let n := !l;
    if #0 ≤ n
      then cas(l, n, n + #1)
      else #false)

@[rocq_alias heap_lang.acquire_reader]
def acquireReader : Val := hl_val(
  rec acquire l :=
    if (&tryAcquireReader l)
      then #()
      else acquire l)

@[rocq_alias heap_lang.release_reader]
def releaseReader : Val := hl_val(
  λ l, faa(l, #(-1 : Int)); #())

@[rocq_alias heap_lang.try_acquire_writer]
def tryAcquireWriter : Val := hl_val(
  λ l, cas(l, #0, #(-1 : Int)))

@[rocq_alias heap_lang.acquire_writer]
def acquireWriter : Val := hl_val(
  rec acquire l :=
    if (&tryAcquireWriter l)
      then #()
      else acquire l)

@[rocq_alias heap_lang.release_writer]
def releaseWriter : Val := hl_val(
  λ l, l ← #0)

/-- The multiset of fractions that have been handed out to readers. -/
abbrev ReaderFracs := ListPerm Qp

abbrev RwSpinLockF : COFE.OFunctorPre := constOF (Auth (LeibnizMultiSet ReaderFracs))

@[rocq_alias heap_lang.rw_spin_lockG]
class RwSpinLockG (GF : BundledGFunctors) where [elemG : ElemG GF RwSpinLockF]

attribute [reducible, instance] RwSpinLockG.elemG

#rocq_ignore heap_lang.«rw_spin_lockΣ»
  "Superseded by the `RwSpinLockG` typeclass on `BundledGFunctors`."
#rocq_ignore heap_lang.«subG_rw_spin_lockΣ»
  "Superseded by Lean's direct `ElemG` typeclass synthesis."

section proof

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [RwSpinLockG GF]

def rwLockN : Namespace := nroot .@ "rw_lock"

/-- Shorthand for ghost ownership of the reader-set authority. -/
abbrev own (γ : GName) (a : Auth (LeibnizMultiSet ReaderFracs)) : IProp GF :=
  iOwn (F := RwSpinLockF) γ a

/-- We need *some* ghost state that allows us to establish a contradiction in the left disjunct
(where the lock is write-locked) when proving `releaseReader_spec`, so we use a fraction of the
empty authoritative reader set (the rest goes to `writerLocked`). Any fraction would do, but the
benefit of giving over half to `writerLocked` (and keeping less than half here) is that we can
prove `writerLocked_exclusive`. -/
@[rocq_alias heap_lang.rw_state_inv]
def rwStateInv (γ : GName) (l : Loc) (Φ : Qp → IProp GF) : IProp GF := iprop%
  ∃ z : Int, l ↦ some hl_val(#z) ∗
    (⌜z = -1⌝ ∗ own γ (●{.own Qp.quarter} (.ofSet ∅))
     ∨ ⌜0 ≤ z⌝ ∗ ∃ (q : Qp) (g : ReaderFracs),
         own γ (● .ofSet g) ∗
         ⌜size g = z.toNat⌝ ∗
         ⌜fold Qp.add q g = 1⌝ ∗
         Φ q)

/-- The `▷` in front of `internalFractional` is preserved even when taking steps, which makes it
easier to re-establish. -/
@[rocq_alias heap_lang.is_rw_lock]
def isRwLock (γ : GName) (lk : Val) (Φ : Qp → IProp GF) : IProp GF := iprop%
  ▷ internalFractional Φ ∗ ∃ l : Loc, ⌜lk = hl_val(#l)⌝ ∗ inv rwLockN (rwStateInv γ l Φ)

@[rocq_alias heap_lang.is_rw_lock_persistent]
instance instIsRwLockPersistent (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    Persistent (isRwLock γ lk Φ) := by unfold isRwLock; infer_instance

@[rocq_alias heap_lang.reader_locked]
def readerLocked (γ : GName) (q : Qp) : IProp GF := own γ (◯ .ofSet {q})

@[rocq_alias heap_lang.writer_locked]
def writerLocked (γ : GName) : IProp GF := own γ (●{.own Qp.threeQuarters} .ofSet ∅)

instance instReaderLockedTimeless (γ : GName) (q : Qp) :
    Timeless (readerLocked (GF := GF) γ q) := by unfold readerLocked; infer_instance

instance instWriterLockedTimeless (γ : GName) :
    Timeless (writerLocked (GF := GF) γ) := by unfold writerLocked; infer_instance

/-- Full authoritative ownership of the empty reader set splits into the quarter kept by
`rwStateInv` and the three quarters owned by `writerLocked`. -/
theorem own_auth_empty_split (γ : GName) :
    own (GF := GF) γ (●{.own Qp.quarter} .ofSet (∅ : ReaderFracs)) ∗
      own γ (●{.own Qp.threeQuarters} .ofSet ∅) ⊣⊢ own γ (● .ofSet (∅ : ReaderFracs)) := by
  have hsplit : (● .ofSet (∅ : ReaderFracs) : Auth (LeibnizMultiSet ReaderFracs))
      = (●{.own Qp.quarter} LeibnizMultiSet.ofSet (∅ : ReaderFracs)) • ●{.own Qp.threeQuarters} LeibnizMultiSet.ofSet ∅ := by
    rw [← Auth.auth_dfrac_op, DFrac.op_own, Qp.quarter_add_threeQuarters]
  rw [hsplit]
  exact iOwn_op.symm

@[rocq_alias heap_lang.writer_locked_exclusive]
theorem writerLocked_exclusive (γ : GName) :
    writerLocked γ ∗ writerLocked γ ⊢@{IProp GF} False := by
  unfold writerLocked
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hvalid
  rw [Auth.auth_dfrac_op_valid, DFrac.op_own, DFrac.valid_own] at Hvalid
  grind

@[rocq_alias heap_lang.writer_locked_not_reader_locked]
theorem writerLocked_not_readerLocked (γ : GName) (q : Qp) :
    writerLocked γ ∗ readerLocked γ q ⊢@{IProp GF} False := by
  unfold writerLocked readerLocked
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hvalid
  have hq := subset_iff.mp
    (included_iff_subset.mp (Auth.both_dfrac_valid_discrete.mp Hvalid).2.1) q
  rw [multiplicity_singleton_eq, multiplicity_empty] at hq
  omega

@[rocq_alias heap_lang.is_rw_lock_iff]
theorem isRwLock_iff (γ : GName) (lk : Val) (Φ Ψ : Qp → IProp GF) :
    isRwLock γ lk Φ ⊢ (▷ □ ∀ q, Φ q ∗-∗ Ψ q) -∗ isRwLock γ lk Ψ := by
  unfold isRwLock rwStateInv
  iintro ⟨#HΦdup, %l, %Heq, #Hlockinv⟩ #Hiff
  subst Heq
  isplitl []
  · inext
    iapply internalFractional_iff $$ Hiff HΦdup
  iexists l
  isplitl []
  · itrivial
  iapply inv_iff $$ Hlockinv
  inext
  imodintro
  isplit
  · iintro ⟨%z, Hl, (Hneg | ⟨Hge, %q, %g, Hauth, Hsize, Hfold, HΦ⟩)⟩
    · iexists z
      iframe Hl Hneg
    iexists z
    iframe Hl
    iright
    iframe Hge
    iexists q, g
    iframe Hauth Hsize Hfold
    iapply Hiff $$ HΦ
  · iintro ⟨%z, Hl, (Hneg | ⟨Hge, %q, %g, Hauth, Hsize, Hfold, HΨ⟩)⟩
    · iexists z
      iframe Hl Hneg
    iexists z
    iframe Hl
    iright
    iframe Hge
    iexists q, g
    iframe Hauth Hsize Hfold
    iapply Hiff $$ HΨ

/-! ## Helper lemmas for "auth of a multiset" -/

@[rocq_alias heap_lang.auth_valid_gmultiset_singleton]
theorem auth_valid_singleton {MS : Type _} [LawfulMultiSet MS A] {dq : DFrac} {v : A} {g : MS}
    (h : ✓ ((●{dq} .ofSet g : Auth (LeibnizMultiSet MS)) • ◯ LeibnizMultiSet.ofSet {v})) : v ∈ g :=
  singleton_subset_iff.mp (included_iff_subset.mp (Auth.both_dfrac_valid_discrete.mp h).2.1)

@[rocq_alias heap_lang.own_auth_gmultiset_singleton_2]
theorem own_auth_singleton_2 {γ : GName} {dq : DFrac} {v : Qp} {g : ReaderFracs} :
    own (GF := GF) γ (●{dq} .ofSet g) ∗ own γ (◯ .ofSet {v}) ⊢ ⌜v ∈ g⌝ := by
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureintro
  exact auth_valid_singleton Hvalid

@[rocq_alias heap_lang.newlock_spec]
theorem newlock_spec (Φ : Qp → IProp GF) {P : IProp GF} {ioΦ ioq}
    [hP : AsFractional P ioΦ Φ ioq 1] :
    {{ P }} hl(&newlock #()) {{ lk γ, RET lk; isRwLock γ lk Φ }} := by
  iintro %φ HP Hφ
  wp_rec
  imod iOwn_alloc (F := RwSpinLockF) (● .ofSet ∅) (Auth.auth_valid.mpr trivial) with ⟨%γ, Hγ⟩
  wp_alloc l with Hl
  imod inv_alloc rwLockN ⊤ (rwStateInv γ l Φ) $$ [Hl Hγ HP] with #Hinv
  · unfold rwStateInv
    iexists (0 : Int)
    iframe Hl
    iright
    isplitl []
    · ipureintro
      omega
    iexists 1, (∅ : ReaderFracs)
    iframe Hγ
    isplitl []
    · ipureintro
      exact size_empty
    isplitl []
    · ipureintro
      exact fold_empty
    iapply hP.as_fractional.mp $$ HP
  imodintro
  iapply Hφ
  unfold isRwLock
  isplitl []
  · inext
    iapply fractional_internalFractional hP.as_fractional_fractional
  iexists l
  iframe Hinv
  itrivial

@[rocq_alias heap_lang.try_acquire_reader_spec]
theorem tryAcquireReader_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ }} hl(&tryAcquireReader &lk)
    {{ (b : Bool), RET hl_val(#b);
       if b then iprop(∃ q, readerLocked γ q ∗ Φ q) else iprop(True) }} := by
  unfold isRwLock internalFractional
  iintro %φ ⟨#HΦdup, %l, %Heq, #Hlockinv⟩ Hφ
  subst Heq
  wp_rec
  wp_bind !_
  iapply wp_atomic
  imod inv_acc $$ Hlockinv with ⟨G1, G2⟩
  · simp
  unfold rwStateInv
  imodintro
  icases G1 with ⟨%z, Hl, Hz⟩
  wp_load
  imod G2 $$ [Hl Hz]
  · iexists z
    iframe Hl Hz
  imodintro
  wp_pures
  by_cases hle : (0 : Int) ≤ z
  case neg =>
    rw [decide_eq_false hle]
    wp_pures
    iapply Hφ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  rw [decide_eq_true hle]
  wp_pures
  wp_bind cmpXchg(_, _, _)
  iapply wp_atomic
  imod inv_acc $$ Hlockinv with ⟨G1, G2⟩
  · simp
  imodintro
  icases G1 with ⟨%z', Hl, Hz⟩
  wp_cmpxchg with hsuc hfail
  · obtain rfl : z = z' := by simpa using hsuc.symm
    icases Hz with (⟨%Hneg, -⟩ | ⟨-, %q, %g, Hauth, %Hsize, %Hfold, HΦ⟩)
    · omega
    ihave HΦ : iprop(Φ (q.half + q.half)) $$ [HΦ]
    · rw [Qp.half_add_half]
      iexact HΦ
    icases HΦdup $$ %q.half %q.half HΦ with ⟨HΦ, HΦgive⟩
    have halloc : (● .ofSet g : Auth (LeibnizMultiSet ReaderFracs)) ~~>
        (● LeibnizMultiSet.ofSet (g ⊎ {q.half})) • ◯ LeibnizMultiSet.ofSet ({q.half} : ReaderFracs) :=
      Auth.auth_update_alloc (localUpdate (Y := ∅) disjUnion_empty_right.symm)
    imod iOwn_update halloc $$ Hauth with ⟨Hauth, Hview⟩
    imod G2 $$ [Hl Hauth HΦ]
    · iexists (z + 1)
      iframe Hl
      iright
      isplitl []
      · ipureintro
        omega
      iexists q.half, (g ⊎ {q.half})
      iframe Hauth HΦ
      isplitl []
      · ipureintro
        rw [size_disjUnion, size_singleton, Hsize]
        omega
      ipureintro
      calc fold Qp.add q.half (g ⊎ {q.half})
          = fold Qp.add (fold Qp.add q.half {q.half}) g :=
            fold_disjUnion fun x y z => Qp.add_left_comm y x z
        _ = fold Qp.add q g :=
            congrArg (fold Qp.add · g) (fold_singleton.trans (Qp.half_add_half q))
        _ = 1 := Hfold
    imodintro
    wp_pures
    iapply Hφ
    simp only [↓reduceIte]
    unfold readerLocked
    iexists q.half
    iframe Hview HΦgive
  · imod G2 $$ [Hl Hz]
    · iexists z'
      iframe Hl Hz
    imodintro
    wp_pures
    iapply Hφ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

@[rocq_alias heap_lang.acquire_reader_spec]
theorem acquireReader_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ }} hl(&acquireReader &lk)
    {{ q, RET hl_val(#()); readerLocked γ q ∗ Φ q }} := by
  iintro %φ #Hislock Hφ
  iloeb as IH
  wp_rec
  wp_bind &tryAcquireReader _
  iapply tryAcquireReader_spec $$ Hislock
  iintro !> %b Hb
  cases b
  · wp_pure
    iapply IH
    inext
    iexact Hφ
  · wp_pure
    imodintro
    simp only [↓reduceIte]
    icases Hb with ⟨%q, Hlocked, HΦ⟩
    iapply Hφ $$ %q
    iframe Hlocked HΦ

@[rocq_alias heap_lang.release_reader_spec]
theorem releaseReader_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) (q : Qp) :
    {{ isRwLock γ lk Φ ∗ readerLocked γ q ∗ Φ q }} hl(&releaseReader &lk)
    {{ RET hl_val(#()); True }} := by
  unfold isRwLock internalFractional readerLocked
  iintro %φ ⟨⟨#HΦdup, %l, %Heq, #Hlockinv⟩, Hlocked, HΦ⟩ Hφ
  subst Heq
  wp_rec
  wp_bind faa(_, _)
  iapply wp_atomic
  imod inv_acc $$ Hlockinv with ⟨G1, G2⟩
  · simp
  unfold rwStateInv
  imodintro
  icases G1 with ⟨%z, Hl, Hz⟩
  wp_faa
  icases Hz with (⟨-, Hempty⟩ | ⟨%Hge, %q', %g, Hauth, %Hsize, %Hsum, HΦq'⟩)
  · ihave %Hmem : ⌜q ∈ (∅ : ReaderFracs)⌝ $$ [Hempty Hlocked]
    · iapply own_auth_singleton_2
      iframe Hempty Hlocked
    rw [mem_iff_multiplicity_pos, multiplicity_empty] at Hmem
    omega
  ihave %Hmem : ⌜q ∈ g⌝ $$ [Hauth Hlocked]
  · iapply own_auth_singleton_2
    iframe Hauth Hlocked
  have hpos : 0 < z := by
    have hne : size g ≠ 0 := fun h => by
      rw [size_eq_zero_iff.mp h, mem_iff_multiplicity_pos, multiplicity_empty] at Hmem
      omega
    omega
  have hdealloc :
      ((● .ofSet g : Auth (LeibnizMultiSet ReaderFracs)) • ◯ LeibnizMultiSet.ofSet ({q} : ReaderFracs)) ~~>
        ● .ofSet (g \ {q}) :=
    Auth.auth_update_dealloc (localUpdate (Y' := ∅) (by
      rw [disjUnion_empty_right, disjUnion_comm, ← disjUnion_singleton_difference Hmem]))
  imod iOwn_update_op (F := RwSpinLockF) hdealloc $$ [$Hauth $Hlocked] with Hauth
  ihave HΦsum : iprop(Φ (q + q')) $$ [HΦ HΦq']
  · iapply HΦdup $$ %q %q' [$HΦ $HΦq']
  imod G2 $$ [Hl Hauth HΦsum]
  · iexists (z + -1)
    iframe Hl
    iright
    isplitl []
    · ipureintro
      omega
    iexists (q + q'), (g \ {q})
    iframe Hauth HΦsum
    isplitl []
    · ipureintro
      rw [size_difference (singleton_subset_iff.mpr Hmem), size_singleton, Hsize]
      omega
    ipureintro
    calc fold Qp.add (Qp.add q q') (g \ {q})
        = Qp.add q (fold Qp.add q' (g \ {q})) :=
          fold_comm_acc (g := Qp.add q) fun x y => Qp.add_left_comm x q y
      _ = fold Qp.add (fold Qp.add q' (g \ {q})) {q} := fold_singleton.symm
      _ = fold Qp.add q' ({q} ⊎ (g \ {q})) :=
          (fold_disjUnion fun x y z => Qp.add_left_comm y x z).symm
      _ = fold Qp.add q' g :=
          congrArg (fold Qp.add q') (disjUnion_singleton_difference Hmem).symm
      _ = 1 := Hsum
  imodintro
  wp_pures
  iapply Hφ
  itrivial

@[rocq_alias heap_lang.try_acquire_writer_spec]
theorem tryAcquireWriter_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ }} hl(&tryAcquireWriter &lk)
    {{ (b : Bool), RET hl_val(#b);
       if b then iprop(writerLocked γ ∗ Φ 1) else iprop(True) }} := by
  unfold isRwLock
  iintro %φ ⟨#HΦdup, %l, %Heq, #Hlockinv⟩ Hφ
  subst Heq
  wp_rec
  wp_bind cmpXchg(_, _, _)
  iapply wp_atomic
  imod inv_acc $$ Hlockinv with ⟨G1, G2⟩
  · simp
  unfold rwStateInv
  imodintro
  icases G1 with ⟨%z, Hl, Hz⟩
  wp_cmpxchg with hsuc hfail
  · obtain rfl : z = 0 := by simpa using hsuc
    icases Hz with (⟨%Hneg, -⟩ | ⟨-, %q, %g, Hauth, %Hsize, %Hfold, HΦ⟩)
    · omega
    obtain rfl : g = ∅ := size_eq_zero_iff.mp (by simpa using Hsize)
    rw [fold_empty] at Hfold
    subst Hfold
    icases (own_auth_empty_split γ).mpr $$ Hauth with ⟨Hauth, Hgive⟩
    imod G2 $$ [Hl Hauth]
    · iexists (-1)
      iframe Hl
      ileft
      iframe Hauth
      itrivial
    imodintro
    wp_pures
    iapply Hφ
    simp only [↓reduceIte]
    unfold writerLocked
    iframe Hgive HΦ
  · imod G2 $$ [Hl Hz]
    · iexists z
      iframe Hl Hz
    imodintro
    wp_pures
    iapply Hφ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

@[rocq_alias heap_lang.acquire_writer_spec]
theorem acquireWriter_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ }} hl(&acquireWriter &lk)
    {{ RET hl_val(#()); writerLocked γ ∗ Φ 1 }} := by
  iintro %φ #Hislock Hφ
  iloeb as IH
  wp_rec
  wp_bind &tryAcquireWriter _
  iapply tryAcquireWriter_spec $$ Hislock
  iintro !> %b Hb
  cases b
  · wp_pure
    iapply IH
    inext
    iexact Hφ
  · wp_pure
    imodintro
    simp only [↓reduceIte]
    iapply Hφ
    iframe Hb

@[rocq_alias heap_lang.release_writer_spec]
theorem releaseWriter_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ ∗ writerLocked γ ∗ Φ 1 }} hl(&releaseWriter &lk)
    {{ RET hl_val(#()); True }} := by
  unfold isRwLock writerLocked
  iintro %φ ⟨⟨#HΦdup, %l, %Heq, #Hlockinv⟩, Hlocked, HΦ⟩ Hφ
  subst Heq
  wp_rec
  iapply wp_atomic
  imod inv_acc $$ Hlockinv with ⟨G1, G2⟩
  · simp
  unfold rwStateInv
  imodintro
  icases G1 with ⟨%z, Hl, Hz⟩
  wp_store
  icases Hz with (⟨-, Hquarter⟩ | ⟨-, %q, %g, Hauth, -, -, -⟩)
  · ihave Hauth : iprop(own γ (● .ofSet (∅ : ReaderFracs))) $$ [Hquarter Hlocked]
    · iapply (own_auth_empty_split γ).mp
      iframe Hquarter Hlocked
    imod G2 $$ [Hl Hauth HΦ]
    · iexists (0 : Int)
      iframe Hl
      iright
      isplitl []
      · ipureintro
        omega
      iexists 1, (∅ : ReaderFracs)
      iframe Hauth HΦ
      isplitl []
      · ipureintro
        exact size_empty
      ipureintro
      exact fold_empty
    imodintro
    iapply Hφ
    itrivial
  · icombine Hauth Hlocked gives %Hvalid
    rw [Auth.auth_dfrac_op_valid, DFrac.op_own, DFrac.valid_own] at Hvalid
    grind

end proof

@[rocq_alias heap_lang.rw_spin_lock, implicit_reducible]
def instRwLock [HeapLangGS hlc GF] : RwLock GF where
  newlock := newlock
  acquireReader := acquireReader
  releaseReader := releaseReader
  acquireWriter := acquireWriter
  releaseWriter := releaseWriter
  rwlockG := RwSpinLockG
  name := GName
  isRwLock _ γ lk Φ := isRwLock γ lk Φ
  readerLocked _ γ q := readerLocked γ q
  writerLocked _ γ := writerLocked γ
  isRwLock_persistent γ lk Φ := instIsRwLockPersistent γ lk Φ
  isRwLock_iff γ lk Φ Ψ := isRwLock_iff γ lk Φ Ψ
  readerLocked_timeless γ q := instReaderLockedTimeless γ q
  writerLocked_timeless γ := instWriterLockedTimeless γ
  writerLocked_exclusive γ := writerLocked_exclusive γ
  writerLocked_not_readerLocked γ q := writerLocked_not_readerLocked γ q
  newlock_spec {_} Φ {P ioΦ ioq} [AsFractional P ioΦ Φ ioq 1] :=
    newlock_spec (ioΦ := ioΦ) (ioq := ioq) Φ
  acquireReader_spec γ lk Φ := acquireReader_spec γ lk Φ
  releaseReader_spec γ lk Φ q := releaseReader_spec γ lk Φ q
  acquireWriter_spec γ lk Φ := acquireWriter_spec γ lk Φ
  releaseWriter_spec γ lk Φ := releaseWriter_spec γ lk Φ

end RwSpinLock
end
