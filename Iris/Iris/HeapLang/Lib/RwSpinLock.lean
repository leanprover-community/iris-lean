/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Auth
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

@[rocq_alias heap_lang.rw_spin_lock.newlock]
def newlock : Val := hl_val%
  λ _, ref(#0)

@[rocq_alias heap_lang.try_acquire_reader]
def tryAcquireReader : Val := hl_val%
  λ l,
    let n := !l;
    if #0 ≤ n
      then cas(l, n, n + #1)
      else #false

@[rocq_alias heap_lang.acquire_reader]
def acquireReader : Val := hl_val%
  rec acquire l :=
    if (&tryAcquireReader l)
      then #()
      else acquire l

@[rocq_alias heap_lang.release_reader]
def releaseReader : Val := hl_val%
  λ l, faa(l, #(-1 : Int)); #()

@[rocq_alias heap_lang.try_acquire_writer]
def tryAcquireWriter : Val := hl_val%
  λ l, cas(l, #0, #(-1 : Int))

@[rocq_alias heap_lang.acquire_writer]
def acquireWriter : Val := hl_val%
  rec acquire l :=
    if (&tryAcquireWriter l)
      then #()
      else acquire l

@[rocq_alias heap_lang.release_writer]
def releaseWriter : Val := hl_val%
  λ l, l ← #0

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

abbrev own (γ : GName) (a : Auth (LeibnizMultiSet ReaderFracs)) : IProp GF :=
  iOwn (F := RwSpinLockF) γ a

/-- The quarter kept while write-locked contradicts `readerLocked`; `writerLocked` owns the rest. -/
@[rocq_alias heap_lang.rw_state_inv]
abbrev rwStateInv (γ : GName) (l : Loc) (Φ : Qp → IProp GF) : IProp GF := iprop%
  ∃ z : Int, l ↦ some hl_val(#z) ∗
    (⌜z = -1⌝ ∗ own γ (●{.own Qp.quarter} (.ofSet ∅))
     ∨ ⌜0 ≤ z⌝ ∗ ∃ (q : Qp) (g : ReaderFracs),
         own γ (● .ofSet g) ∗
         ⌜size g = z.toNat⌝ ∗
         ⌜fold Qp.add q g = 1⌝ ∗
         Φ q)

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

/-! ## Ghost-state lemmas for the reader set -/

@[rocq_alias heap_lang.auth_valid_gmultiset_singleton]
theorem auth_valid_singleton {dq : DFrac} {v : Qp} {g : ReaderFracs}
    (h : ✓ ((●{dq} .ofSet g : Auth (LeibnizMultiSet ReaderFracs)) •
      ◯ LeibnizMultiSet.ofSet {v})) : v ∈ g :=
  singleton_subset_iff.mp (included_iff_subset.mp (Auth.both_dfrac_valid_discrete.mp h).2.1)

@[rocq_alias heap_lang.own_auth_gmultiset_singleton_2]
theorem own_auth_singleton_2 {γ : GName} {dq : DFrac} {v : Qp} {g : ReaderFracs} :
    own (GF := GF) γ (●{dq} .ofSet g) ∗ own γ (◯ .ofSet {v}) ⊢ ⌜v ∈ g⌝ := by
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureintro
  exact auth_valid_singleton Hvalid

private theorem own_auth_auth_False {γ : GName} {q₁ q₂ : Qp} {g₁ g₂ : ReaderFracs}
    (h : ¬ (q₁ + q₂).val ≤ 1) :
    own γ (●{.own q₁} .ofSet g₁) ∗ own γ (●{.own q₂} .ofSet g₂) ⊢@{IProp GF} False := by
  iintro ⟨H₁, H₂⟩
  icombine H₁ H₂ gives %Hvalid
  rw [Auth.auth_dfrac_op_valid, DFrac.op_own, DFrac.valid_own] at Hvalid
  grind

/-! ## Re-establishing the lock invariant -/

private theorem rwStateInv_readLocked {γ : GName} {l : Loc} {Φ : Qp → IProp GF} {z : Int} {q : Qp}
    {g : ReaderFracs} (hz : 0 ≤ z) (hsize : size g = z.toNat) (hfold : fold Qp.add q g = 1) :
    l ↦ some hl_val(#z) ∗ own γ (● .ofSet g) ∗ Φ q ⊢ rwStateInv γ l Φ := by
  unfold rwStateInv
  iintro ⟨Hl, Hauth, HΦ⟩
  iexists z; iframe Hl
  iright; iframe %hz
  iexists q, g; iframe ∗ %

private theorem rwStateInv_unlocked {γ : GName} {l : Loc} {Φ : Qp → IProp GF} :
    l ↦ some hl_val(#(0 : Int)) ∗ own γ (● .ofSet (∅ : ReaderFracs)) ∗ Φ 1
    ⊢ rwStateInv γ l Φ :=
  rwStateInv_readLocked (by omega) (by rw [size_empty]; rfl) fold_empty

private theorem rwStateInv_mono {γ : GName} {l : Loc} (Φ Ψ : Qp → IProp GF) :
    (∀ q, Φ q -∗ Ψ q) ⊢ rwStateInv γ l Φ -∗ rwStateInv γ l Ψ := by
  unfold rwStateInv
  iintro Hmono ⟨%z, Hl, (Hneg | ⟨Hge, %q, %g, Hauth, Hsize, Hfold, HΦ⟩)⟩
  · iexists z; iframe Hl Hneg
  iexists z; iframe Hl
  iright; iframe Hge
  iexists q, g; iframe Hauth Hsize Hfold
  iapply Hmono $$ HΦ

@[rocq_alias heap_lang.writer_locked_exclusive]
theorem writerLocked_exclusive (γ : GName) :
    writerLocked γ ∗ writerLocked γ ⊢@{IProp GF} False :=
  own_auth_auth_False (by grind)

@[rocq_alias heap_lang.writer_locked_not_reader_locked]
theorem writerLocked_not_readerLocked (γ : GName) (q : Qp) :
    writerLocked γ ∗ readerLocked γ q ⊢@{IProp GF} False := by
  iintro H
  unfold writerLocked readerLocked
  ihave %Hmem := own_auth_singleton_2 $$ H
  simp at Hmem

@[rocq_alias heap_lang.is_rw_lock_iff]
theorem isRwLock_iff (γ : GName) (lk : Val) (Φ Ψ : Qp → IProp GF) :
    isRwLock γ lk Φ ⊢ (▷ □ ∀ q, Φ q ∗-∗ Ψ q) -∗ isRwLock γ lk Ψ := by
  unfold isRwLock
  iintro ⟨#HΦdup, %l, %Heq, #Hlockinv⟩ #Hiff
  subst Heq
  isplit
  · inext; iapply internalFractional_iff $$ Hiff HΦdup
  iexists l
  isplit; itrivial
  iapply inv_iff $$ Hlockinv
  inext
  imodintro
  isplit
  · iintro Hinv
    iapply rwStateInv_mono $$ [] Hinv
    iintro %q HΦ; iapply Hiff $$ HΦ
  · iintro Hinv
    iapply rwStateInv_mono $$ [] Hinv
    iintro %q HΨ; iapply Hiff $$ HΨ

@[rocq_alias heap_lang.rw_spin_lock.newlock_spec]
theorem newlock_spec (Φ : Qp → IProp GF) {P : IProp GF} {ioΦ ioq}
    [hP : AsFractional P ioΦ Φ ioq 1] :
    {{ P }} hl(&newlock #()) {{ lk γ, RET lk; isRwLock γ lk Φ }} := by
  iintro %φ HP Hφ
  wp_lam
  imod iOwn_alloc (F := RwSpinLockF) (● .ofSet ∅) with ⟨%γ, Hγ⟩
  · exact Auth.auth_valid.mpr trivial
  wp_alloc l with Hl
  imod inv_alloc rwLockN ⊤ (rwStateInv γ l Φ) $$ [- Hφ] with #Hinv
  · iapply rwStateInv_unlocked
    iframe
    iapply hP.as_fractional.mp $$ HP
  iapply Hφ
  unfold isRwLock
  isplitl
  · iapply fractional_internalFractional hP.as_fractional_fractional
  iexists l; iframe Hinv; itrivial

@[rocq_alias heap_lang.try_acquire_reader_spec]
theorem tryAcquireReader_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ }} hl(&tryAcquireReader &lk)
    {{ (b : Bool), RET hl_val(#b);
       if b then iprop(∃ q, readerLocked γ q ∗ Φ q) else iprop(True) }} := by
  unfold isRwLock internalFractional readerLocked rwStateInv
  iintro %φ ⟨#HΦdup, %l, %Heq, #Hlockinv⟩ Hφ
  subst Heq
  wp_lam
  wp_bind !_
  iinv Hlockinv with ⟨%z, >Hl, Hz⟩ Hclose
  wp_load
  imod Hclose $$ [$Hl $Hz] with -
  imodintro
  wp_pures
  by_cases hle : (0 : Int) ≤ z
  case neg =>
    rw [decide_eq_false hle]
    wp_pures
    iapply Hφ
    simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  rw [decide_eq_true hle]
  wp_pures
  wp_bind cmpXchg(_, _, _)
  iinv Hlockinv with ⟨%z', >Hl, Hz⟩ Hclose
  wp_cmpxchg with hsuc hfail
  · obtain rfl : z = z' := by simpa using hsuc.symm
    icases Hz with (⟨%Hneg, -⟩ | ⟨-, %q, %g, Hauth, %Hsize, %Hfold, HΦ⟩)
    · omega
    ieval (rewrite [← Qp.half_add_half q]) at HΦ
    icases HΦdup $$ %q.half %q.half HΦ with ⟨HΦ, HΦgive⟩
    imod iOwn_update
      (a' := ((● LeibnizMultiSet.ofSet (g ⊎ {q.half})) •
        ◯ LeibnizMultiSet.ofSet {q.half} : Auth (LeibnizMultiSet ReaderFracs))) $$ Hauth with
      ⟨Hauth, Hview⟩
    · refine Auth.auth_update_alloc ?_
      have h := localUpdate_alloc (X := g) (Y := (∅ : ReaderFracs)) (X' := {q.half})
      rwa [disjUnion_empty_left] at h
    imod Hclose $$ [Hl Hauth HΦ] with -
    · iapply rwStateInv_readLocked (by omega) $$ [$]
      · rw [size_disjUnion, size_singleton, Hsize]; omega
      · rwa [fold_disjUnion (f := Qp.add) fun x y z => Qp.add_left_comm y x z, fold_singleton,
          show Qp.add q.half q.half = q from Qp.half_add_half q]
    imodintro
    wp_pures
    iapply Hφ; simp only [↓reduceIte]
    iexists q.half; iframe
  · imod Hclose $$ [$Hl $Hz] with -
    imodintro
    wp_pures
    iapply Hφ
    simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

@[rocq_alias heap_lang.acquire_reader_spec]
theorem acquireReader_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ }} hl(&acquireReader &lk)
    {{ q, RET hl_val(#()); readerLocked γ q ∗ Φ q }} := by
  iintro %φ #Hislock Hφ
  iloeb as IH
  wp_rec
  wp_apply tryAcquireReader_spec $$ Hislock with %b Hb
  cases b
  · wp_if_false
    iapply IH
    iframe
  · wp_if_true
    imodintro
    simp only [↓reduceIte]
    icases Hb with ⟨%q, Hlocked, HΦ⟩
    iapply Hφ $$ %q
    iframe

@[rocq_alias heap_lang.release_reader_spec]
theorem releaseReader_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) (q : Qp) :
    {{ isRwLock γ lk Φ ∗ readerLocked γ q ∗ Φ q }} hl(&releaseReader &lk)
    {{ RET hl_val(#()); True }} := by
  unfold isRwLock internalFractional readerLocked rwStateInv
  iintro %φ ⟨⟨#HΦdup, %l, %Heq, #Hlockinv⟩, Hlocked, HΦ⟩ Hφ
  subst Heq
  wp_lam
  wp_bind faa(_, _)
  iinv Hlockinv with ⟨%z, Hl, Hz⟩ Hclose
  wp_faa
  icases Hz with (⟨-, Hempty⟩ | ⟨%Hge, %q', %g, Hauth, %Hsize, %Hsum, HΦq'⟩)
  · iexfalso
    ihave %Hmem := own_auth_singleton_2 $$ [$]
    simp at Hmem
  ihave %Hmem := own_auth_singleton_2 $$ [$Hauth $Hlocked]
  icombine Hauth Hlocked as Hown
  imod iOwn_update (F := RwSpinLockF) (a' := ● .ofSet (g \ {q})) $$ Hown with Hown
  · refine Auth.auth_update_dealloc ?_
    have h := localUpdate_dealloc (X := g) (X' := {q}) subset_refl
    rwa [difference_self] at h
  imod Hclose $$ [-Hφ] with -
  · inext
    ispecialize HΦdup $$ %q %q' [$HΦ $HΦq']
    iapply rwStateInv_readLocked $$ [$]
    · have : size g ≠ 0 := fun h => by simp [size_eq_zero_iff.mp h] at Hmem
      omega
    · rw [size_difference (singleton_subset_iff.mpr Hmem), size_singleton, Hsize]; omega
    · calc fold Qp.add (Qp.add q q') (g \ {q}) = Qp.add q (fold Qp.add q' (g \ {q})) :=
          fold_comm_acc fun x y => Qp.add_left_comm x q y
      _ = fold Qp.add (fold Qp.add q' (g \ {q})) {q} := fold_singleton.symm
      _ = fold Qp.add q' ({q} ⊎ (g \ {q})) :=
          (fold_disjUnion fun x y z => Qp.add_left_comm y x z).symm
      _ = fold Qp.add q' g :=
          congrArg _ (disjUnion_singleton_difference Hmem).symm
      _ = 1 := Hsum
  imodintro
  wp_pures
  iapply Hφ; itrivial

@[rocq_alias heap_lang.try_acquire_writer_spec]
theorem tryAcquireWriter_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ }} hl(&tryAcquireWriter &lk)
    {{ (b : Bool), RET hl_val(#b); if b then (writerLocked γ ∗ Φ 1) else True }} := by
  unfold isRwLock writerLocked rwStateInv
  iintro %φ ⟨#HΦdup, %l, %Heq, #Hlockinv⟩ Hφ
  subst Heq
  wp_lam
  wp_bind cmpXchg(_, _, _)
  iinv Hlockinv with ⟨%z, >Hl, Hz⟩ Hclose
  wp_cmpxchg with hsuc hfail
  · obtain rfl : z = 0 := by simpa using hsuc
    icases Hz with (⟨%Hneg, -⟩ | ⟨-, %q, %g, Hauth, %Hsize, %Hfold, HΦ⟩)
    · omega
    obtain rfl : g = ∅ := size_eq_zero_iff.mp (by simpa using Hsize)
    rw [fold_empty] at Hfold
    subst Hfold
    ieval (rewrite [← Qp.quarter_add_threeQuarters, ← Frac.op_eq]) at Hauth
    -- FIXME: Frac.op_eq should not be needed
    icases Hauth with ⟨Hauth, Hgive⟩
    imod Hclose $$ [Hl Hauth] with -
    · inext
      iexists (-1); iframe Hl
      ileft; iframe; itrivial
    imodintro
    wp_pures
    iapply Hφ; simp only [↓reduceIte]
    iframe Hgive HΦ
  · imod Hclose $$ [$Hl $Hz] with -
    imodintro
    wp_pures
    iapply Hφ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

@[rocq_alias heap_lang.acquire_writer_spec]
theorem acquireWriter_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ }} hl(&acquireWriter &lk)
    {{ RET hl_val(#()); writerLocked γ ∗ Φ 1 }} := by
  iintro %φ #Hislock Hφ
  iloeb as IH
  wp_rec
  wp_apply tryAcquireWriter_spec $$ Hislock with %b Hb
  cases b
  · wp_if_false; iapply IH; itrivial
  · wp_if_true; iapply Hφ;
    simp only [↓reduceIte]; iframe Hb

@[rocq_alias heap_lang.release_writer_spec]
theorem releaseWriter_spec (γ : GName) (lk : Val) (Φ : Qp → IProp GF) :
    {{ isRwLock γ lk Φ ∗ writerLocked γ ∗ Φ 1 }} hl(&releaseWriter &lk)
    {{ RET hl_val(#()); True }} := by
  unfold isRwLock writerLocked rwStateInv
  iintro %φ ⟨⟨#HΦdup, %l, %Heq, #Hlockinv⟩, Hlocked, HΦ⟩ Hφ
  subst Heq
  wp_lam
  iinv Hlockinv with ⟨%z, >Hl, Hz⟩ Hclose
  wp_store
  icases Hz with (⟨-, Hquarter⟩ | ⟨-, %-, %-, Hauth, -⟩)
  · icombine Hquarter Hlocked as Hown
    imod Hclose $$ [Hl Hown HΦ] with -
    · iapply rwStateInv_unlocked; iframe
    iapply Hφ; itrivial
  · iexfalso; iapply own_auth_auth_False (q₁ := 1) (by grind) $$ [$Hauth $Hlocked]

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
