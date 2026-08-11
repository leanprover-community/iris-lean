/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Lib.Fractional
public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances

namespace Iris.HeapLang

open BI OFE

@[expose] public section

/-- A general interface for a reader-writer lock. -/
@[rocq_alias heap_lang.rwlock]
structure RwLock (GF : BundledGFunctors) [IrisGS_gen hlc Exp GF] where
  -- Operations
  newlock : Val
  acquireReader : Val
  releaseReader : Val
  acquireWriter : Val
  releaseWriter : Val
  -- Ghost state
  rwlockG : BundledGFunctors → Type
  name : Type
  -- Predicates
  isRwLock : rwlockG GF → name → Val → (Qp → IProp GF) → IProp GF
  readerLocked : rwlockG GF → name → Qp → IProp GF
  writerLocked : rwlockG GF → name → IProp GF
  -- General properties of the predicates
  isRwLock_persistent {L} γ lk Φ : Persistent (isRwLock L γ lk Φ)
  isRwLock_iff {L} γ lk Φ Ψ : isRwLock L γ lk Φ ⊢ (▷ □ ∀ q, Φ q ∗-∗ Ψ q) -∗ isRwLock L γ lk Ψ
  readerLocked_timeless {L} γ q : Timeless (readerLocked L γ q)
  writerLocked_timeless {L} γ : Timeless (writerLocked L γ)
  writerLocked_exclusive {L} γ : writerLocked L γ ∗ writerLocked L γ ⊢@{IProp GF} False
  writerLocked_not_readerLocked {L} γ q :
    writerLocked L γ ∗ readerLocked L γ q ⊢@{IProp GF} False
  -- Program specs
  newlock_spec {L} (Φ : Qp → IProp GF) {P ioΦ ioq} [AsFractional P ioΦ Φ ioq 1] :
    {{ P }} hl(&newlock #()) {{ lk γ, RET lk; isRwLock L γ lk Φ }}
  acquireReader_spec {L} γ lk Φ :
    {{ isRwLock L γ lk Φ }} hl(&acquireReader &lk)
    {{ q, RET hl_val(#()); readerLocked L γ q ∗ Φ q }}
  releaseReader_spec {L} γ lk Φ q :
    {{ isRwLock L γ lk Φ ∗ readerLocked L γ q ∗ Φ q }} hl(&releaseReader &lk)
    {{ RET hl_val(#()); True }}
  acquireWriter_spec {L} γ lk Φ :
    {{ isRwLock L γ lk Φ }} hl(&acquireWriter &lk)
    {{ RET hl_val(#()); writerLocked L γ ∗ Φ 1 }}
  releaseWriter_spec {L} γ lk Φ :
    {{ isRwLock L γ lk Φ ∗ writerLocked L γ ∗ Φ 1 }} hl(&releaseWriter &lk)
    {{ RET hl_val(#()); True }}

section lemmas

variable [IrisGS_gen hlc Exp GF] (rw : RwLock GF) (L : rw.rwlockG GF)

instance instPersistentIsRwLock γ lk Φ : Persistent (rw.isRwLock L γ lk Φ) :=
  rw.isRwLock_persistent γ lk Φ

instance instTimelessReaderLocked γ q : Timeless (rw.readerLocked L γ q) :=
  rw.readerLocked_timeless γ q

instance instTimelessWriterLocked γ : Timeless (rw.writerLocked L γ) :=
  rw.writerLocked_timeless γ

@[rocq_alias heap_lang.is_rw_lock_contractive]
instance isRwLock_contractive γ lk : Contractive (rw.isRwLock L γ lk) := by
  rw [contractive_internalEq (PROP := IProp GF)]
  iintro %Φ₁ %Φ₂ #HEQ
  ihave #HΦ : iprop(▷ ∀ q, Φ₁ q ≡ Φ₂ q) $$ [HEQ]
  · iapply later_mono (discreteFun_equivI Φ₁ Φ₂).mp $$ [$]
  iapply prop_ext
  imodintro
  isplit
  · iintro #H
    iapply rw.isRwLock_iff $$ H
    iintro !> !> %q
    irewrite [HΦ $$ %q]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne h .rfl⟩
    · iapply equiv_wandIff; exact .rfl
  · iintro #H
    iapply rw.isRwLock_iff $$ H
    iintro !> !> %q
    irewrite [HΦ $$ %q]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne .rfl h⟩
    · iapply equiv_wandIff; exact .rfl

#rocq_ignore heap_lang.is_rw_lock_proper "OFE is Leibniz; use equality"

end lemmas

end
