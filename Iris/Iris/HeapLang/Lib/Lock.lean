module

public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances

namespace Iris.HeapLang

open BI

@[expose] public section

@[rocq_alias heap_lang.lock]
class Lock (GF : BundledGFunctors) [IrisGS_gen hlc Exp GF] where
  newlock : Val
  acquire : Val
  release : Val

  lockG : BundledGFunctors → Type
  name : Type
  [lock_name_inhabited : Inhabited name]

  isLock : lockG GF → name → Val → IProp GF → IProp GF
  locked : lockG GF → name → IProp GF

  isLock_persistent {N} γ lk (R : IProp GF) : Persistent (isLock N γ lk R)
  isLock_iff {N} γ lk (R₁ R₂ : IProp GF) : isLock N γ lk R₁ ⊢ (▷ □ (R₁ ∗-∗ R₂)) -∗ isLock N γ lk R₂

  locked_timeless {N} γ : Timeless (locked N γ)
  locked_exclusive {N} γ : locked N γ ∗ locked N γ ⊢@{IProp GF} False

  newlock_spec_delay_init {N} :
    {{ True }} hl(&newlock #()) {{ v γ, RET v; ∀ R E, R ={E}=∗ isLock N γ v R }}
  acquire_spec {N} γ lk R :
    {{ isLock N γ lk R }} hl(&acquire &lk) {{ RET hl_val(#()); locked N γ ∗ R }}
  release_spec {N} γ lk R :
    {{ isLock N γ lk R ∗ locked N γ ∗ R }} hl(&release &lk) {{ RET hl_val(#()); True }}

instance instInhabitedLockName [IrisGS_gen hlc Exp GF] [lk : Lock GF] : Inhabited lk.name :=
  lk.lock_name_inhabited

section lemmas

variable [IrisGS_gen hlc Exp GF] [lk : Lock GF] (N : lk.lockG GF)

instance instPersistentLockIsLock  γ v R : Persistent (lk.isLock N γ v R) :=
  lk.isLock_persistent γ v R

instance instTimelessLockLocked  γ : Timeless (lk.locked N γ) :=
  lk.locked_timeless γ

@[rocq_alias heap_lang.is_lock_contractive]
theorem isLock_contractive γ v : OFE.Contractive (lk.isLock N γ v) := by
  rw [contractive_internalEq (PROP := IProp GF)]
  iintro %x₁ %x₂ #HEQ
  iapply prop_ext
  imodintro
  isplit
  · iintro #H
    iapply Lock.isLock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne h .rfl⟩
    · iapply equiv_wandIff; exact .rfl
  · iintro #H
    iapply Lock.isLock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne .rfl h⟩
    · iapply equiv_wandIff; exact .rfl

instance is_lock_ne γ v : OFE.NonExpansive (lk.isLock N γ v) :=
  letI _ := isLock_contractive N γ v
  OFE.ne_of_contractive _

#rocq_ignore heap_lang.is_lock_proper "OFE is Leibniz; use equality"

@[rocq_alias heap_lang.lock.newlock_spec]
theorem newlock_spec R :
    {{ R }} hl(&lk.newlock #()) {{ v γ, RET v; lk.isLock N γ v R }} := by
  iintro %Φ HR HΦ
  iapply wp_fupd
  iapply lk.newlock_spec_delay_init (N := N) $$ %(fun v => iprop(|={⊤}=> Φ v)) [//]
  inext
  iintro %v %γ Hinit
  imod Hinit $$ %R %⊤ HR
  iapply HΦ $$ Hinit

end lemmas

end
