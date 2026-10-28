/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.Lib.Lock
public import Iris.HeapLang.ProofMode
public import Iris.Instances.Lib.GhostVar
public import Iris.ProgramLogic.Atomic

@[expose] public section

namespace Iris.HeapLang

open BI DFrac ProofMode ProgramLogic Std

/-! # A TaDA-style logically atomic specification for a lock

Derived for an arbitrary implementation of the lock interface. The opposite direction could also
be derived rather easily (modulo a later in the `acquire` postcondition or a restriction to
timeless lock invariants), as shown in the TaDA paper.

In essence, this is an instance of the general fact that 'invariant-based' ("HoCAP-style")
logically atomic specifications are equivalent to TaDA-style logically atomic specifications; see
<https://gitlab.mpi-sws.org/iris/examples/blob/master/theories/logatom/elimination_stack/hocap_spec.v>
for that being worked out and explained in more detail for a stack specification. -/

/-- Whether a lock is currently held. Rocq calls this `state`; here `State` is already the
heap-state type. -/
@[rocq_alias heap_lang.state]
inductive LockState where
  | free
  | locked

@[rocq_alias heap_lang.alockG]
class ALockG (GF : BundledGFunctors) where
  [ghostVarG : GhostVarG GF LockState]

attribute [reducible, instance] ALockG.ghostVarG

#rocq_ignore heap_lang.«alockΣ» "Superseded by the `ALockG` typeclass on `BundledGFunctors`."
#rocq_ignore heap_lang.«subG_alockΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

section Tada

/- Rocq names the lock instance and the lock value both `lk`. The instance is `L` here, so that
`lk` can stay the value, as in the Rocq statements.

Rocq assumes `heapGS`; like the lock interface itself, nothing here touches the heap, so the
weakest precondition only needs `IrisGS_gen`. -/
variable {hlc : HasLC} {GF : BundledGFunctors} [IrisGS_gen hlc Exp GF] [ALockG GF]
variable [L : Lock GF] (N : L.lockG GF)

@[rocq_alias heap_lang.tada_lock_name]
structure TadaLockName (L : Lock GF) where
  state : GName
  lock : L.name

@[rocq_alias heap_lang.tada_lock_state]
def tadaLockState (γ : TadaLockName L) (s : LockState) : IProp GF :=
  iprop((γ.state ↪VAR{.own Qp.threeQuarters} s) ∗
    (match s with
     | .locked => L.locked N γ.lock ∗ (γ.state ↪VAR{.own Qp.quarter} LockState.locked)
     | .free => True))

@[rocq_alias heap_lang.tada_is_lock]
def tadaIsLock (γ : TadaLockName L) (lk : Val) : IProp GF :=
  L.isLock N γ.lock lk iprop(γ.state ↪VAR{.own Qp.quarter} LockState.free)

@[rocq_alias heap_lang.tada_is_lock_persistent]
instance (γ : TadaLockName L) (lk : Val) : Persistent (tadaIsLock N γ lk) := by
  unfold tadaIsLock
  infer_instance

@[rocq_alias heap_lang.tada_lock_state_timeless]
instance (γ : TadaLockName L) (s : LockState) : Timeless (tadaLockState N γ s) := by
  unfold tadaLockState
  cases s <;> infer_instance

@[rocq_alias heap_lang.tada_lock_state_exclusive]
theorem tadaLockState_exclusive (γ : TadaLockName L) (s1 s2 : LockState) :
    tadaLockState N γ s1 ⊢ tadaLockState N γ s2 -∗ (False : IProp GF) := by
  iunfold tadaLockState
  iintro ⟨Hvar1, -⟩ ⟨Hvar2, -⟩
  icombine Hvar1 Hvar2 gives %⟨Hval, -⟩
  refine absurd Hval ?_
  simp only [op_own, valid_own]
  grind

@[rocq_alias heap_lang.newlock_tada_spec]
theorem newlock_tada_spec :
    {{ True }} hl(&(L.newlock) #())
    {{ v γ, RET v; tadaIsLock N γ v ∗ tadaLockState N γ LockState.free }} := by
  iintro %Φ _ HΦ
  imod ghost_var_alloc LockState.free with ⟨%γvar, Hvar⟩
  rw [show (1 : Qp) = Qp.threeQuarters + Qp.quarter from by grind]
  icases Hvar with ⟨Hvar1, Hvar2⟩
  iapply newlock_spec N iprop(γvar ↪VAR{.own Qp.quarter} LockState.free) $$ Hvar2
  inext
  iintro %lk %γlock Hlock
  iapply HΦ $$ %lk %(TadaLockName.mk γvar γlock)
  iunfold tadaIsLock, tadaLockState
  iframe Hlock Hvar1

@[rocq_alias heap_lang.acquire_tada_spec]
theorem acquire_tada_spec (γ : TadaLockName L) (lk : Val) :
    tadaIsLock N γ lk ⊢
    <<{ ∀∀ s, tadaLockState N γ s }>> hl(&(L.acquire) &lk) @ ∅
    <<{ ⌜s = LockState.free⌝ ∗ tadaLockState N γ LockState.locked | RET hl_val(#()) }>> := by
  iunfold atomic_wp
  iintro #Hislock %Φ AU
  iunfold tadaIsLock at Hislock
  iapply wp_fupd
  iapply L.acquire_spec $$ Hislock
  inext
  iintro ⟨Hlocked, Hvar1⟩
  imod AU with ⟨%⟨s, _⟩, Hα, ⟨-, Hclose⟩⟩
  isimp only [Tele.app] at Hα
  iunfold tadaLockState at Hα
  icases Hα with ⟨Hvar2, -⟩
  icombine Hvar1 Hvar2 gives %⟨-, rfl⟩
  imod ghost_var_update_2 LockState.locked _ _ _ _ _ (by grind)
    $$ Hvar1 Hvar2 with ⟨Hvar1, Hvar2⟩
  iunfold tadaLockState at Hclose
  isimp only [Tele.app] at Hclose
  imod Hclose $$ %Tele.Arg.nil [$Hvar2 $Hlocked $Hvar1 //]
  isimp only [Tele.bind, Tele.app] at Hclose
  iunfold BIBase.wandM at Hclose
  iapply Hclose $$ %Tele.Arg.nil

@[rocq_alias heap_lang.release_tada_spec]
theorem release_tada_spec (γ : TadaLockName L) (lk : Val) :
    tadaIsLock N γ lk ⊢
    <<{ tadaLockState N γ LockState.locked }>> hl(&(L.release) &lk) @ ∅
    <<{ tadaLockState N γ LockState.free | RET hl_val(#()) }>> := by
  iunfold atomic_wp
  iintro #Hislock %Φ AU
  iunfold tadaIsLock at Hislock
  iapply fupd_wp
  imod AU with ⟨%_, Hα, ⟨-, Hclose⟩⟩
  isimp only [Tele.app] at Hα
  iunfold tadaLockState at Hα
  icases Hα with ⟨Hvar1, Hlocked, Hvar2⟩
  imod ghost_var_update_2 LockState.free _ _ _ _ _ (by grind)
    $$ Hvar1 Hvar2 with ⟨Hvar1, Hvar2⟩
  iunfold tadaLockState at Hclose
  isimp only [Tele.app] at Hclose
  imod Hclose $$ %Tele.Arg.nil [$Hvar1]
  imodintro
  iapply L.release_spec γ.lock lk
    iprop(γ.state ↪VAR{.own Qp.quarter} LockState.free) $$ [$Hislock $Hlocked $Hvar2]
  inext
  iintro _
  isimp only [Tele.bind, Tele.app] at Hclose
  iunfold BIBase.wandM at Hclose
  iapply Hclose $$ %Tele.Arg.nil

end Tada

end Iris.HeapLang

end
