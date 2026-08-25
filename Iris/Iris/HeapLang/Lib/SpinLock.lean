/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Fernando Leal, Klaus Kraßnitzer
-/
module

public import Iris.HeapLang.Lib.Lock
public import Iris.Instances.Lib.Token
public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace SpinLock

@[rocq_alias heap_lang.spin_lock.newlock]
def newlock : Val := hl_val(
  λ _, ref(#false))
@[rocq_alias heap_lang.try_acquire]
def tryAcquire : Val := hl_val(
  λ l, snd(cmpXchg(l, #false, #true)))
@[rocq_alias heap_lang.spin_lock.acquire]
def acquire : Val := hl_val(
  rec acquire l :=
    if (&tryAcquire l)
      then #()
      else acquire l)
@[rocq_alias heap_lang.spin_lock.release]
def release : Val := hl_val(
  λ l, l ← #false)

@[rocq_alias heap_lang.spin_lockG]
abbrev SpinLockG (GF : BundledGFunctors) := TokenG GF

#rocq_ignore heap_lang.«spin_lockΣ» "Superseded by the `SpinLockG` typeclass on `BundledGFunctors`."
#rocq_ignore heap_lang.«subG_spin_lockΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

def spinlockN : Namespace := ndot nroot "spinlock"

section Predicates

variable [HeapLangGS hlc GF] [SpinLockG GF]

@[rocq_alias heap_lang.spin_lock.locked]
def locked (γ : GName) : IProp GF := token γ

@[rocq_alias heap_lang.spin_lock.lock_inv]
def lockInv (γ : GName) (l : Loc) (R : IProp GF) : IProp GF := iprop%
  ∃ b : Bool, (l ↦ some hl_val(#b)) ∗ (if b then True else locked γ ∗ R)

@[rocq_alias heap_lang.spin_lock.is_lock]
def isLock (γ : GName) (lk : Val) (R : IProp GF) : IProp GF := iprop%
  ∃ l : Loc, ⌜lk = Val.lit (.loc l)⌝ ∧ inv spinlockN (lockInv γ l R)

instance instIsLockPersistent (γ : GName) (lk : Val) (R : IProp GF) : Persistent (isLock γ lk R) := by
  unfold isLock; infer_instance

instance instLockedTimeless (γ : GName) : Timeless (locked (GF := GF) γ) := by
  unfold locked; infer_instance

@[rocq_alias heap_lang.spin_lock.locked_exclusive]
theorem instLockedExclusive (γ : GName) : locked γ ∗ locked γ ⊢@{IProp GF} False :=
  token_exclusive γ

@[rocq_alias heap_lang.spin_lock.is_lock_iff]
theorem is_lock_iff (γ : GName) (lk : Val) (R₁ R₂ : IProp GF) :
    isLock γ lk R₁ ⊢ (▷ □ (R₁ ∗-∗ R₂)) -∗ isLock γ lk R₂ := by
  unfold isLock lockInv
  iintro ⟨%l, %H1, #H2⟩ #Heq
  iexists l
  isplit; itrivial
  iapply inv_iff $$ H2
  inext; imodintro
  isplit
  · iintro ⟨%b, H1, H3⟩
    iexists _; iframe H1
    split; itrivial
    icases H3 with ⟨$, H3⟩
    iapply Heq $$ H3
  · iintro ⟨%b, H1, H3⟩
    iexists _; iframe H1
    split; itrivial
    icases H3 with ⟨$, H3⟩
    iapply Heq $$ H3

end Predicates

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF]

@[rocq_alias heap_lang.spin_lock.newlock_spec_delay_init]
theorem newlock_spec :
    {{ True }} hl(&newlock #())
    {{ v γ, RET v; ∀ R E, R ={E}=∗ isLock (GF := GF) γ v R }} := by
  iintro %Φ - Hcont
  wp_rec
  imod token_alloc with ⟨%γ, Hγ⟩
  wp_alloc l with Hpt
  imodintro
  iapply Hcont
  iintro %R %E HR
  imod inv_alloc spinlockN E (lockInv γ l R) $$ [Hpt HR Hγ] with H
  · unfold lockInv locked
    iexists false; simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  imodintro
  unfold isLock
  iexists l
  iframe
  itrivial

@[rocq_alias heap_lang.try_acquire_spec]
theorem try_acquire_spec (γ : GName) (lk : Val) (R : IProp GF) :
    {{ isLock γ lk R }} hl(&tryAcquire &lk)
    {{ (b : Bool), RET hl_val(#b); if b then locked γ ∗ R else True }} := by
  iintro %Φ #Hlock Hcont
  wp_rec
  unfold isLock
  icases Hlock with ⟨%l, %Heq, #Hinv⟩
  subst Heq
  wp_bind cmpXchg(_,_,_)
  iinv Hinv with G1
  unfold lockInv
  icases G1 with ⟨%b, Hpt, Hcond⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_cmpxchg_suc
    imodintro
    isplitl [Hpt]
    · iframe; simp; itrivial
    wp_pures
    imodintro
    iapply Hcont $$ [Hcond]
    simp only [↓reduceIte]; iframe
  · simp only [↓reduceIte]
    wp_cmpxchg_fail
    imodintro
    isplitl [Hpt]
    · iframe; simp; itrivial
    wp_pures
    imodintro
    iapply Hcont $$ [Hcond]
    simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

@[rocq_alias heap_lang.spin_lock.acquire_spec]
theorem acquire_spec (γ : GName) (lk : Val) (R : IProp GF) :
    {{ isLock γ lk R }} hl(&acquire &lk) {{ RET hl_val(#()); locked γ ∗ R }} := by
  iintro %Φ #Hlock Hcont
  iloeb as IH
  wp_rec
  wp_apply try_acquire_spec $$ Hlock with %b Hpt
  cases b
  · wp_pure
    iapply IH
    iapply Hcont
  · wp_pure
    imodintro
    iapply Hcont
    simp only [if_pos]
    iframe

@[rocq_alias heap_lang.spin_lock.release_spec]
theorem release_spec (γ : GName) (lk : Val) (R : IProp GF) :
    {{ isLock γ lk R ∗ locked γ ∗ R }} hl(&release &lk) {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hlock, Hl, HR⟩ Hcont
  wp_rec
  unfold isLock
  icases Hlock with ⟨%l, %Heq, #Hinv⟩
  subst Heq
  iinv Hinv with G1
  unfold lockInv
  icases G1 with ⟨%b, Hpt, Hcond⟩
  wp_store
  imodintro; iframe Hpt
  simp only [Bool.false_eq_true, ↓reduceIte]; iframe
  iapply Hcont; itrivial

end Specs

@[implicit_reducible, rocq_alias heap_lang.spin_lock]
def instLock [HeapLangGS hlc GF] : Lock GF where
  newlock := newlock
  acquire := acquire
  release := release
  lockG   := SpinLockG
  name := GName
  isLock _ γ lk R  := isLock γ lk R
  locked _ γ := locked γ
  isLock_persistent γ lk R := instIsLockPersistent γ lk R
  isLock_iff γ lk R₁ R₂ := is_lock_iff γ lk R₁ R₂
  locked_timeless γ := instLockedTimeless γ
  locked_exclusive γ := instLockedExclusive γ
  newlock_spec_delay_init := newlock_spec
  acquire_spec γ lk R := acquire_spec γ lk R
  release_spec γ lk R := release_spec γ lk R

end SpinLock
end
