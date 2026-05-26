module

public import Iris.HeapLang.Lib.Lock
public import Iris.Instances.Lib.Token
public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces

namespace Iris.HeapLang

open BI Iris

@[expose] public section

def spinlock_newlock : Val := hl_val(λ _, ref(#false))
def spinlock_try_acquire : Val := hl_val(λ l, cas(l, #false, #true))
def spinlock_acquire : Val :=
  hl_val(rec acquire l := if {spinlock_try_acquire} l then #() else acquire l)
def spinlock_release : Val := hl_val(λ l, l ← #false)

abbrev SpinLockG (GF : BundledGFunctors) := TokenG GF

def spinlockN : Namespace := ndot nroot "spinlock"

section SpinLockPredicates

variable [InvGS_gen hlc GF] [SpinLockG GF]

def locked (γ : GName) : IProp GF := token γ

def lock_inv (γ : GName) (l : Loc) (R : IProp GF) : IProp GF :=
  sorry

def is_lock (γ : GName) (lk : Val) (R : IProp GF) : IProp GF :=
  iprop(∃ l : Loc, ⌜lk = Val.lit (.loc l)⌝ ∧ inv spinlockN (lock_inv γ l R))

instance is_lock_persistent (γ : GName) (lk : Val) (R : IProp GF) :
    Persistent (is_lock γ lk R) := by
  unfold is_lock; infer_instance

instance locked_timeless (γ : GName) : Timeless (locked (GF := GF) γ) := by
  unfold locked; infer_instance

theorem locked_exclusive (γ : GName) :
    (locked γ ∗ locked γ) ⊢@{IProp GF} False :=
  token_exclusive γ

theorem is_lock_iff (γ : GName) (lk : Val) (R₁ R₂ : IProp GF) :
    is_lock γ lk R₁ ⊢ (▷ □ (R₁ ∗-∗ R₂)) -∗ is_lock γ lk R₂ := by
  unfold is_lock lock_inv
  sorry

end SpinLockPredicates

section SpinLockSpecs

variable {GF : BundledGFunctors} [IrisGS_gen hlc Exp GF] [SpinLockG GF]

theorem spinlock_newlock_spec :
  ⊢ □ ∀ (Φ : Val → IProp GF),
    (∀ (v : Val) (γ : GName), (∀ R E, R ={E}=∗ is_lock γ v R) -∗ Φ v)
    -∗ WP hl({spinlock_newlock} #()) {{ Φ }} := by
  sorry

theorem spinlock_try_acquire_spec (γ : GName) (lk : Val) (R : IProp GF) :
    ⊢ □ ∀ (Φ : Val → IProp GF),
    is_lock γ lk R
    -∗ (((locked γ ∗ R) -∗ Φ (.lit (.bool true))) ∧
     (True -∗ Φ (.lit (.bool false))))
    -∗ WP hl({spinlock_try_acquire} {lk}) {{ Φ }} := by
  sorry

theorem spinlock_acquire_spec (γ : GName) (lk : Val) (R : IProp GF) :
  ⊢ □ ∀ (Φ : Val → IProp GF),
    is_lock γ lk R
    -∗ ((locked γ ∗ R) -∗ Φ (.lit .unit))
    -∗ WP hl({spinlock_acquire} {lk}) {{ Φ }} := by
  sorry

theorem spinlock_release_spec (γ : GName) (lk : Val) (R : IProp GF) :
  ⊢ □ ∀ (Φ : Val → IProp GF),
    (is_lock γ lk R ∗ locked γ ∗ R)
    -∗ (True -∗ Φ (.lit .unit))
    -∗ WP hl({spinlock_release} {lk}) {{ Φ }} := by
  sorry

end SpinLockSpecs

@[implicit_reducible]
def spinLock [IrisGS_gen hlc Exp GF] : lock GF where
  newlock := spinlock_newlock
  acquire := spinlock_acquire
  release := spinlock_release
  lockG   := SpinLockG
  name := GName
  is_lock _ γ lk R  := is_lock γ lk R
  locked _ γ := locked γ
  is_lock_persistent γ lk R := is_lock_persistent γ lk R
  is_lock_iff γ lk R₁ R₂ := is_lock_iff γ lk R₁ R₂
  locked_timeless γ := locked_timeless γ
  locked_exclusive γ := locked_exclusive γ
  newlock_spec_delay_init Φ := spinlock_newlock_spec Φ
  acquire_spec γ lk R Φ := spinlock_acquire_spec γ lk R Φ
  release_spec γ lk R Φ := spinlock_release_spec γ lk R Φ

end
