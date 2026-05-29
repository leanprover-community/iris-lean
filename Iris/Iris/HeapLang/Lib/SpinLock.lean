module

public import Iris.HeapLang.Lib.Lock
public import Iris.Instances.Lib.Token
public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces
public import Iris.HeapLang.PrimitiveLaws

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

variable [HeapLangGS hlc GF] [SpinLockG GF]

def locked (γ : GName) : IProp GF := token γ

def lock_inv (γ : GName) (l : Loc) (R : IProp GF) : IProp GF :=
  iprop(∃ b : Bool, (l ↦ Option.some hl_val(#b)) ∗ (if b then True else token γ ∗ R))

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
  iintro ⟨%l, %H1, #H2⟩ Heq
  iexists l
  isplit; itrivial
  iapply inv_iff $$ H2
  inext; icases Heq with #Heq; imodintro
  isplit
  · iintro ⟨%b, H1, H3⟩
    iexists b; iframe H1
    split; itrivial
    icases H3 with ⟨$, H3⟩
    iapply Heq $$ H3
  · iintro ⟨%b, H1, H3⟩
    iexists b; iframe H1
    split; itrivial
    icases H3 with ⟨$, H3⟩
    iapply Heq $$ H3

end SpinLockPredicates

section SpinLockSpecs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF]

theorem spinlock_newlock_spec :
  ⊢ □ ∀ (Φ : Val → IProp GF),
    (∀ (v : Val) (γ : GName), (∀ R E, R ={E}=∗ is_lock γ v R) -∗ Φ v)
    -∗ WP hl({spinlock_newlock} #()) {{ Φ }} := by
  unfold spinlock_newlock
  imodintro
  iintro %Φ Hcont
  iapply wp_rec; simp only [Exp.subst]
  inext
  imod token_alloc with ⟨%γ, Hγ⟩
  iapply wp_wand (Φ := fun v => iprop(∃ l', ⌜v = hl_val(#(BaseLit.loc l'))⌝ ∗ l' ↦ some hl_val(#false)))
  · iapply wp_alloc
  iintro %v ⟨%l, %Heq, Hpt⟩
  iapply Hcont $$ %v %γ
  iintro %R %E HR
  imod inv_alloc spinlockN E iprop(∃ b, (l ↦ some hl_val(#(BaseLit.bool b))) ∗ if b = true then True else token γ ∗ R) $$ [Hpt HR Hγ]
  · iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    inext; iframe
  · subst Heq
    imodintro
    unfold is_lock
    iexists l
    isplit; itrivial
    unfold lock_inv
    iframe

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
def spinLock [HeapLangGS hlc GF] : lock GF where
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
