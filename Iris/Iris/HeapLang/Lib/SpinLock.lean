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

def newlock : Val := hl_val(
  λ _, ref(#false))
def tryAcquire : Val := hl_val(
  λ l, snd(cmpXchg(l, #false, #true)))
def acquire : Val := hl_val(
  rec acquire l :=
    if (?tryAcquire l)
      then #()
      else acquire l)
def release : Val := hl_val(
  λ l, l ← #false)

abbrev SpinLockG (GF : BundledGFunctors) := TokenG GF

def spinlockN : Namespace := ndot nroot "spinlock"

section Predicates

variable [HeapLangGS hlc GF] [SpinLockG GF]

def locked (γ : GName) : IProp GF := token γ

def lockInv (γ : GName) (l : Loc) (R : IProp GF) : IProp GF := iprop%
  ∃ b : Bool, (l ↦ some hl_val(#b)) ∗ (if b then True else locked γ ∗ R)

def isLock (γ : GName) (lk : Val) (R : IProp GF) : IProp GF := iprop%
  ∃ l : Loc, ⌜lk = Val.lit (.loc l)⌝ ∧ inv spinlockN (lockInv γ l R)

instance instIsLockPersistent (γ : GName) (lk : Val) (R : IProp GF) : Persistent (isLock γ lk R) := by
  unfold isLock; infer_instance

instance instLockedTimeless (γ : GName) : Timeless (locked (GF := GF) γ) := by
  unfold locked; infer_instance

theorem instLockedExclusive (γ : GName) : locked γ ∗ locked γ ⊢@{IProp GF} False :=
  token_exclusive γ

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

theorem newlock_spec :
  ⊢ □ ∀ (Φ : Val → IProp GF),
    (∀ (v : Val) (γ : GName), (∀ R E, R ={E}=∗ isLock γ v R) -∗ Φ v) -∗
    WP hl(?newlock #()) {{ Φ }} := by
  iintro !> %Φ Hcont
  wp_rec
  imod token_alloc with ⟨%γ, Hγ⟩
  iapply wp_alloc
  iintro !> %l Hpt
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

theorem try_acquire_spec (γ : GName) (lk : Val) (R : IProp GF) :
    ⊢ □ ∀ (Φ : Val → IProp GF),
    isLock γ lk R -∗
    (∀ (b : Bool), iprop(if b then locked γ ∗ R else iprop(True)) -∗ Φ hl_val(#b)) -∗
    WP hl(?tryAcquire ?lk) {{ Φ }} := by
  iintro !> %Φ #Hlock Hcont
  wp_rec
  unfold isLock
  icases Hlock with ⟨%l, %Heq, #Hinv⟩
  subst Heq
  wp_bind cmpXchg(_,_,_)
  iapply wp_atomic
  imod inv_acc $$ Hinv with ⟨G1, G2⟩
  · simp
  unfold lockInv
  imodintro
  icases G1 with ⟨%b, Hpt, Hcond⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply wp_wand $$ [Hpt]
    · iapply wp_cmpXchg_true rfl rfl $$ Hpt <;>
        simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
    iintro %v ⟨%Heq, Hpt⟩
    subst Heq
    imod G2 $$ [Hpt]
    · iexists true
      simp only [↓reduceIte]
      iframe
    · imodintro
      wp_pure
      imodintro
      iapply Hcont $$ [Hcond]
      simp only [↓reduceIte]
      iframe
  · simp only [↓reduceIte]
    iapply wp_wand $$ [Hpt]
    · iapply wp_cmpXchg_fail rfl rfl $$ Hpt <;>
        simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
    iintro %v ⟨%Heq, Hpt⟩
    subst Heq
    imod G2 $$ [Hpt]
    · iexists true
      simp only [↓reduceIte]
      iframe
    · imodintro
      wp_pure
      imodintro
      iapply Hcont
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial

theorem acquire_spec (γ : GName) (lk : Val) (R : IProp GF) :
  ⊢ □ ∀ (Φ : Val → IProp GF),
    isLock γ lk R -∗
    (locked γ ∗ R -∗ Φ hl_val(#())) -∗
    WP hl({acquire} {lk}) {{ Φ }} := by
  iintro !> %Φ #Hlock Hcont
  iloeb as IH
  wp_rec
  wp_bind ?tryAcquire _
  iapply try_acquire_spec $$ Hlock
  iintro %b Hpt
  cases b
  · wp_pure
    iapply IH
    iapply Hcont
  · wp_pure
    imodintro
    iapply Hcont
    simp only [if_pos]
    iframe

theorem release_spec (γ : GName) (lk : Val) (R : IProp GF) :
  ⊢ □ ∀ (Φ : Val → IProp GF),
    isLock γ lk R ∗ (locked γ ∗ R) -∗
    (True -∗ Φ hl_val(#())) -∗
    WP hl({release} {lk}) {{ Φ }} := by
  iintro !> %Φ ⟨#Hlock, ⟨Hl, HR⟩⟩ Hcont
  wp_rec
  unfold isLock
  icases Hlock with ⟨%l, %Heq, #Hinv⟩
  subst Heq
  iapply wp_atomic
  imod inv_acc $$ Hinv with ⟨G1, G2⟩
  · simp
  unfold lockInv
  imodintro
  icases G1 with ⟨%b, Hpt, Hcond⟩
  iapply wp_store $$ Hpt
  iintro !> Hpt
  imod G2 $$ [- Hcont]
  · inext
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  · imodintro
    iapply Hcont
    itrivial

end Specs

@[implicit_reducible]
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
