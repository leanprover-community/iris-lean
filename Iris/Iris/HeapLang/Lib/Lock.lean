module

public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances

namespace Iris.HeapLang

open BI

@[expose] public section

class lock (GF : BundledGFunctors) [IrisGS_gen hlc Exp GF] where
  newlock : Val
  acquire : Val
  release : Val

  lockG : BundledGFunctors → Type
  name : Type
  [lock_name_inhabited : Inhabited name]

  is_lock : lockG GF → name → Val → IProp GF → IProp GF
  locked : lockG GF → name → IProp GF

  is_lock_persistent {N} γ lk (R : IProp GF) :
    Persistent (is_lock N γ lk R)
  is_lock_iff {N} γ lk (R₁ R₂ : IProp GF) :
    is_lock N γ lk R₁ ⊢ (▷ □ (R₁ ∗-∗ R₂)) -∗ is_lock N γ lk R₂

  locked_timeless {N} γ : Timeless (locked N γ)
  locked_exclusive {N} γ : locked N γ ∗ locked N γ ⊢@{IProp GF} False

  -- TODO: redo with texan triples
  newlock_spec_delay_init {N} :
    ⊢ □ ∀ (Φ : Val → IProp GF),
      (∀ (v : Val) (γ : name), (∀ R E, R ={E}=∗ is_lock N γ v R) -∗ Φ v)
      -∗ WP hl({newlock} #()) {{ Φ }}
  acquire_spec {N} γ lk R :
    ⊢ □ ∀ (Φ : Val → IProp GF),
    is_lock N γ lk R
    -∗ ((locked N γ ∗ R) -∗ Φ (.lit .unit))
    -∗ WP hl({acquire} {lk}) {{ Φ }}
  release_spec {N} γ lk R :
    ⊢ □ ∀ (Φ : Val → IProp GF),
    (is_lock N γ lk R ∗ locked N γ ∗ R)
    -∗ (True -∗ Φ (.lit .unit))
    -∗ WP hl({release} {lk}) {{ Φ }}

instance lock_name_inhabited [IrisGS_gen hlc Exp GF] [lk : lock GF] : Inhabited lk.name := lk.lock_name_inhabited

section lemmas

variable [IrisGS_gen hlc Exp GF] [lk : lock GF] (N : lk.lockG GF)

instance is_lock_persistent_inst γ v R :
    Persistent (lk.is_lock N γ v R) :=
  lk.is_lock_persistent γ v R

instance locked_timeless_inst γ :
    Timeless (lk.locked N γ) :=
  lk.locked_timeless γ

theorem is_lock_contractive γ v :
    OFE.Contractive (lk.is_lock N γ v) := by
  rw [contractive_internalEq (PROP := IProp GF)]
  iintro %x₁ %x₂ #HEQ
  iapply BI.prop_ext
  iintro !>
  isplit
  · iintro #H
    iapply lock.is_lock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne h .rfl⟩
    · iapply equiv_wandIff; exact .rfl
  · iintro #H
    iapply lock.is_lock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne .rfl h⟩
    · iapply equiv_wandIff; exact .rfl

instance is_lock_ne γ v :
    OFE.NonExpansive (lk.is_lock N γ v) :=
  letI := is_lock_contractive N γ v
  OFE.ne_of_contractive _

theorem newlock_spec R :
    ⊢ □ ∀ (Φ : Val → IProp GF),
    R
    -∗ (∀ (v : Val) (γ : lk.name), lk.is_lock N γ v R -∗ Φ v)
    -∗ WP hl({lk.newlock} #()) {{ Φ }} := by
  iintro %Φ !> HR HΦ
  iapply wp_fupd
  iapply lk.newlock_spec_delay_init $$ %(fun v => iprop(|={⊤}=> Φ v))
  iintro %v %γ Hinit
  imod Hinit $$ %R %⊤ HR
  imodintro
  iapply HΦ $$ Hinit

end lemmas

end
