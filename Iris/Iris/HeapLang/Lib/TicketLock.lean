/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.Excl
public import Iris.Algebra.LeibnizSet
public import Iris.HeapLang.Lib.Lock
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.Instances.Lib.Invariants
public import Iris.Std.GenSetsInstances
public import Iris.Std.Namespaces

namespace Iris.HeapLang

open BI Std CMRA Excl DisjointLeibnizSet LawfulSet

@[expose] public section

namespace TicketLock

@[rocq_alias heap_lang.wait_loop]
def waitLoop : Val := hl_val%
  rec waitLoop x lk :=
    let o := !fst(lk);
    if x = o
      then #()
      else waitLoop x lk

@[rocq_alias heap_lang.ticket_lock.newlock]
def newlock : Val := hl_val%
  λ _, (ref(#0), ref(#0))

@[rocq_alias heap_lang.ticket_lock.acquire]
def acquire : Val := hl_val%
  rec acquire lk :=
    let n := !snd(lk);
    if cas(snd(lk), n, n + #1)
      then &waitLoop n lk
      else acquire lk

@[rocq_alias heap_lang.ticket_lock.release]
def release : Val := hl_val%
  λ lk, fst(lk) ← !fst(lk) + #1

/-- Tickets are natural numbers, and the lock tracks a finite set of them. -/
abbrev Tickets := Std.ExtTreeSet Nat compare

/-- The ticket now being served, together with the set of tickets handed out so far. -/
abbrev TicketR := Auth (Option (Excl (DiscreteO Nat)) × DisjointLeibnizSet Tickets)

abbrev TicketLockF : COFE.OFunctorPre := constOF TicketR

@[rocq_alias heap_lang.tlockG]
class TicketLockG (GF : BundledGFunctors) where [elemG : ElemG GF TicketLockF]

attribute [reducible, instance] TicketLockG.elemG

#rocq_ignore heap_lang.«tlockΣ» "Superseded by the `TicketLockG` typeclass on `BundledGFunctors`."
#rocq_ignore heap_lang.«subG_tlockΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

section proof

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [TicketLockG GF]

def ticketLockN : Namespace := nroot .@ "ticket_lock"

abbrev own (γ : GName) (a : TicketR) : IProp GF := iOwn (F := TicketLockF) γ a

/-- The authority: ticket `o` is being served, and tickets `0, …, n - 1` have been handed out. -/
abbrev auth (o n : Nat) : TicketR := ● (some (excl ⟨o⟩), .valid (setSeq 0 n))

/-- The right to enter the critical section, held by whoever drew ticket `o`. -/
abbrev owner (o : Nat) : TicketR := ◯ (some (excl ⟨o⟩), ∅)

/-- Ticket `x` has been handed out. -/
abbrev ticket (x : Nat) : TicketR := ◯ (none, .valid {x})

@[rocq_alias heap_lang.ticket_lock.lock_inv]
def lockInv (γ : GName) (lo ln : Loc) (R : IProp GF) : IProp GF := iprop(
  ∃ o n : Nat,
    lo ↦ some hl_val(#o) ∗ ln ↦ some hl_val(#n) ∗ own γ (auth o n) ∗
    (own γ (owner o) ∗ R ∨ own γ (ticket o)))

@[rocq_alias heap_lang.ticket_lock.is_lock]
def isLock (γ : GName) (lk : Val) (R : IProp GF) : IProp GF := iprop(
  ∃ lo ln : Loc, ⌜lk = hl_val((#lo, #ln))⌝ ∗ inv ticketLockN (lockInv γ lo ln R))

@[rocq_alias heap_lang.issued]
def issued (γ : GName) (x : Nat) : IProp GF := own γ (ticket x)

@[rocq_alias heap_lang.ticket_lock.locked]
def locked (γ : GName) : IProp GF := iprop(∃ o : Nat, own γ (owner o))

instance instIsLockPersistent (γ : GName) (lk : Val) (R : IProp GF) :
    Persistent (isLock γ lk R) := by unfold isLock; infer_instance

instance instOwnerTimeless (γ : GName) (o : Nat) : Timeless (own (GF := GF) γ (owner o)) :=
  iOwn_timeless

instance instLockedTimeless (γ : GName) : Timeless (locked (GF := GF) γ) := by
  unfold locked; infer_instance

/-! ## Ghost-state lemmas -/

/-- Owning two fragments at once exposes the validity of their composition. -/
private theorem own_op_valid {γ : GName} {a₁ a₂ : TicketR} :
    own (GF := GF) γ a₁ ∗ own γ a₂ ⊢ ⌜✓ (a₁ • a₂)⌝ :=
  iOwn_cmraValid_op.trans (internalCmraValid_discrete (A := TicketR)).mp

/-- Only one thread at a time holds the right to enter the critical section. -/
private theorem own_owner_exclusive {γ : GName} {o₁ o₂ : Nat} :
    own (GF := GF) γ (owner o₁) ∗ own γ (owner o₂) ⊢ False :=
  pure_elim _ own_op_valid fun h => (Auth.frag_op_valid.mp h).1.elim

/-- A ticket is handed out at most once. -/
private theorem own_ticket_exclusive {γ : GName} {x : Nat} :
    own (GF := GF) γ (ticket x) ∗ own γ (ticket x) ⊢ False :=
  pure_elim _ own_op_valid fun h => (disjoint_singleton_left.mp
    (valid_op_iff_disj.mp (Auth.frag_op_valid.mp h).2) (mem_singleton.mpr rfl)).elim

/-- The authority agrees with the holder of the right to enter the critical section. -/
private theorem own_owner_agree {γ : GName} {o o' n : Nat} :
    own (GF := GF) γ (auth o n) ∗ own γ (owner o') ⊢ ⌜o' = o⌝ :=
  own_op_valid.trans (pure_mono fun h =>
    DiscreteO.eqv_inj (excl_included.mp (Prod.inc_def.mp (Auth.auth_both_valid_discrete.mp h).1).1))

@[rocq_alias heap_lang.ticket_lock.locked_exclusive]
theorem locked_exclusive (γ : GName) : locked γ ∗ locked γ ⊢@{IProp GF} False := by
  unfold locked
  iintro ⟨⟨%o₁, H₁⟩, ⟨%o₂, H₂⟩⟩
  iapply own_owner_exclusive $$ [$H₁ $H₂]

/-! ## The lock invariant -/

private theorem lockInv_mono {γ : GName} {lo ln : Loc} (R₁ R₂ : IProp GF) :
    (R₁ -∗ R₂) ⊢ lockInv γ lo ln R₁ -∗ lockInv γ lo ln R₂ := by
  unfold lockInv
  iintro HR ⟨%o, %n, Hlo, Hln, Hauth, Hstate⟩
  iexists o, n
  iframe Hlo Hln Hauth
  icases Hstate with (⟨Howner, HR₁⟩ | Hissued)
  · ileft; iframe Howner
    iapply HR $$ HR₁
  · iright; iframe Hissued

@[rocq_alias heap_lang.ticket_lock.is_lock_iff]
theorem isLock_iff (γ : GName) (lk : Val) (R₁ R₂ : IProp GF) :
    isLock γ lk R₁ ⊢ (▷ □ (R₁ ∗-∗ R₂)) -∗ isLock γ lk R₂ := by
  unfold isLock
  iintro ⟨%lo, %ln, %Heq, #Hinv⟩ #HR
  iexists lo, ln
  isplit; itrivial
  iapply inv_iff $$ Hinv
  inext; imodintro
  isplit
  · iintro Hlockinv
    iapply lockInv_mono $$ [] Hlockinv
    iintro HR₁; iapply HR $$ HR₁
  · iintro Hlockinv
    iapply lockInv_mono $$ [] Hlockinv
    iintro HR₂; iapply HR $$ HR₂

/-! ## Specifications -/

@[rocq_alias heap_lang.ticket_lock.newlock_spec_delay_init]
theorem newlock_spec :
    {{ True }} hl(&newlock #())
    {{ v γ, RET v; ∀ R E, R ={E}=∗ isLock (GF := GF) γ v R }} := by
  iintro %Φ - Hcont
  wp_rec
  wp_alloc ln with Hln
  wp_alloc lo with Hlo
  imod iOwn_alloc (F := TicketLockF) ((auth 0 0 : TicketR) • owner 0) with ⟨%γ, ⟨Hauth, Howner⟩⟩
  · exact Auth.auth_both_valid_2 ⟨trivial, trivial⟩ (inc_refl _)
  wp_pures
  imodintro
  iapply Hcont
  iintro %R %E HR
  imod inv_alloc ticketLockN E (lockInv γ lo ln R) $$ [Hlo Hln Hauth Howner HR] with #Hinv
  · unfold lockInv
    iexists 0, 0
    iframe Hlo Hln Hauth
    ileft; iframe Howner HR
  imodintro
  unfold isLock
  iexists lo, ln
  iframe Hinv
  itrivial

@[rocq_alias heap_lang.wait_loop_spec]
theorem waitLoop_spec (γ : GName) (lk : Val) (x : Nat) (R : IProp GF) :
    {{ isLock γ lk R ∗ issued γ x }} hl(&waitLoop #x &lk)
    {{ RET hl_val(#()); locked γ ∗ R }} := by
  unfold isLock issued locked lockInv
  iintro %Φ ⟨⟨%lo, %ln, %Heq, #Hinv⟩, Hissued⟩ HΦ
  subst Heq
  iloeb as IH
  wp_rec
  wp_pures
  wp_bind !_
  iinv Hinv with ⟨%o, %n, >Hlo, Hln, Hauth, Hstate⟩ Hclose
  wp_load
  by_cases hxo : x = o
  · subst hxo
    icases Hstate with (⟨Howner, HR⟩ | Hissued')
    · imod Hclose $$ [Hlo Hln Hauth Hissued] with -
      · iexists x, n
        iframe Hlo Hln Hauth
        iright; iframe Hissued
      imodintro
      wp_pures
      rw [beq_self_eq_true]
      wp_pures
      iapply HΦ
      imodintro
      iframe HR
      iexists x; iframe Howner
    · iexfalso; iapply own_ticket_exclusive $$ [$Hissued $Hissued']
  · imod Hclose $$ [Hlo Hln Hauth Hstate] with -
    · iexists o, n
      iframe Hlo Hln Hauth Hstate
    imodintro
    wp_pures
    rw [beq_eq_false_iff_ne.mpr (by simp; omega)]
    wp_pures
    iapply IH $$ Hissued HΦ

@[rocq_alias heap_lang.ticket_lock.acquire_spec]
theorem acquire_spec (γ : GName) (lk : Val) (R : IProp GF) :
    {{ isLock γ lk R }} hl(&acquire &lk) {{ RET hl_val(#()); locked γ ∗ R }} := by
  iintro %Φ #Hlock Hcont
  unfold isLock lockInv
  icases Hlock with ⟨%lo, %ln, %Heq, #Hinv⟩
  subst Heq
  iloeb as IH
  wp_rec
  wp_pures
  wp_bind !_
  iinv Hinv with ⟨%o, %n, Hlo, >Hln, Hauth, Hstate⟩ Hclose
  wp_load
  imod Hclose $$ [$Hlo $Hln $Hauth $Hstate] with -
  imodintro
  wp_pures
  wp_bind cmpXchg(_, _, _)
  iinv Hinv with ⟨%o', %n', >Hlo, >Hln, >Hauth, Hstate⟩ Hclose
  wp_cmpxchg with hsuc hfail
  · obtain rfl : n' = n := by simp at hsuc; omega
    imod iOwn_update (a' := (auth o' (n' + 1) : TicketR) • ticket n') $$ Hauth
      with ⟨Hauth, Hissued⟩
    · refine Auth.auth_update_alloc ?_
      rw [setSeq_succ, Nat.zero_add]
      exact LocalUpdate.prod_2 _ _
        (localUpdate_alloc_empty_of_disj _ _ (disjoint_singleton_setSeq (by omega)))
    imod Hclose $$ [Hlo Hln Hauth Hstate] with -
    · iexists o', n' + 1
      rw [Int.natCast_succ]
      iframe Hlo Hln Hauth Hstate
    imodintro
    wp_pures
    iapply waitLoop_spec $$ [Hissued] Hcont
    unfold isLock issued lockInv
    iframe Hissued
    iexists lo, ln
    iframe Hinv
    itrivial
  · imod Hclose $$ [$Hlo $Hln $Hauth $Hstate] with -
    imodintro
    wp_pures
    iapply IH $$ Hcont

@[rocq_alias heap_lang.ticket_lock.release_spec]
theorem release_spec (γ : GName) (lk : Val) (R : IProp GF) :
    {{ isLock γ lk R ∗ locked γ ∗ R }} hl(&release &lk) {{ RET hl_val(#()); True }} := by
  unfold isLock locked lockInv
  iintro %Φ ⟨⟨%lo, %ln, %Heq, #Hinv⟩, ⟨%o, Howner⟩, HR⟩ Hcont
  subst Heq
  wp_rec
  wp_pures
  wp_bind !_
  iinv Hinv with ⟨%o', %n, >Hlo, >Hln, >Hauth, Hstate⟩ Hclose
  wp_load
  ihave %rfl := own_owner_agree $$ [$Hauth $Howner]
  imod Hclose $$ [$Hlo $Hln $Hauth $Hstate] with -
  imodintro
  wp_pures
  iapply wp_fupd
  iinv Hinv with ⟨%o', %n', >Hlo, >Hln, >Hauth, Hstate⟩ Hclose
  wp_store
  ihave %rfl := own_owner_agree $$ [$Hauth $Howner]
  icases Hstate with (⟨Howner', -⟩ | Hissued)
  · iexfalso; iapply own_owner_exclusive $$ [$Howner $Howner']
  imod iOwn_update (F := TicketLockF) (a := (auth o n' : TicketR) • owner o)
      (a' := (auth (o + 1) n' : TicketR) • owner (o + 1)) $$ [Hauth Howner]
      with ⟨Hauth, Howner⟩
  · exact Auth.auth_update
      (LocalUpdate.prod_1 _ _ (LocalUpdate.option (LocalUpdate.exclusive trivial)))
  · iapply iOwn_op.mpr
    iframe Hauth Howner
  imod Hclose $$ [Hlo Hln Hauth Howner HR] with -
  · iexists o + 1, n'
    rw [Int.natCast_succ]
    iframe Hlo Hln Hauth
    ileft; iframe Howner HR
  iapply Hcont; itrivial

end proof

@[implicit_reducible, rocq_alias heap_lang.ticket_lock]
def instLock [HeapLangGS hlc GF] : Lock GF where
  newlock := newlock
  acquire := acquire
  release := release
  lockG := TicketLockG
  name := GName
  isLock _ γ lk R := isLock γ lk R
  locked _ γ := locked γ
  isLock_persistent γ lk R := instIsLockPersistent γ lk R
  isLock_iff γ lk R₁ R₂ := isLock_iff γ lk R₁ R₂
  locked_timeless γ := instLockedTimeless γ
  locked_exclusive γ := locked_exclusive γ
  newlock_spec_delay_init := newlock_spec
  acquire_spec γ lk R := acquire_spec γ lk R
  release_spec γ lk R := release_spec γ lk R

end TicketLock
end
