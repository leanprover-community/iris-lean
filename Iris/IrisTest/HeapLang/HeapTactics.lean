/-
Copyright (c) 2026 Klaus Kraßnitzer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Kraßnitzer
-/
module

public import Iris.BI
public import Iris.Instances
public import Iris.HeapLang.Notation
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre

/-! Tests for the heap-operation tactics (`wp_load`, ...). Unlike the tests in
`Tests.HeapLang.WeakestPre`, these need the `IrisGS_gen` instance to be the one
derived from `HeapLangGS`, so no generic `IrisGS_gen` variable is in scope. -/

namespace Iris.HeapLang

variable {hlc} {GF : BundledGFunctors} [ι : HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

section wp_load

example {l : Loc} {v : Val} :
    (l ↦ some v) ∗ ((l ↦ some v) -∗ Φ v) ⊢ WP hl(!v(#l)) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, HΦ⟩
  wp_load
  imodintro
  iapply HΦ $$ Hpt

-- with a ▷ on the points-to and the load inside an evaluation context
example {l l' : Loc} :
    ▷ (l ↦ some hl_val(#2)) ∗ ▷ (l' ↦ some hl_val(#3)) ⊢
      WP hl(#1 + !v(#l)) @ s ; E {{ w, ⌜w = hl_val(#3)⌝ ∗ (l ↦ some hl_val(#2)) }} := by
  iintro ⟨Hpt, Hpt'⟩
  wp_load
  wp_binop
  imodintro
  iframe Hpt
  itrivial

-- `wp_load` accepts *fractional* ownership (where store/faa/free would reject)
example {l : Loc} {dq : DFrac} {v : Val} :
    (l ↦{dq} some v) ∗ ((l ↦{dq} some v) -∗ Φ v) ⊢ WP hl(!v(#l)) @ s ; E {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_load
  imodintro
  iapply HΦ $$ Hl

-- a *discarded* points-to is persistent, so it can sit in the intuitionistic context;
-- the lookup finds it there and keeps it (`Hl` is still available afterwards)
example {l : Loc} {v : Val} :
    □ (l ↦{.discard} some v) ∗ ((l ↦{.discard} some v) -∗ Φ v) ⊢
      WP hl(!v(#l)) @ s ; E {{ Φ }} := by
  iintro ⟨#Hl, HΦ⟩
  wp_load
  imodintro
  iapply HΦ $$ Hl

-- a *bare* discarded points-to moved to the intuitionistic context with `#`;
-- this needs the `Persistent` instance for `l ↦{.discard} v`
example {l : Loc} {v : Val} :
    (l ↦{.discard} some v) ∗ ((l ↦{.discard} some v) -∗ Φ v) ⊢
      WP hl(!v(#l)) @ s ; E {{ Φ }} := by
  iintro ⟨#Hl, HΦ⟩
  wp_load
  imodintro
  iapply HΦ $$ Hl

/-- error: wp_load: cannot find a points-to hypothesis for l ↦{?_} _ -/
#guard_msgs (whitespace := lax) in
set_option pp.mvars false in
example {l l' : Loc} {v : Val} :
    (l' ↦ some v) ⊢ WP hl(!v(#l)) @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_load

/-- error: wp_load: cannot find a `load` redex -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {v v' : Val} :
    (l ↦ some v) ⊢ WP hl(v(#l) ← &v') @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_load

end wp_load

section wp_store

example {l : Loc} {v v' : Val} :
    (l ↦ some v) ∗ ((l ↦ some v') -∗ Φ hl_val(#())) ⊢ WP hl(v(#l) ← &v') @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, HΦ⟩
  wp_store
  imodintro
  iapply HΦ $$ Hpt

-- `wp_store` must pick the `l` points-to and leave the `l'` one untouched
example {l l' : Loc} {v v' w : Val} :
    (l ↦ some v) ∗ (l' ↦ some w) ⊢
      WP hl(v(#l) ← &v') @ s ; E {{ _r, (l ↦ some v') ∗ (l' ↦ some w) }} := by
  iintro ⟨Hl, Hl'⟩
  wp_store
  imodintro
  iframe

example {l : Loc} {v v' v'' : Val} :
    (l ↦ some v) ⊢
      WP hl(if #true then (v(#l) ← &v') else (v(#l) ← &v'')) @ s ; E
        {{ _r, l ↦ some v' }} := by
  iintro Hpt
  wp_store
  imodintro
  iframe

-- Rocq parity (`first [wp_seq|wp_finish]`): a store in sequencing position discards its
-- `#()` result, so `wp_store` steps through the `;` instead of leaving a pure redex behind
/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
v v' : Val
⊢
  ∗Hpt : l ↦ some v'
  ⊢ WP hl(!#l) @ s ; E {{ w, ⌜w = v'⌝ ∗ l ↦ some v' }}
-/
#guard_msgs (whitespace := lax, trace, drop error) in
example {l : Loc} {v v' : Val} :
    (l ↦ some v) ⊢
      WP hl(v(#l) ← &v'; !v(#l)) @ s ; E {{ w, ⌜w = v'⌝ ∗ l ↦ some v' }} := by
  iintro Hpt
  wp_store
  trace_state

-- the fast-forward is *only* for the sequencing redex: a `let` binding the result stays
/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
v v' : Val
⊢
  ∗Hpt : l ↦ some v'
  ⊢ WP hl(let x := #(); !#l) @ s ; E {{ _r, l ↦ some v' }}
-/
#guard_msgs (whitespace := lax, trace, drop error) in
example {l : Loc} {v v' : Val} :
    (l ↦ some v) ⊢
      WP hl(let x := v(#l) ← &v'; !v(#l)) @ s ; E {{ _r, l ↦ some v' }} := by
  iintro Hpt
  wp_store
  trace_state

/-- error: wp_store: cannot find a points-to hypothesis for l ↦{DFrac.own 1} _ -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {dq : DFrac} {v v' : Val} :
    (l ↦{dq} some v) ⊢ WP hl(v(#l) ← &v') @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_store

end wp_store

section wp_faa

example {l : Loc} {z1 z2 : Int} :
    (l ↦ some hl_val(#z1)) ∗ ((l ↦ some hl_val(#(z1 + z2))) -∗ Φ hl_val(#z1)) ⊢
      WP hl(faa(#l, #z2)) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, HΦ⟩
  wp_faa
  imodintro
  iapply HΦ $$ Hpt

-- `wp_faa` buried in an evaluation context (`#1 + •`), with a `▷` on the points-to
example {l : Loc} {z : Int} :
    ▷ (l ↦ some hl_val(#z)) ⊢
      WP hl(#1 + faa(#l, #2)) @ s ; E
        {{ w, ⌜w = hl_val(#((1 : Int) + z))⌝ ∗ l ↦ some hl_val(#(z + (2 : Int))) }} := by
  iintro Hl
  wp_faa
  wp_binop
  imodintro
  iframe
  itrivial

-- `wp_faa` failing: writes need full ownership, fractional is rejected
/-- error: wp_faa: cannot find a points-to hypothesis for l ↦{DFrac.own 1} _ -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {dq : DFrac} {z : Int} :
    (l ↦{dq} some hl_val(#z)) ⊢ WP hl(faa(#l, #1)) @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_faa

-- `wp_faa` failing: the stored value must be an integer literal
/-- error: wp_faa: the points-to hypothesis for location l does not store an integer -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {v : Val} :
    (l ↦ some v) ⊢ WP hl(faa(#l, #1)) @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_faa

end wp_faa

section wp_xchg

-- `xchg` returns the old value and stores the new one
example {l : Loc} {v v' : Val} :
    (l ↦ some v) ∗ ((l ↦ some v') -∗ Φ v) ⊢ WP hl(xchg(#l, &v')) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, HΦ⟩
  wp_xchg
  imodintro
  iapply HΦ $$ Hpt

-- `wp_xchg` under a `▷`, returning the old value
example {l : Loc} {v v' : Val} :
    ▷ (l ↦ some v) ⊢ WP hl(xchg(#l, &v')) @ s ; E {{ w, ⌜w = v⌝ ∗ l ↦ some v' }} := by
  iintro Hl
  wp_xchg
  imodintro
  iframe
  itrivial

-- Rocq parity: like `wp_store`, an `xchg` in sequencing position discards its result
/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
v v' : Val
⊢
  ∗Hpt : l ↦ some v'
  ⊢ WP hl(!#l) @ s ; E {{ w, ⌜w = v'⌝ ∗ l ↦ some v' }}
-/
#guard_msgs (whitespace := lax) in
example {l : Loc} {v v' : Val} :
    (l ↦ some v) ⊢
      WP hl(xchg(#l, &v'); !v(#l)) @ s ; E {{ w, ⌜w = v'⌝ ∗ l ↦ some v' }} := by
  iintro Hpt
  wp_xchg

-- `wp_xchg` failing: writes need full ownership, fractional is rejected
/-- error: wp_xchg: cannot find a points-to hypothesis for l ↦{DFrac.own 1} _ -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {dq : DFrac} {v v' : Val} :
    (l ↦{dq} some v) ⊢ WP hl(xchg(#l, &v')) @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_xchg

end wp_xchg

section wp_free

-- `free` consumes the points-to (its resource is gone in the continuation)
example {l : Loc} {v : Val} :
    (l ↦ some v) ∗ Φ hl_val(#()) ⊢ WP hl(free(#l)) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, HΦ⟩
  wp_free
  imodintro
  iexact HΦ

-- `wp_free` on a `▷`-wrapped points-to, among several; the survivor stays
example {l l' : Loc} {v w : Val} :
    ▷ (l ↦ some v) ∗ (l' ↦ some w) ⊢
      WP hl(free(#l)) @ s ; E {{ _r, l' ↦ some w }} := by
  iintro ⟨Hl, Hl'⟩
  wp_free
  imodintro
  iframe

-- `wp_free` failing: deallocation needs full ownership, fractional is rejected
/-- error: wp_free: cannot find a points-to hypothesis for l ↦{DFrac.own 1} _ -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {dq : DFrac} {v : Val} :
    (l ↦{dq} some v) ⊢ WP hl(free(#l)) @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_free

end wp_free

section wp_alloc

-- `alloc` produces a fresh `l ↦ some v`; `wp_alloc l with Hl` names both
example {v : Val} :
    ⊢ WP hl(ref(&v)) @ s ; E {{ w, ∃ l : Loc, ⌜w = hl_val(#l)⌝ ∗ l ↦ some v }} := by
  wp_alloc l with Hl
  imodintro
  iexists l
  isplit
  · itrivial
  · iexact Hl

-- anonymous variant: `wp_alloc l` auto-names the points-to; `iframe` picks it up
example {v : Val} :
    ⊢ WP hl(ref(&v)) @ s ; E {{ w, ∃ l : Loc, ⌜w = hl_val(#l)⌝ ∗ l ↦ some v }} := by
  wp_alloc l
  imodintro
  iexists l
  iframe
  itrivial

-- For a general `allocn`, `wp_alloc` returns ownership of the freshly allocated array.
example {v : Val} :
    ⊢ WP hl(allocn(#3, &v)) @ s ; E
      {{ w, ∃ l : Loc, ⌜w = hl_val(#l)⌝ ∗
          (l ↦∗ List.replicate (3 : Int).toNat v : IProp GF) }} := by
  wp_alloc l with Hl
  imodintro
  iexists l
  iframe
  itrivial

-- A symbolic positive length is accepted, and unrelated spatial resources are preserved.
example {n : Int} (hn : 0 < n) {l' : Loc} {v w : Val} :
    l' ↦ some w ⊢ WP hl(allocn(#n, &v)) @ s ; E
      {{ r, ∃ l : Loc, ⌜r = hl_val(#l)⌝ ∗ l ↦∗ List.replicate n.toNat v ∗ l' ↦ some w }} := by
  iintro Hl'
  wp_alloc l with Hl
  imodintro
  iexists l
  iframe
  itrivial

-- Anonymous-hypothesis variant, with the allocation nested in an evaluation context.
example {v w : Val} :
    ⊢ WP hl((allocn(#2, &v), &w)) @ s ; E
      {{ r, ∃ l : Loc, ⌜r = hl_val((#l, &w))⌝ ∗
          (l ↦∗ List.replicate (2 : Int).toNat v : IProp GF) }} := by
  wp_alloc l
  wp_pair
  imodintro
  iexists l
  iframe
  itrivial

end wp_alloc

section wp_cmpxchg_suc

-- concrete equal values: the `v = v1` and `compareSafe` side conditions are
-- discharged automatically, the slot is updated to `v2`, result is `(v, #true)`
example {l : Loc} {v2 : Val} :
    ▷ (l ↦ some hl_val(#1)) ⊢
      WP hl(cmpXchg(v(#l), v(#1), &v2)) @ s ; E
        {{ w, ⌜w = hl_val((#1, #true))⌝ ∗ l ↦ some v2 }} := by
  iintro Hl
  wp_cmpxchg_suc
  imodintro
  iframe
  itrivial

-- `wp_cmpxchg_suc` failing: a successful CAS writes, so fractional is rejected
/-- error: wp_cmpxchg_suc: cannot find a points-to hypothesis for l ↦{DFrac.own 1} _ -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {dq : DFrac} {v2 : Val} :
    (l ↦{dq} some hl_val(#1)) ⊢
      WP hl(cmpXchg(v(#l), v(#1), &v2)) @ s ; E {{ Φ }} := by
  iintro Hl
  wp_cmpxchg_suc

end wp_cmpxchg_suc

section wp_cmpxchg_fail

-- distinct concrete values with *fractional* ownership: the points-to is only
-- read and kept at its fraction; result is `(v, #false)`. Both side conditions
-- (`≠` and `compareSafe`) are discharged automatically for concrete values.
example {l : Loc} {dq : DFrac} {v2 : Val} :
    ▷ (l ↦{dq} some hl_val(#1)) ⊢
      WP hl(cmpXchg(v(#l), v(#2), &v2)) @ s ; E
        {{ w, ⌜w = hl_val((#1, #false))⌝ ∗ l ↦{dq} some hl_val(#1) }} := by
  iintro Hl
  wp_cmpxchg_fail
  imodintro
  iframe
  itrivial

end wp_cmpxchg_fail

section wp_cmpxchg

-- symbolic compare value: both continuations appear as goals, with the
-- (dis)equality introduced into the Lean context under the given names;
-- `compareSafe` is discharged since the stored value is an unboxed literal
example {l : Loc} {v1 : Val} :
    ▷ (l ↦ some hl_val(#1)) ⊢
      WP hl(cmpXchg(v(#l), &v1, v(#7))) @ s ; E
        {{ w, (⌜w = hl_val((#1, #true))⌝ ∗ l ↦ some hl_val(#7)) ∨
              (⌜w = hl_val((#1, #false))⌝ ∗ l ↦ some hl_val(#1)) }} := by
  iintro Hl
  wp_cmpxchg with Heq Hne
  · imodintro
    ileft
    iframe
    itrivial
  · imodintro
    iright
    iframe
    itrivial

end wp_cmpxchg

section goal_shape

-- heap tactics reject WPs over a non-HeapLang `IrisGS_gen` instance
/-- error: wp_load: the goal is not a HeapLang WP -/
#guard_msgs (whitespace := lax) in
example {hlc'} {GF' : BundledGFunctors} [IrisGS_gen hlc' Exp GF']
    {e : Exp} {Φ : Val → IProp GF'} :
    ⊢ WP e @ s ; E {{ Φ }} := by
  wp_load

-- heap tactics reject goals that are not WPs at all
/-- error: wp_load: the goal is not a WP -/
#guard_msgs (whitespace := lax) in
example {P : IProp GF} : P ⊢ P := by
  iintro HP
  wp_load

-- the `wp_pures` prologue can reduce the expression to a value, leaving no redex
/-- error: wp_load: the expression has been reduced to a value, there is no redex left -/
#guard_msgs (whitespace := lax) in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #0) {{ v, True }} := by
  wp_load

end goal_shape

end Iris.HeapLang
