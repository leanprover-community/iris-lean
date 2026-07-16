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
  ipureintro
  rfl

-- `wp_load` accepts *fractional* ownership (where store/faa/free would reject)
example {l : Loc} {dq : DFrac} {v : Val} :
    (l ↦{dq} some v) ∗ ((l ↦{dq} some v) -∗ Φ v) ⊢ WP hl(!v(#l)) @ s ; E {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_load
  imodintro
  iapply HΦ $$ Hl

/--
error: Tactic `wp_load` failed: cannot find a points-to hypothesis for location l

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l l' : Loc
v : Val
⊢
  ∗Hpt : l' ↦ some v
  ⊢ WP hl(!#l) @ s ; E {{ Φ }}
-/
#guard_msgs (whitespace := lax) in
example {l l' : Loc} {v : Val} :
    (l' ↦ some v) ⊢ WP hl(!v(#l)) @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_load

/--
error: Tactic `wp_load` failed: cannot find a `load` redex

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
v v' : Val
⊢
  ∗Hpt : l ↦ some v
  ⊢ WP hl(#l ← v(&v')) @ s ; E {{ Φ }}
-/
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

/--
error: Tactic `wp_store` failed: cannot find a full-ownership points-to hypothesis for location l

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
dq : DFrac
v v' : Val
⊢
  ∗Hpt : l ↦{dq} some v
  ⊢ WP hl(#l ← v(&v')) @ s ; E {{ Φ }}
-/
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
  ipureintro
  rfl

-- `wp_faa` failing: writes need full ownership, fractional is rejected
/--
error: Tactic `wp_faa` failed: cannot find a full-ownership points-to hypothesis for location l

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
dq : DFrac
z : Int
⊢
  ∗Hpt : l ↦{dq} some hl_val(#z)
  ⊢ WP hl(faa(#l, #1)) @ s ; E {{ Φ }}
-/
#guard_msgs (whitespace := lax) in
example {l : Loc} {dq : DFrac} {z : Int} :
    (l ↦{dq} some hl_val(#z)) ⊢ WP hl(faa(#l, #1)) @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_faa

-- `wp_faa` failing: the stored value must be an integer literal
/--
error: Tactic `wp_faa` failed: the points-to hypothesis for location l does not store an integer

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
v : Val
⊢
  ∗Hpt : l ↦ some v
  ⊢ WP hl(faa(#l, #1)) @ s ; E {{ Φ }}
-/
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
  ipureintro
  rfl

-- `wp_xchg` failing: writes need full ownership, fractional is rejected
/--
error: Tactic `wp_xchg` failed: cannot find a full-ownership points-to hypothesis for location l

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
dq : DFrac
v v' : Val
⊢
  ∗Hpt : l ↦{dq} some v
  ⊢ WP hl(xchg(#l, v(&v'))) @ s ; E {{ Φ }}
-/
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
/--
error: Tactic `wp_free` failed: cannot find a full-ownership points-to hypothesis for location l

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
dq : DFrac
v : Val
⊢
  ∗Hpt : l ↦{dq} some v
  ⊢ WP hl(free(#l)) @ s ; E {{ Φ }}
-/
#guard_msgs (whitespace := lax) in
example {l : Loc} {dq : DFrac} {v : Val} :
    (l ↦{dq} some v) ⊢ WP hl(free(#l)) @ s ; E {{ Φ }} := by
  iintro Hpt
  wp_free

end wp_free

section wp_alloc

-- `alloc` produces a fresh `l ↦ some v`; `wp_alloc l as Hl` names both
example {v : Val} :
    ⊢ WP hl(ref(&v)) @ s ; E {{ w, ∃ l : Loc, ⌜w = hl_val(#l)⌝ ∗ l ↦ some v }} := by
  wp_alloc l as Hl
  imodintro
  iexists l
  isplit
  · ipureintro; rfl
  · iexact Hl

-- anonymous variant: `wp_alloc l` auto-names the points-to; `iframe` picks it up
example {v : Val} :
    ⊢ WP hl(ref(&v)) @ s ; E {{ w, ∃ l : Loc, ⌜w = hl_val(#l)⌝ ∗ l ↦ some v }} := by
  wp_alloc l
  imodintro
  iexists l
  iframe
  ipureintro
  rfl

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
  ipureintro
  rfl

-- `wp_cmpxchg_suc` failing: a successful CAS writes, so fractional is rejected
/--
error: Tactic `wp_cmpxchg_suc` failed: cannot find a full-ownership points-to hypothesis for
location l

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ : Val → IProp GF
l : Loc
dq : DFrac
v2 : Val
⊢
  ∗Hl : l ↦{dq} some hl_val(#1)
  ⊢ WP hl(cmpXchg(#l, #1, v(&v2))) @ s ; E {{ Φ }}
-/
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
  ipureintro
  rfl

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
  wp_cmpxchg as Heq | Hne
  · imodintro
    ileft
    iframe
    ipureintro
    rfl
  · imodintro
    iright
    iframe
    ipureintro
    rfl

end wp_cmpxchg

section goal_shape

-- heap tactics reject WPs over a non-HeapLang `IrisGS_gen` instance
/--
error: Tactic `wp_load` failed: the goal is not a HeapLang WP

hlc : HasLC
GF : BundledGFunctors
ι : HeapLangGS hlc GF
s : Stuckness
E : CoPset
Φ✝ : Val → IProp GF
hlc' : HasLC
GF' : BundledGFunctors
inst✝ : IrisGS_gen hlc' Exp GF'
e : Exp
Φ : Val → IProp GF'
⊢
  ⊢ WP e @ s ; E {{ Φ }}
-/
#guard_msgs (whitespace := lax) in
example {hlc'} {GF' : BundledGFunctors} [IrisGS_gen hlc' Exp GF']
    {e : Exp} {Φ : Val → IProp GF'} :
    ⊢ WP e @ s ; E {{ Φ }} := by
  wp_load

-- heap tactics reject goals that are not WPs at all
/--
error: The goal P must be a WP
-/
#guard_msgs (whitespace := lax) in
example {P : IProp GF} : P ⊢ P := by
  iintro HP
  wp_load

end goal_shape

end Iris.HeapLang
