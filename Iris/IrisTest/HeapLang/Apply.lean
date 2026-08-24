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
public import Iris.HeapLang.PrimitiveLaws
public import Iris.ProgramLogic.WeakestPre

/-! Tests for `wp_apply` and `wp_smart_apply`. Several exercise machinery shared by
both: evaluation-context search order, and the post-pass that must touch only the
goals an application created. -/

namespace Iris.HeapLang

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF]
set_option linter.unusedVariables false
set_option pp.mvars false

-- direct application of a WP hypothesis from the Iris context
example {Φ : Val → IProp GF} : ⊢@{IProp GF}
    WP hl(#1 + #2) {{ Φ }} -∗ WP hl(#1 + #2) {{ Φ }} := by
  iintro H
  wp_apply H

-- a beta-redex step lemma whose premise is a later'd WP
theorem beta_spec {v : Val} {Φ : Val → IProp GF} :
    ▷ WP hl(v(&v) + #1) {{ Φ }} ⊢ WP hl(v(λ x, x + #1) v(&v)) {{ Φ }} := by
  iintro H
  wp_pure
  iexact H

-- the later'd WP premise is post-processed: the later is stripped
example : ⊢@{IProp GF} WP hl(v(λ x, x + #1) #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_apply beta_spec
  wp_pure
  itrivial

-- with a raw lambda, wp_smart_apply first takes the closure-formation pure step
example : ⊢@{IProp GF} WP hl((λ x, x + #1) #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_smart_apply beta_spec
  wp_pure
  itrivial

-- application at the head of the expression, discharging the points-to premise
example {l : Loc} {v : Val} : ⊢@{IProp GF}
    l ↦ some v -∗ WP hl(!v(#l)) {{ w, ⌜w = v⌝ }} := by
  iintro Hpt
  wp_apply wp_load $$ Hpt
  iintro Hpt
  itrivial

-- application under an evaluation context
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
n : Int
⊢
  ⊢ l ↦ some hl_val(#n) -∗ WP hl((#n + #1)) {{ w, ⌜w = hl_val(#(n + 1))⌝ }}
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {l : Loc} {n : Int} : ⊢@{IProp GF}
    l ↦ some hl_val(#n) -∗ WP hl(!v(#l) + #1) {{ w, ⌜w = hl_val(#(n + 1 : Int))⌝ }} := by
  iintro Hpt
  wp_apply wp_load $$ Hpt
  trace_state

-- wp_smart_apply takes pure steps until the lemma applies
example {l : Loc} {v : Val} : ⊢@{IProp GF}
    l ↦ some v -∗ WP hl(if #true then !v(#l) else #42) {{ w, ⌜w = v⌝ }} := by
  iintro Hpt
  wp_smart_apply wp_load $$ Hpt
  iintro Hpt
  itrivial

-- plain wp_apply fails when a pure step is needed
/-- error: wp_apply: cannot apply iprop(▷ (l ↦ some v -∗ ?_ v) -∗ WP hl(!#l) @ ?_ ; ?_ {{ ?_ }} ) -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {v : Val} : ⊢@{IProp GF}
    l ↦ some v -∗ WP hl(if #true then !v(#l) else #42) {{ w, ⌜w = v⌝ }} := by
  iintro Hpt
  wp_apply wp_load $$ Hpt

-- wp_apply fails when the lemma matches no evaluation context
/-- error: wp_apply: cannot apply iprop(▷ (l ↦ some v -∗ ?_ v) -∗ WP hl(!#l) @ ?_ ; ?_ {{ ?_ }} ) -/
#guard_msgs (whitespace := lax) in
example {l : Loc} {v : Val} : ⊢@{IProp GF}
    l ↦ some v -∗ WP hl(#1 + #2) {{ w, ⌜w = v⌝ }} := by
  iintro Hpt
  wp_apply wp_load $$ Hpt

-- under a non-empty context, so the remainder goes into the postcondition
example {l : Loc} {Φ : Val → IProp GF} : ⊢@{IProp GF}
    WP hl(!v(#l)) {{ w, WP hl(v(&w) + #1) {{ Φ }} }} -∗ WP hl(!v(#l) + #1) {{ Φ }} := by
  iintro H
  wp_apply H

-- the post-pass must not reach a sibling goal
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
v : Val
P : IProp GF
⊢
  ⊢ l ↦ some v -∗ ⌜v = v⌝

hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
v : Val
P : IProp GF
⊢
  ∗HP : ▷ P
  ⊢ ▷ P
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {l : Loc} {v : Val} {P : IProp GF} : ⊢@{IProp GF}
    ▷ P ∗ (l ↦ some v) -∗ WP hl(!v(#l)) {{ w, ⌜w = v⌝ }} ∗ (▷ P) := by
  iintro ⟨HP, Hpt⟩
  isplitl [Hpt]
  wp_apply wp_load $$ Hpt
  trace_state

-- also goals that are part of the specialization pattern have ▷ stripped
-- (this differs from Rocq)
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢
  ⊢ WP hl((#2 + #1)) {{ v, ⌜v = hl_val(#3)⌝ }}
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example : ⊢@{IProp GF} WP hl(v(λ x, x + #1) #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_apply beta_spec $$ []
  trace_state

-- `wp_smart_apply` taking more than one pure step before the lemma applies
example {l : Loc} {v : Val} : ⊢@{IProp GF}
    l ↦ some v -∗
      WP hl(if #true then (if #true then !v(#l) else #0) else #42) {{ w, ⌜w = v⌝ }} := by
  iintro Hpt
  wp_smart_apply wp_load $$ Hpt
  iintro Hpt
  itrivial

-- the post-pass runs once, in the successful iteration: `▷ ▷` loses exactly one `▷`
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
P : IProp GF
Φ : Val → IProp GF
H : ▷ ▷ P ⊢ WP hl((v(λ x, (x + #1))) #2) {{ Φ }}
⊢
  ⊢ ▷ P
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {P : IProp GF} {Φ : Val → IProp GF}
    (H : ▷ ▷ P ⊢ WP hl(v(λ x, x + #1) #2) {{ Φ }}) : ⊢@{IProp GF}
    WP hl(if #true then ((λ x, x + #1) #2) else #0) {{ Φ }} := by
  wp_smart_apply H
  trace_state

-- out of pure steps: the error is about the original goal, not a mid-reduction one
/--
error: wp_smart_apply: cannot apply iprop(▷ (l ↦ some v -∗ ?_ v) -∗ WP hl(!#l) @ ?_ ; ?_ {{ ?_ }} )
-/
#guard_msgs (whitespace := lax) in
example {l : Loc} {v : Val} : ⊢@{IProp GF}
    l ↦ some v -∗ WP hl(#1 + #2) {{ w, ⌜w = v⌝ }} := by
  iintro Hpt
  wp_smart_apply wp_load $$ Hpt

-- `wp_wand` is polymorphic in expression and postcondition, so every decomposition
-- unifies and only the order decides: outermost leaves the expression the caller wrote,
-- innermost would return a goal about `#l`.
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
Φ : Val → IProp GF
⊢
  ⊢ WP hl((!#l + #1)) {{ ?_ }}

hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
Φ : Val → IProp GF
⊢
  ⊢ ∀ v, ?_ v -∗ Φ v

hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
Φ : Val → IProp GF
⊢ Val → IProp GF
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {l : Loc} {Φ : Val → IProp GF} : ⊢@{IProp GF}
    WP hl(!v(#l) + #1) {{ Φ }} := by
  wp_apply wp_wand
  trace_state

-- the same, instrumented: the leftover premise records which decomposition was picked
example {l : Loc} {Φ : Val → IProp GF} : ⊢@{IProp GF}
    (∀ (e : Exp) (Ψ : Val → IProp GF), ⌜e = hl(!v(#l) + #1)⌝ -∗ WP hl(&e) {{ Ψ }}) -∗
    WP hl(!v(#l) + #1) {{ Φ }} := by
  iintro H
  wp_apply H
  itrivial

-- `with` subsumes a following `iintro`
example {l : Loc} {v : Val} : ⊢@{IProp GF}
    l ↦ some v -∗ WP hl(if #true then !v(#l) else #0) {{ w, ⌜w = v⌝ }} := by
  iintro Hpt
  wp_smart_apply wp_load $$ Hpt with Hpt
  itrivial

-- binders and hypotheses mix in one pattern list
example {l : Loc} {Φ Ψ : Val → IProp GF} : ⊢@{IProp GF}
    WP hl(!v(#l)) {{ Ψ }} -∗ (∀ w, Ψ w -∗ WP hl(v(&w) + #1) {{ Φ }}) -∗
    WP hl(!v(#l) + #1) {{ Φ }} := by
  iintro H HΦ
  wp_apply wp_wand $$ H with %w Hw
  iapply HΦ $$ Hw

-- it targets the last goal the application produced, leaving the others untouched
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
v : Val
Φ : Val → IProp GF
⊢
  ⊢ l ↦ some v

hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
v : Val
Φ : Val → IProp GF
w : Val
⊢
  ∗Hw : ⌜w = v⌝
  ⊢ Φ w
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {l : Loc} {v : Val} {Φ : Val → IProp GF} : ⊢@{IProp GF}
    (l ↦ some v -∗ (∀ w, ⌜w = v⌝ -∗ Φ w) -∗ WP hl(!v(#l)) {{ Φ }}) -∗
    WP hl(!v(#l)) {{ Φ }} := by
  iintro Hspec
  wp_apply Hspec with %w Hw
  trace_state

-- test `with` notation
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
Φ : Val → IProp GF
a b c : Val
⊢
  ∗Ha : ⌜a = hl_val(#1)⌝
  ∗Hb : ⌜b = hl_val(#2)⌝
  ∗Hc : ⌜c = hl_val(#3)⌝
  ⊢ Φ a
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {l : Loc} {Φ : Val → IProp GF} : ⊢@{IProp GF}
    ((∀ a b c, ⌜a = hl_val(#1)⌝ -∗ ⌜b = hl_val(#2)⌝ -∗ ⌜c = hl_val(#3)⌝ -∗ Φ a) -∗
      WP hl(!v(#l)) {{ Φ }}) -∗
    WP hl(!v(#l)) {{ Φ }} := by
  iintro Hspec
  wp_apply Hspec with %a %b %c Ha Hb Hc
  trace_state

-- `with` runs after the loop: a failed introduction must not trigger another retry
/--
error: iintro: iprop(l ↦ some v -∗ ⌜v = v⌝) cannot be turned into a universal quantifier
  or pure hypothesis
-/
#guard_msgs (whitespace := lax) in
example {l : Loc} {v : Val} : ⊢@{IProp GF}
    l ↦ some v -∗ WP hl(if #true then !v(#l) else #0) {{ w, ⌜w = v⌝ }} := by
  iintro Hpt
  wp_smart_apply wp_load $$ Hpt with %bogus

-- `with` targets a `$$` goal when the application produced none
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
Q R : IProp GF
e : Exp
Φ : Val → IProp GF
⊢
  ∗HQR : Q -∗ R
  ∗HQ : Q
  ⊢ R
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {Q R : IProp GF} {e : Exp} {Φ : Val → IProp GF} : ⊢@{IProp GF}
    ((Q -∗ R) -∗ WP hl(&e) {{ Φ }}) -∗ (Q -∗ R) -∗ WP hl(&e) {{ Φ }} := by
  iintro H HQR
  wp_apply H $$ [HQR] with HQ
  trace_state

-- the continuation handed to a `$$` pattern
/-- trace:
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
Φ Ψ : Val → IProp GF
v : Val
⊢
  ∗Hv : Ψ v
  ⊢ Φ v
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {l : Loc} {Φ Ψ : Val → IProp GF} : ⊢@{IProp GF}
    WP hl(!v(#l)) {{ Ψ }} -∗ WP hl(!v(#l)) {{ Φ }} := by
  iintro H
  wp_apply wp_wand $$ H [] with %v Hv
  trace_state


-- `wp_apply ... with` when there are mvars after the last Iris goal
/--
trace: hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
Φ : Val → IProp GF
⊢ ⏎
  ⊢ ⌜l = ?_⌝

hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
Φ : Val → IProp GF
l' : Loc
x✝ : l = l'
⊢ ⏎
  ⊢ WP hl(!#l') {{ Φ }}

hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
Φ : Val → IProp GF
⊢ Loc
-/
#guard_msgs (trace, drop all, whitespace := lax) in
example {l : Loc} {Φ : Val → IProp GF} : ⊢@{IProp GF}
    (∀ l', ⌜l = l'⌝ -∗ (∀ l', ⌜l = l'⌝ -∗ WP hl(!v(#l')) {{ Φ }}) -∗ WP hl(!v(#l)) {{ Φ }}) -∗ WP hl(!v(#l)) {{ Φ }} := by
  iintro H
  wp_apply H with %l' %_
  trace_state

-- no goal to introduce into
/-- error: no remaining Iris goal -/
#guard_msgs (whitespace := lax) in
example {Φ : Val → IProp GF} {v : Val} : ⊢@{IProp GF}
    WP hl(v(&v)) {{ Φ }} -∗ WP hl(v(&v)) {{ Φ }} := by
  iintro H
  wp_apply H with Hx
