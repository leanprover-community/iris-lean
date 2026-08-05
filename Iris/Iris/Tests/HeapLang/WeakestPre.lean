/-
Copyright (c) 2026 Fernando Leal, Klaus Kraßnitzer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal, Klaus Kraßnitzer
-/
module

public import Iris.BI
public import Iris.Instances
public import Iris.HeapLang.Notation
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre

local stepindex Nat

namespace Iris.HeapLang

variable {hlc} {GF : BundledGFunctors} [ι : IrisGS_gen hlc HeapLang.Exp GF]
set_option linter.unusedVariables false
set_option pp.mvars false

namespace wp_value_head

variable (v : Val)

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v : Val
⊢ ⏎
  ⊢ |={⊤}=> True
-/
#guard_msgs in
example : ⊢@{IProp GF} WP (v : Exp) {{ v, True }} := by
  wp_value_head

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v : Val
⊢ ⏎
  ⊢ |={⊤}=> True
-/
#guard_msgs in
example : ⊢@{IProp GF} WP (v : Exp) {{ v, |={⊤}=> True }} := by
  wp_value_head

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v : Val
⊢ ⏎
  ⊢ WP hl(v(&v)) {{ v, True }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP (v : Exp) {{ v, WP ((v : Val) : Exp) {{ v, True }} }} := by
  istart
  wp_value_head

end wp_value_head

namespace wp_bind

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(((#0 + #1) + #2)) {{ v, WP hl((v(&v) + #3)) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind ((#0 + _) + _)

/--
error: Tactic `wp_bind` failed: Cannot unify hl((#2 + &?_)) with any possible evaluation context

hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((((#0 + #1) + #2) + #3)) {{ v, True }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (#2 + _)

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(((#0 + #1) + #2)) {{ v, WP hl((v(&v) + #3)) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (_ + #2)

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#0 + #1)) {{ v, WP hl(((v(&v) + #2) + #3)) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (#0 + #1)

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#2 + (#1 + #2))) {{ v, True }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(#2 + (#1 + #2)) {{ v, True }} := by
  wp_bind (#2 + _)


/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#1 + #2)) {{ v, WP hl((#2 + v(&v))) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(#2 + (#1 + #2)) {{ v, True }} := by
  wp_bind (_ + #2)

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(snd((#1, #0))) {{ v, WP hl((v(&v) + #1)) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(snd((#1,#0)) + #1) {{ v, True }} := by
  wp_bind (snd(_))

end wp_bind

section wp_pure

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#0) = hl_val(#0)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(if #false then #1 else #0) {{ v, ⌜v = hl_val(#0)⌝ }} := by
  istart
  wp_pure

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(if #true then #1 else #0) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  istart
  wp_pure

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(snd(v((#1,#2)))) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  istart
  wp_pure

example : ⊢@{IProp GF}  WP hl(snd(v((#1,#2)))) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  istart
  wp_pure
  itrivial

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then if #false then #1 else #2 else #3) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_pures

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
n : Int
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#(hl_val(#(decide (1 * 2 <<< 3 ≤ n + (1 &&& 2 ^^^ 3)))) == hl_val(#true))) = hl_val(#true)⌝
-/
#guard_msgs in
example (n : Int) : ⊢@{IProp GF} WP hl((#1 * #2 <<< #3 ≤ #n + (#1 &&& #2 ^^^ #3)) = #true) {{ v, ⌜v = hl_val(#true)⌝ }} := by
  wp_pures

end wp_pure

section pure_tactics

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

section wp_lam

def addOne : Val := hl_val% λ x, x + #1

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(v(λ x, x + #1) #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_lam

/--
error: iapply: cannot apply WP hl(v(&?_) v(&?_)) @ ?_ ; ?_ {{ ?_ }} to WP hl(let x := #1; (x + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl((λ x, x + #1) #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_lam

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(&addOne #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_lam

/--
error: iapply: cannot apply WP hl(v(&?_) v(&?_)) @ ?_ ; ?_ {{ ?_ }} to WP hl(v(&addOne) (#1 + #1)) {{ v, ⌜v = hl_val(#3)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(&addOne (#1 + #1)) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_lam

end wp_lam

section wp_let

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(#1; #2) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1; #2) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_let

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(let x := #1; x + #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_let

end wp_let

section wp_seq

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1; #2) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_seq

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(let x := #1; x) {{ v, ⌜v = hl_val(#1)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(let x := #1; x) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_seq

end wp_seq

section wp_closure

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1 + #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_closure

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((v(λ x, (x + #1))) #1) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl((λ x, x + #1) #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_closure

end wp_closure

section wp_if

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_if

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #2)) {{ v, ⌜v = hl_val(#3)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1 + #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_if

end wp_if

section wp_if_true

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(if #false then #1 else #2) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #false then #1 else #2) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_if_true

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_if_true

end wp_if_true

section wp_if_false

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #false then #1 else #2) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_if_false

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_if_false

end wp_if_false

section wp_proj

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(fst(v((#1, #2)))) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_proj

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1, #2)) {{ v, ⌜v = hl_val((#1, #2))⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl((#1, #2)) {{ v, ⌜v = hl_val((#1, #2))⌝ }} := by
  wp_proj

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(snd(v((#1, #2)))) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_proj

end wp_proj

section wp_inj

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(injr((#1 + #1))) {{ v, ⌜v = hl_val(injr(#2))⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(injr(#1 + #1)) {{ v, ⌜v = hl_val(injr(#2))⌝ }} := by
  wp_inj

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(injr(#1)) = hl_val(injr(#1))⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(injr(#1)) {{ v, ⌜v = hl_val(injr(#1))⌝ }} := by
  wp_inj

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(injl(#1)) = hl_val(injl(#1))⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(injl(#1)) {{ v, ⌜v = hl_val(injl(#1))⌝ }} := by
  wp_inj

end wp_inj

section wp_pair

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val((#1, #2)) = hl_val((#1, #2))⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl((#1, #2)) {{ v, ⌜v = hl_val((#1, #2))⌝ }} := by
  wp_pair

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(((#1 + #1), #2)) {{ v, ⌜v = hl_val((#2, #2))⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl((#1 + #1, #2)) {{ v, ⌜v = hl_val((#2, #2))⌝ }} := by
  wp_pair

end wp_pair

section wp_unop

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #2)) {{ v, ⌜v = hl_val(#3)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1 + #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_unop

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#!true) = hl_val(#false)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(~#true) {{ v, ⌜v = hl_val(#false)⌝ }} := by
  wp_unop

end wp_unop

section wp_binop

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#(1 + 2)) = hl_val(#3)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1 + #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_binop

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((~#true)) {{ v, ⌜v = hl_val(#false)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(~#true) {{ v, ⌜v = hl_val(#false)⌝ }} := by
  wp_binop

end wp_binop

section wp_op

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#!true) = hl_val(#false)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(~#true) {{ v, ⌜v = hl_val(#false)⌝ }} := by
  wp_op

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_op

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#(1 + 2)) = hl_val(#3)⌝
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1 + #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_op

end wp_op

section wp_case

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(match injl(#1) with | injl(x) => (x + #1) | injr(y) => y) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF}
    WP hl(match injl(#1) with | injl(x) => x + #1 | injr(y) => y)
      {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_case

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(let x := #1; (x + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF}
    WP hl(match v(injl(#1)) with | injl(x) => x + #1 | injr(y) => y)
      {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_case

end wp_case

section wp_match

/--
error: unsolved goals
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF}
    WP hl(match v(injl(#1)) with | injl(x) => x + #1 | injr(y) => y)
      {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_match

/--
error: Tactic `wp_pure` failed: Cannot find expression to evaluate

hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }}
-/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_match

end wp_match

end pure_tactics
