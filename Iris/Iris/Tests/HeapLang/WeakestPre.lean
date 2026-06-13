/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import Iris.Instances
public import Iris.HeapLang.Notation
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre

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
  ⊢ WP hl((#2 + (#1 + #2))) {{ v, WP hl(v(&v)) {{ v, True }} }}
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
