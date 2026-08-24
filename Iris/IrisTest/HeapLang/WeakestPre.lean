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

namespace Iris.HeapLang

variable {hlc} {GF : BundledGFunctors} [ι : IrisGS_gen hlc HeapLang.Exp GF]
set_option linter.unusedVariables false
set_option pp.mvars false

namespace wp_value_head

variable (v : Val)

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v : Val
⊢ ⏎
  ⊢ |={⊤}=> True
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP (v : Exp) {{ v, True }} := by
  wp_value_head
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v : Val
⊢ ⏎
  ⊢ |={⊤}=> True
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP (v : Exp) {{ v, |={⊤}=> True }} := by
  wp_value_head
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v : Val
⊢ ⏎
  ⊢ WP hl(v(&v)) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP (v : Exp) {{ v, WP ((v : Val) : Exp) {{ v, True }} }} := by
  istart
  wp_value_head
  trace_state

end wp_value_head

namespace wp_bind

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(((#0 + #1) + #2)) {{ v, WP hl((v(&v) + #3)) {{ v, True }} }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind ((#0 + _) + _)
  trace_state

/-- error: wp_bind: Cannot unify hl((#2 + &?_)) with any possible evaluation context -/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (#2 + _)

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(((#0 + #1) + #2)) {{ v, WP hl((v(&v) + #3)) {{ v, True }} }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (_ + #2)
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#0 + #1)) {{ v, WP hl(((v(&v) + #2) + #3)) {{ v, True }} }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (#0 + #1)
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#2 + (#1 + #2))) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(#2 + (#1 + #2)) {{ v, True }} := by
  wp_bind (#2 + _)
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#1 + #2)) {{ v, WP hl((#2 + v(&v))) {{ v, True }} }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(#2 + (#1 + #2)) {{ v, True }} := by
  wp_bind (_ + #2)
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(snd((#1, #0))) {{ v, WP hl((v(&v) + #1)) {{ v, True }} }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(snd((#1,#0)) + #1) {{ v, True }} := by
  wp_bind (snd(_))
  trace_state

end wp_bind

section wp_pure

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#0) = hl_val(#0)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(if #false then #1 else #0) {{ v, ⌜v = hl_val(#0)⌝ }} := by
  istart
  wp_pure
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(if #true then #1 else #0) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  istart
  wp_pure
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}  WP hl(snd(v((#1,#2)))) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  istart
  wp_pure
  trace_state

example : ⊢@{IProp GF}  WP hl(snd(v((#1,#2)))) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  istart
  wp_pure
  itrivial

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(if #true then if #false then #1 else #2 else #3) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_pures
  trace_state

/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
n : Int
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#(hl_val(#(decide (1 * 2 <<< 3 ≤ n + (1 &&& 2 ^^^ 3)))) == hl_val(#true))) = hl_val(#true)⌝
-/
#guard_msgs (trace, drop error) in
example (n : Int) : ⊢@{IProp GF} WP hl((#1 * #2 <<< #3 ≤ #n + (#1 &&& #2 ^^^ #3)) = #true) {{ v, ⌜v = hl_val(#true)⌝ }} := by
  wp_pures
  trace_state

end wp_pure

section wp_pures

-- a step whose side condition survives is not taken (`compareSafe` is stuck here)
/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v1 v2 : Val
⊢ ⏎
  ⊢ WP hl((v(&v1) = v(&v2))) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (v1 v2 : Val) : ⊢@{IProp GF} WP hl(&v1 = &v2) {{ v, True }} := by
  wp_pures
  trace_state

-- steps before the guarded one still fire
/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v1 v2 : Val
⊢ ⏎
  ⊢ WP hl((v(&v1) = v(&v2))) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (v1 v2 : Val) :
    ⊢@{IProp GF} WP hl(if #true then (&v1 = &v2) else #false) {{ v, True }} := by
  wp_pures
  trace_state

-- `wp_pure` itself stays permissive and hands the side condition back
/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v1 v2 : Val
⊢ v1.compareSafe v2 = true

hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
v1 v2 : Val
⊢ ⏎
  ⊢ |={⊤}=> True
-/
#guard_msgs (trace, drop error) in
example (v1 v2 : Val) : ⊢@{IProp GF} WP hl(&v1 = &v2) {{ v, True }} := by
  wp_pure
  trace_state

-- with no step to take, `wp_pures` still strips the weakest precondition off a value
/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(v(#1)) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_pures
  trace_state

-- ... and succeeds without doing anything when the expression is stuck
/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
l : Loc
⊢ ⏎
  ⊢ WP hl(!#l) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (l : Loc) : ⊢@{IProp GF} WP hl(!#l) {{ v, True }} := by
  wp_pures
  trace_state

-- neither branch applies when the goal is not a weakest precondition
/-- error: wp_finish: The goal iprop(True) must be a WP -/
#guard_msgs in
example : ⊢@{IProp GF} True := by
  wp_pures

-- the guard counts only the goals the step produced, not those already open
/-- trace:
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ |={⊤}=> True

hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ True
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} (WP hl(if #true then #1 else #0) {{ v, True }} ∧ True) := by
  istart
  isplit
  wp_pures
  trace_state

end wp_pures

section pure_tactics

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

section wp_lam

def addOne : Val := hl_val% λ x, x + #1

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(v(λ x, x + #1) #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_lam
  trace_state

-- the head is still a closure expression, so there is no beta redex yet
/-- error: wp_rec: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl((λ x, x + #1) #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_lam

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(&addOne #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_lam
  trace_state

-- the argument is not a value yet, so the application is not a redex
/-- error: wp_rec: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(&addOne (#1 + #1)) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_lam

end wp_lam

section wp_rec

def readIt : Val := hl_val% λ l, !l

def loopIt : Val := hl_val% rec f x := f x

def callIt : Val := hl_val% rec f x := x #()

def notARec : Val := hl_val% #3

-- unfolding the head to find the redex does not lose the surrounding evaluation context
/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
⊢ ⏎
  ⊢ WP hl((!#l + #1)) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (l : Loc) : ⊢@{IProp GF} WP hl(&readIt #l + #1) {{ v, True }} := by
  wp_rec
  trace_state

-- the recursive call reads as the definition rather than as its expansion
/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
v : Val
⊢ ⏎
  ⊢ WP hl(v(&loopIt) v(&v)) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (v : Val) : ⊢@{IProp GF} WP hl(&loopIt &v) {{ v, True }} := by
  wp_rec
  trace_state

-- an argument that happens to be the same closure is left as written, not folded too
/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((v(rec f x := x #())) #()) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(&callIt v(rec f x := x #())) {{ v, True }} := by
  wp_rec
  trace_state

-- `wp_pures` never unfolds a head, so it terminates on a recursive definition
/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
v : Val
⊢ ⏎
  ⊢ WP hl(v(&loopIt) v(&v)) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (v : Val) : ⊢@{IProp GF} WP hl(&loopIt &v) {{ v, True }} := by
  wp_pures
  trace_state

-- a head that unfolds to something other than a closure is reported as such
/-- error: wp_rec: Cannot find expression to evaluate -/
#guard_msgs in
example (v : Val) : ⊢@{IProp GF} WP hl(&notARec &v) {{ v, True }} := by
  wp_rec

end wp_rec

section wp_let

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1; #2) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_let

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(let x := #1; x + #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_let
  trace_state

-- the evaluation context stays in the goal instead of moving into the postcondition
/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
⊢ ⏎
  ⊢ WP hl((!#l + #1)) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (l : Loc) : ⊢@{IProp GF} WP hl((let x := #l; !x) + #1) {{ v, True }} := by
  wp_let
  trace_state

end wp_let

section wp_seq

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(#1; #2) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_seq
  trace_state

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(let x := #1; x) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_seq

-- the evaluation context stays in the goal instead of moving into the postcondition
/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
⊢ ⏎
  ⊢ WP hl((!#l + #1)) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (l : Loc) : ⊢@{IProp GF} WP hl((#(); !#l) + #1) {{ v, True }} := by
  wp_seq
  trace_state

end wp_seq

section wp_closure

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1 + #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_closure

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((v(λ x, (x + #1))) #1) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl((λ x, x + #1) #1) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_closure
  trace_state

end wp_closure

section wp_if

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_if
  trace_state

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1 + #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_if

end wp_if

section wp_if_true

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #false then #1 else #2) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_if_true

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_if_true
  trace_state

end wp_if_true

section wp_if_false

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(if #false then #1 else #2) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_if_false
  trace_state

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_if_false

end wp_if_false

section wp_proj

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#1) = hl_val(#1)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(fst(v((#1, #2)))) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_proj
  trace_state

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl((#1, #2)) {{ v, ⌜v = hl_val((#1, #2))⌝ }} := by
  wp_proj

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#2) = hl_val(#2)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(snd(v((#1, #2)))) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_proj
  trace_state

end wp_proj

section wp_inj

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(injr(#1 + #1)) {{ v, ⌜v = hl_val(injr(#2))⌝ }} := by
  wp_inj

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(injr(#1)) = hl_val(injr(#1))⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(injr(#1)) {{ v, ⌜v = hl_val(injr(#1))⌝ }} := by
  wp_inj
  trace_state

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(injl(#1)) = hl_val(injl(#1))⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(injl(#1)) {{ v, ⌜v = hl_val(injl(#1))⌝ }} := by
  wp_inj
  trace_state

end wp_inj

section wp_pair

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val((#1, #2)) = hl_val((#1, #2))⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl((#1, #2)) {{ v, ⌜v = hl_val((#1, #2))⌝ }} := by
  wp_pair
  trace_state

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl((#1 + #1, #2)) {{ v, ⌜v = hl_val((#2, #2))⌝ }} := by
  wp_pair

end wp_pair

section wp_unop

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(#1 + #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_unop

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#!true) = hl_val(#false)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(~#true) {{ v, ⌜v = hl_val(#false)⌝ }} := by
  wp_unop
  trace_state

end wp_unop

section wp_binop

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#(1 + 2)) = hl_val(#3)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(#1 + #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_binop
  trace_state

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(~#true) {{ v, ⌜v = hl_val(#false)⌝ }} := by
  wp_binop

end wp_binop

section wp_op

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#!true) = hl_val(#false)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(~#true) {{ v, ⌜v = hl_val(#false)⌝ }} := by
  wp_op
  trace_state

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_op

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ |={⊤}=> ⌜hl_val(#(1 + 2)) = hl_val(#3)⌝
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF} WP hl(#1 + #2) {{ v, ⌜v = hl_val(#3)⌝ }} := by
  wp_op
  trace_state

end wp_op

section wp_case

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF}
    WP hl(match injl(#1) with | injl(x) => x + #1 | injr(y) => y)
      {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_case

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl(let x := #1; (x + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}
    WP hl(match v(injl(#1)) with | injl(x) => x + #1 | injr(y) => y)
      {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_case
  trace_state

end wp_case

section wp_match

/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
⊢ ⏎
  ⊢ WP hl((#1 + #1)) {{ v, ⌜v = hl_val(#2)⌝ }}
-/
#guard_msgs (trace, drop error) in
example : ⊢@{IProp GF}
    WP hl(match v(injl(#1)) with | injl(x) => x + #1 | injr(y) => y)
      {{ v, ⌜v = hl_val(#2)⌝ }} := by
  wp_match
  trace_state

-- the evaluation context stays in the goal instead of moving into the postcondition
/-- trace:
hlc : HasLC
GF✝ : BundledGFunctors
ι : IrisGS_gen hlc Exp GF✝
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
l : Loc
⊢ ⏎
  ⊢ WP hl((!#l + #1)) {{ v, True }}
-/
#guard_msgs (trace, drop error) in
example (l : Loc) : ⊢@{IProp GF}
    WP hl((match v(injl(#l)) with | injl(x) => !x | injr(y) => y) + #1) {{ v, True }} := by
  wp_match
  trace_state

/-- error: wp_pure: Cannot find expression to evaluate -/
#guard_msgs in
example : ⊢@{IProp GF} WP hl(if #true then #1 else #2) {{ v, ⌜v = hl_val(#1)⌝ }} := by
  wp_match

end wp_match

end pure_tactics
