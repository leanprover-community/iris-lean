/-
Copyright (c) 2026 Klaus Kraßnitzer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Kraßnitzer
-/
module

public import Iris.HeapLang.Interpreter
-- `#eval` elaborates as a `meta` definition, so the constructors must also be
-- imported into the meta environment.
public meta import Iris.HeapLang.Interpreter

@[expose] public section

namespace Iris.Tests.HeapLang

open Iris.HeapLang

/-! # Tests for the HeapLang interpreter

Adapted and extended from Iris's `tests/heap_lang_interpreter.v`, which pins
its output with a `.ref` file; here `#guard_msgs` does the same job. `execState`
additionally shows the final heap and any collected forks.

One test deliberately differs from Rocq's. Rocq's last case is labelled an
infinite loop but never applies the closure it builds, so its `.ref` records a
*value* and the `OutOfFuel` path is left untested upstream; the version here
applies it.
-/

/-! ## Working programs -/

/-- Rocq's `test_1`, checked by kernel reduction. -/
example : exec 1000 hl((λ x, x + #1) #2) = .ok hl_val(#3) := rfl

/-- Kernel reduction reaches through the heap, not just the pure fragment. -/
example : exec 10 hl(!(ref(#1))) = .ok hl_val(#1) := rfl

/-- info:
⇒ #()
  #(loc 1) ↦ #()
  #(loc 2) ↦ #()
-/
#guard_msgs in
#eval execState 1000 hl(
  let x := ref(#());
  let y := ref(#());
  !y)

/-! Evaluation is right to left, so `x ← !y` runs first and the answer is `#2`. -/

/-- info:
⇒ #2
  #(loc 1) ↦ #2
  #(loc 2) ↦ #2
-/
#guard_msgs in
#eval execState 1000 hl(
  let x := ref(#1);
  let y := ref(#2);
  (y ← !x, x ← !y);
  !x)

/-! Allocation starts at location 1. -/

/-- info:
⇒ #(loc 2)
  #(loc 1) ↦ #()
  #(loc 2) ↦ #()
-/
#guard_msgs in
#eval execState 1000 hl(ref(#()); ref(#()))

/-- info:
⇒ #false
  #(loc 1) ↦ #()
  #(loc 2) ↦ #()
-/
#guard_msgs in
#eval execState 1000 hl(
  let x := ref(#());
  let y := ref(#());
  x = y)

/-! The deterministic-allocation blind spot, from Rocq: this succeeds because
the interpreter picks location 1, though other executions of the same program
get stuck. `exec_sound` still holds — one real execution does produce `#2`. -/

/-- info:
⇒ #2
  #(loc 1) ↦ #2
-/
#guard_msgs in
#eval execState 1000 hl(
  let x := ref(#1);
  #(BaseLit.loc ⟨1⟩) ← #2;
  !x)

/-! Forks are collected, never scheduled. -/

/-- info:
⇒ #0
  #(loc 1) ↦ #0
  (1 forked thread(s), not scheduled)
-/
#guard_msgs in
#eval execState 1000 hl(
  let c := ref(#0);
  fork(c ← #1);
  !c)

/-! The read-modify-write operations, which the pure tests above never reach.
Each returns the *old* value and leaves the new one in the heap. -/

/-- info:
⇒ #1
  #(loc 1) ↦ #2
-/
#guard_msgs in
#eval execState 1000 hl(let x := ref(#1); xchg(x, #2))

/-- info:
⇒ #1
  #(loc 1) ↦ #4
-/
#guard_msgs in
#eval execState 1000 hl(let x := ref(#1); faa(x, #3))

/-! `cmpXchg` writes only when the comparison succeeds, and reports whether it
did. -/

/-- info:
⇒ (#1, #true)
  #(loc 1) ↦ #9
-/
#guard_msgs in
#eval execState 1000 hl(let x := ref(#1); cmpXchg(x, #1, #9))

/-- info:
⇒ (#1, #false)
  #(loc 1) ↦ #1
-/
#guard_msgs in
#eval execState 1000 hl(let x := ref(#1); cmpXchg(x, #7, #9))

/-! ## Errors and semantic divergences -/

/-- info:
✗ stuck: load: use after free at location #(loc 1)
  #(loc 1) ↦ <freed>
-/
#guard_msgs in
#eval execState 1000 hl(
  let x := ref(#7);
  free(x);
  !x)

/-- info: ✗ stuck: attempt to call non-function #2 -/
#guard_msgs in
#eval execState 1000 hl(#2 #4)

/-! Comparing a location with an integer is stuck in Rocq too, so this one is
parity, not divergence. -/

example : exec 1000 hl(let x := ref(#()); x < #1)
    = .error (.stuck (.binOpFail .lt (.lit (.loc ⟨1⟩)) (.lit (.int 1)))) := rfl

/-! *This* is the divergence: Rocq's `bin_op_eval_loc` orders two locations,
iris-lean's `BinOp.eval` has no case for it. -/

example : exec 1000 hl(let x := ref(#()); let y := ref(#()); x < y)
    = .error (.stuck (.binOpFail .lt (.lit (.loc ⟨1⟩)) (.lit (.loc ⟨2⟩)))) := rfl

/-! Rocq's `~` is bitwise-not on integers; iris-lean's `UnOp.eval` takes
booleans only. -/

example : exec 100 hl(~ #1) = .error (.stuck (.unOpFail .neg (.lit (.int 1)))) := rfl

example : exec 100 hl(~ #true) = .ok hl_val(#false) := rfl

/-! Pairs are boxed, so equality on them is stuck. -/

/-- info: ✗ stuck: cannot compare (#0, #1) and (#0, #1): pairs are boxed -/
#guard_msgs in
#eval execState 1000 hl((#0, #1) = (#0, #1))

/-! `CmpXchg` on boxed operands reports itself, not a plain `=`. -/

/-- info:
✗ stuck: cmpxchg: cannot compare (#0, #1) and (#0, #1): pairs are boxed
  #(loc 1) ↦ (#0, #1)
-/
#guard_msgs in
#eval execState 1000 hl(let x := ref((#0, #1)); cmpXchg(x, (#0, #1), #2))

/-! ## Every remaining stuck reason

One program per constructor of `StuckReason`, checked against the structured
reason rather than its rendering, so a change to `pretty` cannot mask a change
to which reason is reported. The reasons exercised above are not repeated. -/

example : exec 100 hl(if #1 then #2 else #3)
    = .error (.stuck (.notBool (.lit (.int 1)))) := rfl

example : exec 100 hl(fst(#1)) = .error (.stuck (.notPair .fst (.lit (.int 1)))) := rfl

example : exec 100 hl(snd(#1)) = .error (.stuck (.notPair .snd (.lit (.int 1)))) := rfl

example : exec 100 hl(match #1 with | injl(a) => a | injr(b) => b)
    = .error (.stuck (.notSum (.lit (.int 1)))) := rfl

example : exec 100 hl(!#1) = .error (.stuck (.notLoc .load (.lit (.int 1)))) := rfl

example : exec 100 hl(!#(BaseLit.loc ⟨5⟩))
    = .error (.stuck (.unallocated .load ⟨5⟩)) := rfl

example : exec 100 hl(allocn(#true, #0))
    = .error (.stuck (.allocLenNotInt (.lit (.bool true)))) := rfl

example : exec 100 hl(allocn(#0, #7)) = .error (.stuck (.allocLenNonPos 0)) := rfl

example : exec 100 hl(allocn(#(BaseLit.int (-1)), #7))
    = .error (.stuck (.allocLenNonPos (-1))) := rfl

example : exec 100 hl(let x := ref(#true); faa(x, #1))
    = .error (.stuck (.faaCellNotInt (.lit (.bool true)))) := rfl

example : exec 100 hl(let x := ref(#1); faa(x, #true))
    = .error (.stuck (.faaIncrNotInt (.lit (.bool true)))) := rfl

/-! `free` and `store` report themselves, not `load`. -/

example : exec 100 hl(free(#1)) = .error (.stuck (.notLoc .free (.lit (.int 1)))) := rfl

example : exec 100 hl(#1 ← #2) = .error (.stuck (.notLoc .store (.lit (.int 1)))) := rfl

/-! ## Fuel boundaries

`interpret` spends one unit per recursive call, so the smallest sufficient fuel
pins down the accounting; one less must fail. -/

example : exec 0 hl(#1) = .error .outOfFuel := rfl

example : exec 1 hl(#1) = .ok hl_val(#1) := rfl

example : exec 1 hl(#1 + #1) = .error .outOfFuel := rfl

example : exec 2 hl(#1 + #1) = .ok hl_val(#2) := rfl

/-! iris-lean's own linter also flags this before it ever runs. -/

set_option linter.heapLang.freeVars false in
/-- info: ✗ stuck: free var: x -/
#guard_msgs in
#eval execState 100 hl(x)

/-- info: ✗ out of fuel -/
#guard_msgs in
#eval execState 100 hl((rec foo _ := foo #()) #())

/-- info: ✗ unsupported operation: NewProph -/
#guard_msgs in
#eval execState 100 hl(newProph())

end Iris.Tests.HeapLang
