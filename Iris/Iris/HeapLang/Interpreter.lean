/-
Copyright (c) 2026 Klaus Kraßnitzer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Kraßnitzer
-/
module

public import Iris.HeapLang.Instances
public import Iris.HeapLang.Notation
public import Iris.ProgramLogic.ThreadPool

/-! # A verified interpreter for HeapLang

Ported from Iris's Rocq interpreter (`iris_unstable/heap_lang/interpreter.v`,
tracking issue iris/iris#405). `exec fuel e` runs a closed expression and
returns either its value or a structured `InterpError`.

Like the Rocq version the interpreter is *sequential* and *deterministic*:
forks are collected but never run, and allocation always takes the next fresh
location. Fork-and-forget programs therefore work, but anything that waits on a
forked result — `par`, and so `spawn`/`join` — spins in its busy-wait until the
fuel runs out. See the Rocq header for why this is sound but incomplete.

`exec_sound` and `exec_stuck` are the two informative cases of Rocq's
`exec_spec`, combined back into that shape by `exec_spec` below, and stated
over iris-lean's thread-pool `ReflTransGen ErasedStep`.

Rocq names are given in prose rather than with `@[rocq_alias]`: the porting
tracker covers only the `iris` and `iris_heap_lang` packages, so an alias into
`iris_unstable` would be reported as stale.

Divergences from the Rocq development are documented at their definitions.
-/

@[expose] public section

namespace Iris.HeapLang

open Iris.Std FromMathlib ProgramLogic ProgramLogic.Language ProgramLogic.Language.Notation

/-! ## Errors

Unlike Rocq's string-valued `Stuck`, stuck reasons are structured and rendered
separately (see `StuckReason.pretty`). -/

/-- The heap-accessing expression forms, used to say which one got stuck.
Rocq passes these around as strings. -/
inductive HeapOp where
  | load | free | store | xchg | cmpXchg | faa
deriving Repr, DecidableEq

/-- Which projection of a pair was taken. Rocq passes `"fst"`/`"snd"` as
strings. -/
inductive PairField where
  | fst | snd
deriving Repr, DecidableEq

/-- Why the interpreter says a program is stuck. -/
inductive StuckReason where
  /-- An unbound program variable. -/
  | freeVar (x : String)
  /-- Application of a non-closure. -/
  | notFunction (v : Val)
  /-- `UnOp.eval` returned `none`. -/
  | unOpFail (op : UnOp) (v : Val)
  /-- `BinOp.eval` returned `none`. Covers the `EqOp`-on-boxed-values case. -/
  | binOpFail (op : BinOp) (v₁ v₂ : Val)
  /-- `CmpXchg` on operands that are not safe to compare. Rocq reports this
  through the same path as `binOpFail .eq` but prefixes `"cmpxchg: "`; keeping
  it separate means the two are distinguishable in the returned value, not
  only in the rendered string. -/
  | cmpXchgUnsafe (v₁ v₂ : Val)
  /-- `if` scrutinee is not a boolean. -/
  | notBool (v : Val)
  /-- `fst`/`snd` applied to a non-pair. -/
  | notPair (field : PairField) (v : Val)
  /-- `case` applied to a non-sum. -/
  | notSum (v : Val)
  /-- A heap operation applied to a non-location. -/
  | notLoc (op : HeapOp) (v : Val)
  /-- A heap operation on a location that was freed. -/
  | useAfterFree (op : HeapOp) (l : Loc)
  /-- A heap operation on a location that was never allocated. -/
  | unallocated (op : HeapOp) (l : Loc)
  /-- `AllocN` with a non-integer length. -/
  | allocLenNotInt (v : Val)
  /-- `AllocN` with length `≤ 0`. -/
  | allocLenNonPos (n : Int)
  /-- `FAA` where the heap cell does not hold an integer. -/
  | faaCellNotInt (v : Val)
  /-- `FAA` where the increment is not an integer. -/
  | faaIncrNotInt (v : Val)
deriving Repr, DecidableEq

/-- The three ways `exec` can fail. Only `stuck` comes with a guarantee. -/
inductive InterpError where
  /-- The program really does get stuck; `exec_stuck` says so. -/
  | stuck (reason : StuckReason)
  /-- Prophecy variables. The interpreter is not defined on them. -/
  | unsupported (op : String)
  /-- Fuel exhausted. Says nothing about the program. -/
  | outOfFuel
deriving Repr, DecidableEq

/-! ## The interpreter monad

`ExceptT InterpError (StateM InterpState)` unfolds to
`InterpState → Except InterpError α × InterpState`, so it has the same
state-survives-an-error behaviour as Rocq's bespoke `InterpretM`, but the
instances and monad laws come for free. The inversion lemmas still have to be
proved; see `bind_ok_inv` and friends. -/

/-- Interpreter state: the language state, the allocation counter, and the
forked threads we collect but never run. -/
structure InterpState where
  lang : State
  /-- Every location `≥ nextLoc` is guaranteed unallocated (see `StateWf`). -/
  nextLoc : Int
  forked : List Exp

/-- The interpreter monad: state that survives an error, as in Rocq's bespoke
`InterpretM`. -/
abbrev InterpM := ExceptT InterpError (StateM InterpState)

/-- The empty HeapLang state, Rocq's `init_state`. -/
def initState : State := default

/-- Rocq starts allocating at `1`, so that `#(loc 0)` is always a bad pointer. -/
def InterpState.init : InterpState := ⟨initState, 1, []⟩

/-- The invariant that makes allocation sound: `nextLoc` is past everything
allocated so far. Rocq calls this `state_wf`. -/
def StateWf (s : InterpState) : Prop :=
  ∀ l : Loc, s.nextLoc ≤ l.n → s.lang.get? l = none

theorem StateWf.init : StateWf InterpState.init := by
  intro l _
  simp [InterpState.init, initState, State.get?, PartialMap.get?, default]

/-! ### Primitive interpreter actions -/

/-- Apply `f` to the language state, leaving the interpreter bookkeeping alone. -/
def modifyLang (f : State → State) : InterpM Unit :=
  modify fun s => { s with lang := f s.lang }

/-- Read a projection of the language state. -/
def readLang {α} (f : State → α) : InterpM α := do return f (← get).lang

/-- Abort with a stuck reason. -/
def stuck {α} (r : StuckReason) : InterpM α := throw (.stuck r)

/-- Hand out `n` fresh locations starting at `nextLoc`. -/
def allocLoc (n : Int) : InterpM Loc := do
  let s ← get
  set { s with nextLoc := s.nextLoc + n }
  return ⟨s.nextLoc⟩

/-- Record a forked thread. It is collected, never scheduled. -/
def forkThread (e : Exp) : InterpM Unit :=
  modify fun s => { s with forked := s.forked ++ [e] }

/-- Resolve a location value to a live heap cell. -/
def readLoc (op : HeapOp) (v : Val) : InterpM (Loc × Val) := do
  let .lit (.loc l) := v | stuck (.notLoc op v)
  match ← readLang (State.get? · l) with
  | some (some w) => return (l, w)
  | some none => stuck (.useAfterFree op l)
  | none => stuck (.unallocated op l)

/-! ## The interpreter

Structurally recursive on `fuel`, as in Rocq. HeapLang evaluates **right to
left** (`ECtxItem.appL` holds the argument as a value), so every
two-subexpression case interprets `e₂` first. -/
def interpret : Nat → Exp → InterpM Val
  | 0, _ => throw .outOfFuel
  | fuel + 1, e => do
    let interp := interpret fuel
    match e with
    /- Lambda calculus -/
    | .val v => return v
    | .var x => stuck (.freeVar x)
    | .rec_ f x e => return .rec_ f x e
    | .app e₁ e₂ =>
      let v₂ ← interp e₂
      let f ← interp e₁
      let .rec_ fn x body := f | stuck (.notFunction f)
      interp ((body.subst fn (.rec_ fn x body)).subst x v₂)
    /- Pure operations -/
    | .pair e₁ e₂ =>
      let v₂ ← interp e₂
      let v₁ ← interp e₁
      return .pair v₁ v₂
    | .injL e => return .injL (← interp e)
    | .injR e => return .injR (← interp e)
    | .unop op e =>
      let v ← interp e
      let some v' := op.eval v | stuck (.unOpFail op v)
      return v'
    | .binop op e₁ e₂ =>
      let v₂ ← interp e₂
      let v₁ ← interp e₁
      let some v' := op.eval v₁ v₂ | stuck (.binOpFail op v₁ v₂)
      return v'
    | .if e₀ e₁ e₂ =>
      let c ← interp e₀
      let .lit (.bool b) := c | stuck (.notBool c)
      interp (if b then e₁ else e₂)
    | .fst e =>
      let v ← interp e
      let .pair v₁ _ := v | stuck (.notPair .fst v)
      return v₁
    | .snd e =>
      let v ← interp e
      let .pair _ v₂ := v | stuck (.notPair .snd v)
      return v₂
    | .case e₀ e₁ e₂ =>
      let v ← interp e₀
      match v with
      | .injL w => interp (.app e₁ (.ofVal w))
      | .injR w => interp (.app e₂ (.ofVal w))
      | _ => stuck (.notSum v)
    /- Concurrency: collected, never scheduled -/
    | .fork e =>
      forkThread e
      return .lit .unit
    /- Heap -/
    | .allocN e₁ e₂ =>
      let v ← interp e₂
      let nv ← interp e₁
      let .lit (.int n) := nv | stuck (.allocLenNotInt nv)
      if 0 < n then
        let l ← allocLoc n
        modifyLang (State.initHeap · l n (some v))
        return .lit (.loc l)
      else stuck (.allocLenNonPos n)
    | .load e =>
      let (_, v) ← readLoc .load (← interp e)
      return v
    | .free e =>
      let (l, _) ← readLoc .free (← interp e)
      modifyLang (State.initHeap · l 1 none)
      return .lit .unit
    | .store e₁ e₂ =>
      let w ← interp e₂
      let (l, _) ← readLoc .store (← interp e₁)
      modifyLang (State.initHeap · l 1 (some w))
      return .lit .unit
    | .xchg e₁ e₂ =>
      let w ← interp e₂
      let (l, v) ← readLoc .xchg (← interp e₁)
      modifyLang (State.initHeap · l 1 (some w))
      return v
    | .cmpXchg e₀ e₁ e₂ =>
      let v₂ ← interp e₂
      let v₁ ← interp e₁
      let (l, vl) ← readLoc .cmpXchg (← interp e₀)
      if vl.compareSafe v₁ then
        let b := vl == v₁
        if b then modifyLang (State.initHeap · l 1 (some v₂))
        return .pair vl (.lit (.bool b))
      else stuck (.cmpXchgUnsafe vl v₁)
    | .faa e₁ e₂ =>
      let v ← interp e₂
      let (l, v₀) ← readLoc .faa (← interp e₁)
      let .lit (.int i₁) := v₀ | stuck (.faaCellNotInt v₀)
      let .lit (.int i₂) := v | stuck (.faaIncrNotInt v)
      modifyLang (State.initHeap · l 1 (some (.lit (.int (i₁ + i₂)))))
      return .lit (.int i₁)
    /- Prophecies: out of scope, and flagged as such -/
    | .newProph => throw (.unsupported "NewProph")
    | .resolve _ _ _ => throw (.unsupported "Resolve")

/-- Run `e` from the empty heap, keeping the final interpreter state. -/
def run (fuel : Nat) (e : Exp) : Except InterpError Val × InterpState :=
  interpret fuel e InterpState.init

/-- Run `e` from the empty heap. The Rocq `exec`. -/
def exec (fuel : Nat) (e : Exp) : Except InterpError Val :=
  (run fuel e).1

/-! ## Rendering

Presentation only; nothing below is used by the proofs. -/

/-- Render a binder as it appears in surface syntax. -/
def Binder.pretty : Binder → String
  | .anon => "_"
  | .named x => x

/-- Render a literal as it appears in surface syntax. -/
def BaseLit.pretty : BaseLit → String
  | .int n => "#" ++ toString n
  | .bool b => if b then "#true" else "#false"
  | .unit => "#()"
  | .poison => "#poison"
  | .loc l => s!"#(loc {l.n})"
  | .prophecy p => s!"#(proph {p.n})"

/-- Closure bodies are elided: the `hl(...)` delaborators run on syntax, not on
runtime values. -/
def Val.pretty : Val → String
  | .lit l => l.pretty
  | .rec_ f x _ => s!"(rec {f.pretty} {x.pretty} := …)"
  | .pair v₁ v₂ => s!"({v₁.pretty}, {v₂.pretty})"
  | .injL v => s!"injl({v.pretty})"
  | .injR v => s!"injr({v.pretty})"

scoped instance : ToString Val := ⟨Val.pretty⟩

/-- Rocq's `explain_unboxed`: why a value cannot participate in `EqOp`. Kept to
a short noun phrase so that `StuckReason.pretty` can name both operands and
still fit on a line. -/
def Val.explainBoxed : Val → Option String
  | .lit .poison | .injL (.lit .poison) | .injR (.lit .poison) =>
    some "poison is incomparable"
  | .lit (.prophecy _) | .injL (.lit (.prophecy _)) | .injR (.lit (.prophecy _)) =>
    some "prophecies are incomparable"
  | .lit _ | .injL (.lit _) | .injR (.lit _) => none
  | .injL _ | .injR _ => some "sums are boxed unless they hold a literal"
  | .pair _ _ => some "pairs are boxed"
  | .rec_ .. => some "closures are incomparable"

/-- Render the offending operands of a failed comparison. Identical
explanations are given once rather than repeated per operand. -/
def explainPair (v₁ v₂ : Val) (m₁ m₂ : String) : String :=
  if m₁ == m₂ then m₁ else s!"{v₁}: {m₁}; {v₂}: {m₂}"

/-- Render the heap operation as it is spelled in surface syntax. -/
def HeapOp.pretty : HeapOp → String
  | .load => "load" | .free => "free" | .store => "store"
  | .xchg => "xchg" | .cmpXchg => "cmpxchg" | .faa => "faa"

/-- Render the projection as it is spelled in surface syntax. -/
def PairField.pretty : PairField → String
  | .fst => "fst" | .snd => "snd"

/-- Render a unary operator as it appears in surface syntax. -/
def UnOp.pretty : UnOp → String
  | .neg => "~" | .minus => "unary -"

/-- Render a binary operator as it appears in surface syntax. -/
def BinOp.pretty : BinOp → String
  | .plus => "+" | .minus => "-" | .mult => "*" | .tdiv => "/" | .tmod => "%"
  | .and => "&&&" | .or => "|||" | .xor => "^^^"
  | .shiftl => "<<<" | .shiftr => ">>>"
  | .le => "≤" | .lt => "<" | .eq => "="
  | .offset => "+ₗ"

/-- Render a stuck reason. Rocq builds these strings inside the interpreter;
here the reason is structured and only rendered on the way out. -/
def StuckReason.pretty : StuckReason → String
  | .freeVar x => s!"free var: {x}"
  | .notFunction v => s!"attempt to call non-function {v}"
  | .unOpFail op v =>
    match op with
    -- Unlike Rocq, iris-lean's `.neg` accepts only booleans.
    | .neg => s!"~ can only be applied to booleans, got {v}"
    | .minus => s!"unary - can only be applied to integers, got {v}"
  | .binOpFail .eq v₁ v₂ =>
    match v₁.explainBoxed, v₂.explainBoxed with
    | some m₁, some m₂ =>
      s!"cannot compare {v₁} and {v₂}: {explainPair v₁ v₂ m₁ m₂}"
    | _, _ => s!"cannot compare {v₁} and {v₂}"
  -- Unlike Rocq, iris-lean has no `bin_op_eval_loc`: two locations cannot be
  -- ordered. Rocq rejects location-vs-integer ordering too.
  | .binOpFail op v₁ v₂ =>
    match v₁, op with
    | .lit (.loc _), .le | .lit (.loc _), .lt =>
      s!"locations cannot be ordered: {op.pretty} does not apply to {v₁} and {v₂}"
    | .lit (.loc _), .offset => s!"can only offset a location by an integer, got {v₂}"
    | .lit (.loc _), _ =>
      s!"the only operations on locations are +ₗ and =; got {op.pretty}"
    | _, _ => s!"{op.pretty} does not apply to {v₁} and {v₂}"
  | .cmpXchgUnsafe v₁ v₂ =>
    match v₁.explainBoxed, v₂.explainBoxed with
    | some m₁, some m₂ =>
      s!"cmpxchg: cannot compare {v₁} and {v₂}: {explainPair v₁ v₂ m₁ m₂}"
    | _, _ => s!"cmpxchg: cannot compare {v₁} and {v₂}"
  | .notBool v => s!"if: non-bool condition {v}"
  | .notPair field v => s!"{field.pretty}: called on non-pair {v}"
  | .notSum v => s!"case: called on non-sum {v}"
  | .notLoc op v => s!"{op.pretty}: applied to non-loc {v}"
  | .useAfterFree op l => s!"{op.pretty}: use after free at location #(loc {l.n})"
  | .unallocated op l => s!"{op.pretty}: unallocated location #(loc {l.n})"
  | .allocLenNotInt v => s!"alloc: number of elements (first argument) {v}"
  | .allocLenNonPos n =>
    if n == 0 then "alloc: cannot allocate 0 elements"
    else s!"alloc: negative number of elements (first argument) {n}"
  | .faaCellNotInt v => s!"faa: called on non-integer heap value {v}"
  | .faaIncrNotInt v => s!"faa: increment {v} is not an integer"

/-- Render an error. -/
def InterpError.pretty : InterpError → String
  | .stuck r => "stuck: " ++ r.pretty
  | .unsupported op => "unsupported operation: " ++ op
  | .outOfFuel => "out of fuel"

scoped instance : ToString InterpError := ⟨InterpError.pretty⟩

/-- A run's outcome together with its final state, for interactive display. -/
structure ExecResult where
  value : Except InterpError Val
  final : InterpState

/-- Render a run's outcome, its heap, and how many threads it forked. -/
def ExecResult.pretty (r : ExecResult) : String :=
  let head := match r.value with
    | .ok v => s!"⇒ {v}"
    | .error e => s!"✗ {e}"
  let cells := r.final.lang.heap.toList.map fun (l, mv) =>
    s!"\n  #(loc {l.n}) ↦ " ++ (match mv with | some v => v.pretty | none => "<freed>")
  let forks := if r.final.forked.isEmpty then ""
    else s!"\n  ({r.final.forked.length} forked thread(s), not scheduled)"
  head ++ String.join cells ++ forks

instance : Repr ExecResult := ⟨fun r _ => .text r.pretty⟩

/-- `#eval`-friendly entry point: run `e` and show the heap it leaves behind. -/
def execState (fuel : Nat) (e : Exp) : ExecResult :=
  let (v, s) := run fuel e
  ⟨v, s⟩

/-! ## Correctness

Rocq's `exec_spec` splits into `exec_sound` and `exec_stuck`, both stated over
`ReflTransGen ErasedStep` — the thread-pool relation core Iris's `adequacy.v`
quantifies over, so an interpreter run and a weakest-precondition proof speak
about the same transition system. -/

/-! ### The allocation invariant

`allocNS`'s freshness premise is discharged by `StateWf` itself (via
`StateWf.alloc`), not by `Semantics.lean`'s `exists_fresh_block`, which only
provides *some* fresh block. `PreservesWf` is closed under `bind`, so all but
the heap cases are plumbing. -/

private theorem StateWf.lt_nextLoc {s : InterpState} {l : Loc} {w : Option Val}
    (hwf : StateWf s) (hlive : s.lang.get? l = some w) : l.n < s.nextLoc := by
  by_cases h : s.nextLoc ≤ l.n
  · rw [hwf l h] at hlive; simp at hlive
  · omega

/-- Reading a cell out of a freshly written block: inside the block you get the
written value, outside it the heap is unchanged. -/
private theorem State.get?_initHeap (σ : State) (l : Loc) (n : Int) (w : Option Val) (k : Loc) :
    (σ.initHeap l n w).get? k
      = if (∃ i, i < n.toNat ∧ k = l + (i : Int)) then some w else σ.get? k :=
  get?_foldl_insert l w σ.heap n.toNat k

/-- A location at or past `nextLoc` is not in a block written at `base`, given
that the whole block sits below `nextLoc`. Shared by the two `StateWf`
preservation lemmas. -/
private theorem not_mem_block {base : Loc} {n : Int} {k : Loc}
    (h : ∀ i : Nat, i < n.toNat → k.n ≠ base.n + (i : Int)) :
    ¬ ∃ i, i < n.toNat ∧ k = base + (i : Int) := by
  rintro ⟨i, hi, rfl⟩
  exact h i hi (by simp only [loc_add_n])

/-- Writing a single cell that is already allocated keeps the invariant. -/
theorem StateWf.initHeap_of_live {s : InterpState} {l : Loc} {w w' : Option Val}
    (hwf : StateWf s) (hlive : s.lang.get? l = some w) :
    StateWf { s with lang := s.lang.initHeap l 1 w' } := by
  intro k hk
  show (s.lang.initHeap l 1 w').get? k = none
  simp only at hk
  have hl := hwf.lt_nextLoc hlive
  rw [State.get?_initHeap, if_neg (not_mem_block fun i hi => by omega)]
  exact hwf k hk

/-- Allocating at `nextLoc` and advancing it past the block preserves `StateWf`. -/
theorem StateWf.alloc {s : InterpState} {n : Int} {v : Option Val}
    (hwf : StateWf s) (hn : 0 < n) :
    StateWf { lang := s.lang.initHeap (Loc.mk s.nextLoc) n v,
              nextLoc := s.nextLoc + n, forked := s.forked } := by
  intro k hk
  show (s.lang.initHeap (Loc.mk s.nextLoc) n v).get? k = none
  simp only at hk
  rw [State.get?_initHeap, if_neg (not_mem_block fun i hi => by simp only []; omega)]
  exact hwf k (by omega)

private theorem bind_ok {α β} (x : InterpM α) (f : α → InterpM β)
    (s sx : InterpState) (a : α)
    (h : x s = (.ok a, sx)) : (x >>= f) s = f a sx := by
  simp [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, h]

private theorem bind_error {α β}
    (x : InterpM α) (f : α → InterpM β) (s sx : InterpState) (er : InterpError)
    (h : x s = (.error er, sx)) : (x >>= f) s = (.error er, sx) := by
  simp [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, h]
  rfl

private theorem readLang_bind {α β : Type} (f : State → α) (k : α → InterpM β)
    (s : InterpState) :
    (readLang f >>= k) s = k (f s.lang) s :=
  bind_ok (readLang f) k s s (f s.lang) rfl

def PreservesWf {α} (x : InterpM α) : Prop := ∀ s, StateWf s → StateWf (x s).2

theorem PreservesWf.pure {α} (a : α) : PreservesWf (Pure.pure a : InterpM α) := fun _ h => h
theorem PreservesWf.throw {α} (er : InterpError) :
    PreservesWf (throw er : InterpM α) := fun _ h => h
theorem PreservesWf.stuck {α} (r : StuckReason) :
    PreservesWf (stuck r : InterpM α) := fun _ h => h
theorem PreservesWf.forkThread (e : Exp) : PreservesWf (forkThread e) := fun _ h => h

theorem PreservesWf.bind {α β} {x : InterpM α} {f : α → InterpM β}
    (hx : PreservesWf x) (hf : ∀ a, PreservesWf (f a)) : PreservesWf (x >>= f) := by
  intro s hwf
  have hxs := hx s hwf
  rcases hx' : x s with ⟨rx, sx⟩
  rw [hx'] at hxs
  cases rx with
  | ok a => rw [bind_ok x f s sx a hx']; exact hf a sx hxs
  | error er => rw [bind_error x f s sx er hx']; exact hxs

private theorem stuck_ne_ok {α} {r : StuckReason} {s : InterpState} {a : α} {s' : InterpState}
    (h : (stuck r : InterpM α) s = (.ok a, s')) : False := by
  have h2 : (Except.error (InterpError.stuck r) : Except InterpError α) = .ok a :=
    congrArg Prod.fst h
  simp at h2

/-- A successful `readLoc` leaves the state alone and certifies the cell live. -/
theorem readLoc_ok_inv {op : HeapOp} {v : Val} {s s' : InterpState} {l : Loc} {w : Val}
    (h : readLoc op v s = (.ok (l, w), s')) :
    v = .lit (.loc l) ∧ s' = s ∧ s.lang.get? l = some (some w) := by
  unfold readLoc at h
  split at h
  next l' =>
    rw [readLang_bind] at h
    rcases hg : s.lang.get? l' with _ | (_ | w')
    · rw [hg] at h; exact absurd h stuck_ne_ok
    · rw [hg] at h; exact absurd h stuck_ne_ok
    · rw [hg] at h
      have h2 : ((Except.ok (l', w') : Except InterpError (Loc × Val)), s) = (.ok (l, w), s') := h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h2
      obtain ⟨⟨hl, hw'⟩, hs⟩ := h2
      subst hl; subst hw'
      exact ⟨rfl, hs.symm, hg⟩
  next => exact absurd h stuck_ne_ok

private theorem readLoc_state (op : HeapOp) (v : Val) (s : InterpState) :
    (readLoc op v s).2 = s := by
  unfold readLoc
  split
  next l' =>
    rw [readLang_bind]
    rcases hg : s.lang.get? l' with _ | (_ | w') <;> rfl
  next => rfl

/-- `readLoc` only reads, so it cannot break the invariant. -/
theorem PreservesWf.of_readLoc (op : HeapOp) (v : Val) : PreservesWf (readLoc op v) := by
  intro s hwf; rw [readLoc_state]; exact hwf

private theorem modifyLang_bind {β : Type}
    (f : State → State) (k : Unit → InterpM β) (s : InterpState) :
    (modifyLang f >>= k) s = k () { s with lang := f s.lang } :=
  bind_ok (modifyLang f) k s { s with lang := f s.lang } () rfl

private theorem allocLoc_bind {β : Type} (n : Int) (k : Loc → InterpM β) (s : InterpState) :
    (allocLoc n >>= k) s = k (Loc.mk s.nextLoc) { s with nextLoc := s.nextLoc + n } :=
  bind_ok (allocLoc n) k s _ _ rfl

/-- `StateWf` preservation given that `l` is live holding `w`. Stated on the
*unapplied* computation: the heap cases end in `(match v with ...) s`, and
`split` cannot see a match under an application. -/
def PreservesWfAt (l : Loc) (w : Val) {β : Type} (x : InterpM β) : Prop :=
  ∀ s, StateWf s → s.lang.get? l = some (some w) → StateWf (x s).2

theorem PreservesWfAt.stuck {l w} {β : Type} (r : StuckReason) :
    PreservesWfAt l w (stuck r : InterpM β) := fun _ h _ => h

theorem PreservesWfAt.pure {l w} {β : Type} (a : β) :
    PreservesWfAt l w (Pure.pure a : InterpM β) := fun _ h _ => h

/-- Overwriting a cell `readLoc` certified live preserves `StateWf`. -/
theorem PreservesWfAt.write_pure {l w} {β : Type} (w' : Option Val) (a : β) :
    PreservesWfAt l w (modifyLang (State.initHeap · l 1 w') >>= fun _ => Pure.pure a) := by
  intro s hwf hlive
  rw [modifyLang_bind]
  exact StateWf.initHeap_of_live hwf hlive

theorem PreservesWf.readLoc_bind {β : Type} (op : HeapOp) (vl : Val)
    (f : Loc × Val → InterpM β)
    (hf : ∀ l w, PreservesWfAt l w (f (l, w))) : PreservesWf (readLoc op vl >>= f) := by
  intro s hwf
  rcases hr : readLoc op vl s with ⟨rr, sr⟩
  have hsr : sr = s := by have h := readLoc_state op vl s; rw [hr] at h; exact h
  cases rr with
  | error er => rw [bind_error _ _ s sr er hr]; rw [hsr]; exact hwf
  | ok p =>
    obtain ⟨l, w⟩ := p
    obtain ⟨_, _, hlive⟩ := readLoc_ok_inv hr
    rw [bind_ok _ _ s sr (l, w) hr, hsr]
    exact hf l w s hwf hlive

theorem interpret_preservesWf (fuel : Nat) : ∀ e : Exp, PreservesWf (interpret fuel e) := by
  induction fuel with
  | zero => intro e; exact PreservesWf.throw _
  | succ fuel ih =>
    intro e
    cases e with
    | val v => simp only [interpret]; exact PreservesWf.pure _
    | var x => simp only [interpret]; exact PreservesWf.stuck _
    | rec_ f x b => simp only [interpret]; exact PreservesWf.pure _
    | app e1 e2 =>
      simp only [interpret]
      refine .bind (ih e2) fun v2 => ?_
      refine .bind (ih e1) fun f => ?_
      split
      · exact ih _
      · exact PreservesWf.stuck _
    | unop op e =>
      simp only [interpret]
      refine .bind (ih e) fun v => ?_
      split <;> first | exact PreservesWf.pure _ | exact PreservesWf.stuck _
    | binop op e1 e2 =>
      simp only [interpret]
      refine .bind (ih e2) fun v2 => ?_
      refine .bind (ih e1) fun v1 => ?_
      split <;> first | exact PreservesWf.pure _ | exact PreservesWf.stuck _
    | «if» e0 e1 e2 =>
      simp only [interpret]
      refine .bind (ih e0) fun c => ?_
      split <;> first | exact ih _ | exact PreservesWf.stuck _
    | pair e1 e2 =>
      simp only [interpret]
      refine .bind (ih e2) fun v2 => ?_
      refine .bind (ih e1) fun v1 => ?_
      exact PreservesWf.pure _
    | fst e | snd e =>
      simp only [interpret]
      refine .bind (ih e) fun v => ?_
      split <;> first | exact PreservesWf.pure _ | exact PreservesWf.stuck _
    | injL e | injR e =>
      simp only [interpret]
      refine .bind (ih e) fun v => ?_
      exact PreservesWf.pure _
    | case e0 e1 e2 =>
      simp only [interpret]
      refine .bind (ih e0) fun v => ?_
      split <;> first | exact ih _ | exact PreservesWf.stuck _
    | fork e =>
      simp only [interpret]
      refine .bind (PreservesWf.forkThread e) fun _ => ?_
      exact PreservesWf.pure _
    | load e =>
      simp only [interpret]
      refine .bind (ih e) fun vl => ?_
      refine .bind (PreservesWf.of_readLoc _ _) fun p => ?_
      exact PreservesWf.pure _
    | newProph => simp only [interpret]; exact PreservesWf.throw _
    | resolve e0 e1 e2 => simp only [interpret]; exact PreservesWf.throw _
    | allocN e1 e2 =>
      simp only [interpret]
      refine .bind (ih e2) fun v => ?_
      refine .bind (ih e1) fun nv => ?_
      split
      · next n =>
        split
        · next hn =>
          intro s hwf
          rw [allocLoc_bind, modifyLang_bind]
          exact StateWf.alloc hwf hn
        · exact PreservesWf.stuck _
      · exact PreservesWf.stuck _
    | free e =>
      simp only [interpret]
      refine .bind (ih e) fun vl => ?_
      refine PreservesWf.readLoc_bind _ _ _ fun l w0 => ?_
      exact PreservesWfAt.write_pure _ _
    | store e1 e2 =>
      simp only [interpret]
      refine .bind (ih e2) fun w => ?_
      refine .bind (ih e1) fun vl => ?_
      refine PreservesWf.readLoc_bind _ _ _ fun l w0 => ?_
      exact PreservesWfAt.write_pure _ _
    | xchg e1 e2 =>
      simp only [interpret]
      refine .bind (ih e2) fun w => ?_
      refine .bind (ih e1) fun vl => ?_
      refine PreservesWf.readLoc_bind _ _ _ fun l w0 => ?_
      exact PreservesWfAt.write_pure _ _
    | cmpXchg e0 e1 e2 =>
      simp only [interpret]
      refine .bind (ih e2) fun v2 => ?_
      refine .bind (ih e1) fun v1 => ?_
      refine .bind (ih e0) fun vl0 => ?_
      refine PreservesWf.readLoc_bind _ _ _ fun l w0 => ?_
      dsimp only
      split
      · split
        · exact PreservesWfAt.write_pure _ _
        · exact PreservesWfAt.pure _
      · exact PreservesWfAt.stuck _
    | faa e1 e2 =>
      simp only [interpret]
      refine .bind (ih e2) fun v => ?_
      refine .bind (ih e1) fun vl => ?_
      refine PreservesWf.readLoc_bind _ _ _ fun l w0 => ?_
      dsimp only
      split <;>
        first
          | exact PreservesWfAt.stuck _
          | (split <;>
              first
                | exact PreservesWfAt.write_pure _ _
                | exact PreservesWfAt.stuck _)

/-- `StateWf` is preserved on success *and* failure, strengthening Rocq's
success-only `interpret_wf`. -/
theorem interpret_wf {fuel : Nat} {e : Exp} {s s' : InterpState} {r : Except InterpError Val}
    (hwf : StateWf s) (h : interpret fuel e s = (r, s')) : StateWf s' := by
  simpa [h] using interpret_preservesWf fuel e s hwf

/-- Reflexive-transitive single-thread stepping with accumulated forks, with the
observations existentially erased.

Upstream `PrimSteps` is transitive-only, so zero-step facts — which every `Val`
case of `interpret_sound` needs — cannot be stated in it. Rather than re-derive
the transitive part, this adds reflexivity on top and inherits `fill` and the
configuration-level lifting from `PrimSteps.fill` and `cfg_steps`. -/
def Steps (e₁ : Exp) (σ₁ : State) (e₂ : Exp) (σ₂ : State) (efs : List Exp) : Prop :=
  (e₁ = e₂ ∧ σ₁ = σ₂ ∧ efs = []) ∨ ∃ κ, PrimSteps e₁ σ₁ κ e₂ σ₂ efs

/-- Transitivity of upstream `PrimSteps`, which `ThreadPool.lean` does not
provide. Nothing here is HeapLang-specific; it belongs beside `PrimSteps.fill`. -/
theorem primSteps_trans {e₁ e₂ e₃ : Exp} {σ₁ σ₂ σ₃ : State}
    {κ₁ κ₂ : List Observation} {efs₁ efs₂ : List Exp}
    (h₁ : PrimSteps e₁ σ₁ κ₁ e₂ σ₂ efs₁)
    (h₂ : PrimSteps e₂ σ₂ κ₂ e₃ σ₃ efs₂) :
    PrimSteps e₁ σ₁ (κ₁ ++ κ₂) e₃ σ₃ (efs₁ ++ efs₂) := by
  induction h₁ with
  | once hs => exact .next hs h₂
  | next hs _ ih => simpa [List.append_assoc] using PrimSteps.next hs (ih h₂)

theorem Steps.refl {e : Exp} {σ : State} : Steps e σ e σ [] := .inl ⟨rfl, rfl, rfl⟩

theorem Steps.single {e₁ σ₁ κ e₂ σ₂ efs} (h : (e₁, σ₁) -<κ>-> (e₂, σ₂, efs)) :
    Steps e₁ σ₁ e₂ σ₂ efs := .inr ⟨κ, .once h⟩

theorem Steps.trans {e₁ σ₁ e₂ σ₂ efs₁ e₃ σ₃ efs₂}
    (h₁ : Steps e₁ σ₁ e₂ σ₂ efs₁) (h₂ : Steps e₂ σ₂ e₃ σ₃ efs₂) :
    Steps e₁ σ₁ e₃ σ₃ (efs₁ ++ efs₂) := by
  rcases h₁ with ⟨rfl, rfl, rfl⟩ | ⟨_, hs₁⟩
  · simpa using h₂
  rcases h₂ with ⟨rfl, rfl, rfl⟩ | ⟨_, hs₂⟩
  · simp only [List.append_nil]; exact .inr ⟨_, hs₁⟩
  exact .inr ⟨_, primSteps_trans hs₁ hs₂⟩

theorem Steps.fill {K : Exp → Exp} [Context K] {e₁ σ₁ e₂ σ₂ efs}
    (h : Steps e₁ σ₁ e₂ σ₂ efs) : Steps (K e₁) σ₁ (K e₂) σ₂ efs := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨_, hs⟩
  · exact .refl
  exact .inr ⟨_, hs.fill⟩

/-- Lifting through a single evaluation-context frame. -/
theorem Steps.fillItem (Ki : ECtxItem) {e₁ σ₁ e₂ σ₂ efs}
    (h : Steps e₁ σ₁ e₂ σ₂ efs) : Steps (Ki.fill e₁) σ₁ (Ki.fill e₂) σ₂ efs :=
  Steps.fill (K := EvContext.fill [Ki]) h

/-- Lift `Steps` to thread-pool erased steps; the only place the configuration
level appears. -/
theorem Steps.to_cfg {e σ e' σ' efs} (h : Steps e σ e' σ' efs) (tp : List Exp) :
    (e :: tp, σ) -·->ₜₚ* (e' :: tp ++ efs, σ') := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨_, hs⟩
  · simpa using Relation.ReflTransGen.refl (r := ErasedStep (Expr := Exp))
  simpa using cfg_steps (tp := e :: tp) (n := 0) (by simp) hs

theorem Steps.of_baseStep {e σ e' σ' efs} (h : BaseStep e σ [] e' σ' efs) :
    Steps e σ e' σ' efs :=
  Steps.single (EctxLanguage.primStep_of_baseStep h)

/-- Rocq's `interp_bind_inl_inv`. -/
theorem bind_ok_inv {α β} {x : InterpM α} {f : α → InterpM β} {s s' : InterpState} {b : β}
    (h : (x >>= f) s = (.ok b, s')) :
    ∃ a sx, x s = (.ok a, sx) ∧ f a sx = (.ok b, s') := by
  obtain ⟨rx, sx, hx⟩ : ∃ rx sx, x s = (rx, sx) := ⟨(x s).1, (x s).2, rfl⟩
  cases rx with
  | ok a =>
    refine ⟨a, sx, hx, ?_⟩
    rw [bind_ok x f s sx a hx] at h
    exact h
  | error er =>
    rw [bind_error x f s sx er hx] at h
    have h2 : (Except.error er : Except InterpError β) = .ok b := congrArg Prod.fst h
    simp at h2

private theorem forkThread_bind {β : Type} (e : Exp) (k : Unit → InterpM β) (s : InterpState) :
    (forkThread e >>= k) s = k () { s with forked := s.forked ++ [e] } :=
  bind_ok (forkThread e) k s _ () rfl

private theorem pure_ok_inv {α} {a b : α} {s s' : InterpState}
    (h : (Pure.pure a : InterpM α) s = (.ok b, s')) : a = b ∧ s = s' := by
  have h1 : (Except.ok a : Except InterpError α) = .ok b := congrArg Prod.fst h
  have h2 : s = s' := congrArg Prod.snd h
  exact ⟨by simpa using h1, h2⟩

private theorem throw_ne_ok {α} {er : InterpError} {s : InterpState} {a : α} {s' : InterpState}
    (h : (throw er : InterpM α) s = (.ok a, s')) : False := by
  have h2 : (Except.error er : Except InterpError α) = .ok a := congrArg Prod.fst h
  simp at h2

/-- A successful run corresponds to `Steps` and appends exactly its forks.
Stronger than Rocq's `interpret_sound`, which states the forked pool as the
interpreter's own field rather than as a difference. -/
theorem interpret_sound (fuel : Nat) :
    ∀ (e : Exp) (s : InterpState) (v : Val) (s' : InterpState),
      StateWf s → interpret fuel e s = (.ok v, s') →
      ∃ efs, s'.forked = s.forked ++ efs ∧ Steps e s.lang (Exp.ofVal v) s'.lang efs := by
  induction fuel with
  | zero => intro e s v s' _ h; exact absurd h throw_ne_ok
  | succ fuel ih =>
    intro e s v s' hwf h
    cases e with
    | val w =>
      simp only [interpret] at h
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h
      exact ⟨[], by simp, Steps.refl⟩
    | var x => simp only [interpret] at h; exact absurd h stuck_ne_ok
    | rec_ f x b =>
      simp only [interpret] at h
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h
      exact ⟨[], by simp, Steps.of_baseStep (BaseStep.recS f x b _)⟩
    | app e1 e2 =>
      simp only [interpret] at h
      obtain ⟨v2, s1, h2, h⟩ := bind_ok_inv h
      obtain ⟨f, s2, h1, h⟩ := bind_ok_inv h
      obtain ⟨efs2, hf2, st2⟩ := ih e2 s v2 s1 hwf h2
      have hwf1 := interpret_wf hwf h2
      obtain ⟨efs1, hf1, st1⟩ := ih e1 s1 f s2 hwf1 h1
      have hwf2 := interpret_wf hwf1 h1
      cases f with
      | rec_ fn x body =>
        obtain ⟨efs3, hf3, st3⟩ := ih _ s2 v s' hwf2 h
        refine ⟨efs2 ++ efs1 ++ efs3, by rw [hf3, hf1, hf2]; simp, ?_⟩
        have c2 := Steps.fillItem (.appR e1) st2
        have c1 := Steps.fillItem (.appL v2) st1
        have cb : Steps (.app (.ofVal (.rec_ fn x body)) (.ofVal v2)) s2.lang
            ((body.subst fn (.rec_ fn x body)).subst x v2) s2.lang [] :=
          Steps.of_baseStep (BaseStep.betaS fn x body v2 _ _ rfl)
        simpa [ECtxItem.fill] using ((c2.trans c1).trans cb).trans st3
      | _ => exact absurd h stuck_ne_ok
    | unop op e =>
      simp only [interpret] at h
      obtain ⟨w, s1, he, h⟩ := bind_ok_inv h
      obtain ⟨efs1, hf1, st1⟩ := ih e s w s1 hwf he
      rcases hev : op.eval w with _ | w'
      · rw [hev] at h; exact absurd h stuck_ne_ok
      · rw [hev] at h
        obtain ⟨rfl, rfl⟩ := pure_ok_inv h
        refine ⟨efs1, hf1, ?_⟩
        simpa [ECtxItem.fill] using (Steps.fillItem (.unOp op) st1).trans
          (Steps.of_baseStep (BaseStep.unOpS op w w' s1.lang hev))
    | binop op e1 e2 =>
      simp only [interpret] at h
      obtain ⟨v2, s1, h2, h⟩ := bind_ok_inv h
      obtain ⟨v1, s2, h1, h⟩ := bind_ok_inv h
      obtain ⟨efs2, hf2, st2⟩ := ih e2 s v2 s1 hwf h2
      have hwf1 := interpret_wf hwf h2
      obtain ⟨efs1, hf1, st1⟩ := ih e1 s1 v1 s2 hwf1 h1
      rcases hev : op.eval v1 v2 with _ | v'
      · rw [hev] at h; exact absurd h stuck_ne_ok
      · rw [hev] at h
        obtain ⟨rfl, rfl⟩ := pure_ok_inv h
        refine ⟨efs2 ++ efs1, by rw [hf1, hf2]; simp, ?_⟩
        simpa [ECtxItem.fill] using
          ((Steps.fillItem (.binOpR op e1) st2).trans
            (Steps.fillItem (.binOpL op v2) st1)).trans
            (Steps.of_baseStep (BaseStep.binOpS op v1 v2 v' s2.lang hev))
    | «if» e0 e1 e2 =>
      simp only [interpret] at h
      obtain ⟨c, s1, h0, h⟩ := bind_ok_inv h
      obtain ⟨efs0, hf0, st0⟩ := ih e0 s c s1 hwf h0
      have hwf1 := interpret_wf hwf h0
      cases c with
      | lit bl =>
        cases bl with
        | bool b =>
          obtain ⟨efs1, hf1, st1⟩ := ih _ s1 v s' hwf1 h
          refine ⟨efs0 ++ efs1, by rw [hf1, hf0]; simp, ?_⟩
          have cc := Steps.fillItem (.if e1 e2) st0
          have cb : Steps (.if (.ofVal (.lit (.bool b))) e1 e2) s1.lang
              (if b then e1 else e2) s1.lang [] := by
            cases b
            · exact Steps.of_baseStep (BaseStep.ifFalseS e1 e2 _)
            · exact Steps.of_baseStep (BaseStep.ifTrueS e1 e2 _)
          simpa [ECtxItem.fill] using (cc.trans cb).trans st1
        | _ => exact absurd h stuck_ne_ok
      | _ => exact absurd h stuck_ne_ok
    | pair e1 e2 =>
      simp only [interpret] at h
      obtain ⟨v2, s1, h2, h⟩ := bind_ok_inv h
      obtain ⟨v1, s2, h1, h⟩ := bind_ok_inv h
      obtain ⟨efs2, hf2, st2⟩ := ih e2 s v2 s1 hwf h2
      have hwf1 := interpret_wf hwf h2
      obtain ⟨efs1, hf1, st1⟩ := ih e1 s1 v1 s2 hwf1 h1
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h
      refine ⟨efs2 ++ efs1, by rw [hf1, hf2]; simp, ?_⟩
      simpa [ECtxItem.fill] using
        ((Steps.fillItem (.pairR e1) st2).trans
          (Steps.fillItem (.pairL v2) st1)).trans
          (Steps.of_baseStep (BaseStep.pairS v1 v2 s2.lang))
    | fst e =>
      simp only [interpret] at h
      obtain ⟨w, s1, he, h⟩ := bind_ok_inv h
      obtain ⟨efs1, hf1, st1⟩ := ih e s w s1 hwf he
      cases w with
      | pair a b =>
        obtain ⟨rfl, rfl⟩ := pure_ok_inv h
        refine ⟨efs1, hf1, ?_⟩
        simpa [ECtxItem.fill] using (Steps.fillItem .fst st1).trans
          (Steps.of_baseStep (BaseStep.fstS a b s1.lang))
      | _ => exact absurd h stuck_ne_ok
    | snd e =>
      simp only [interpret] at h
      obtain ⟨w, s1, he, h⟩ := bind_ok_inv h
      obtain ⟨efs1, hf1, st1⟩ := ih e s w s1 hwf he
      cases w with
      | pair a b =>
        obtain ⟨rfl, rfl⟩ := pure_ok_inv h
        refine ⟨efs1, hf1, ?_⟩
        simpa [ECtxItem.fill] using (Steps.fillItem .snd st1).trans
          (Steps.of_baseStep (BaseStep.sndS a b s1.lang))
      | _ => exact absurd h stuck_ne_ok
    | injL e =>
      simp only [interpret] at h
      obtain ⟨w, s1, he, h⟩ := bind_ok_inv h
      obtain ⟨efs1, hf1, st1⟩ := ih e s w s1 hwf he
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h
      refine ⟨efs1, hf1, ?_⟩
      simpa [ECtxItem.fill] using (Steps.fillItem .injL st1).trans
        (Steps.of_baseStep (BaseStep.injLS w s1.lang))
    | injR e =>
      simp only [interpret] at h
      obtain ⟨w, s1, he, h⟩ := bind_ok_inv h
      obtain ⟨efs1, hf1, st1⟩ := ih e s w s1 hwf he
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h
      refine ⟨efs1, hf1, ?_⟩
      simpa [ECtxItem.fill] using (Steps.fillItem .injR st1).trans
        (Steps.of_baseStep (BaseStep.injRS w s1.lang))
    | case e0 e1 e2 =>
      simp only [interpret] at h
      obtain ⟨w, s1, h0, h⟩ := bind_ok_inv h
      obtain ⟨efs0, hf0, st0⟩ := ih e0 s w s1 hwf h0
      have hwf1 := interpret_wf hwf h0
      cases w with
      | injL a =>
        obtain ⟨efs1, hf1, st1⟩ := ih _ s1 v s' hwf1 h
        refine ⟨efs0 ++ efs1, by rw [hf1, hf0]; simp, ?_⟩
        simpa [ECtxItem.fill] using
          (((Steps.fillItem (.case e1 e2) st0).trans
            (Steps.of_baseStep (BaseStep.caseLS a e1 e2 s1.lang))).trans st1)
      | injR a =>
        obtain ⟨efs1, hf1, st1⟩ := ih _ s1 v s' hwf1 h
        refine ⟨efs0 ++ efs1, by rw [hf1, hf0]; simp, ?_⟩
        simpa [ECtxItem.fill] using
          (((Steps.fillItem (.case e1 e2) st0).trans
            (Steps.of_baseStep (BaseStep.caseRS a e1 e2 s1.lang))).trans st1)
      | _ => exact absurd h stuck_ne_ok
    | fork e =>
      simp only [interpret] at h
      rw [forkThread_bind] at h
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h
      exact ⟨[e], rfl, Steps.of_baseStep (BaseStep.forkS e s.lang)⟩
    | newProph => simp only [interpret] at h; exact absurd h throw_ne_ok
    | resolve e0 e1 e2 => simp only [interpret] at h; exact absurd h throw_ne_ok
    | load e =>
      simp only [interpret] at h
      obtain ⟨vl, s1, he, h⟩ := bind_ok_inv h
      obtain ⟨⟨l, w⟩, s2, hr, h⟩ := bind_ok_inv h
      obtain ⟨hvl, hs2, hlive⟩ := readLoc_ok_inv hr
      obtain ⟨efs1, hf1, st1⟩ := ih e s vl s1 hwf he
      rw [hvl] at st1
      rw [hs2] at h
      obtain ⟨hv, hs⟩ := pure_ok_inv h
      have hv' : w = v := hv
      refine ⟨efs1, by rw [← hs]; exact hf1, ?_⟩
      rw [← hs, ← hv']
      simpa [ECtxItem.fill] using (Steps.fillItem .load st1).trans
        (Steps.of_baseStep (BaseStep.loadS l w s1.lang hlive))
    | free e =>
      simp only [interpret] at h
      obtain ⟨vl, s1, he, h⟩ := bind_ok_inv h
      obtain ⟨⟨l, w⟩, s2, hr, h⟩ := bind_ok_inv h
      obtain ⟨hvl, hs2, hlive⟩ := readLoc_ok_inv hr
      obtain ⟨efs1, hf1, st1⟩ := ih e s vl s1 hwf he
      rw [hvl] at st1
      rw [hs2, modifyLang_bind] at h
      obtain ⟨hv, hs⟩ := pure_ok_inv h
      refine ⟨efs1, by rw [← hs]; exact hf1, ?_⟩
      rw [← hs, ← hv]
      simpa [ECtxItem.fill] using (Steps.fillItem .free st1).trans
        (Steps.of_baseStep (BaseStep.freeS l w s1.lang hlive))
    | store e1 e2 =>
      simp only [interpret] at h
      obtain ⟨w, s1, h2, h⟩ := bind_ok_inv h
      obtain ⟨vl, s2, h1, h⟩ := bind_ok_inv h
      obtain ⟨⟨l, w0⟩, s3, hr, h⟩ := bind_ok_inv h
      obtain ⟨hvl, hs3, hlive⟩ := readLoc_ok_inv hr
      obtain ⟨efs2, hf2, st2⟩ := ih e2 s w s1 hwf h2
      have hwf1 := interpret_wf hwf h2
      obtain ⟨efs1, hf1, st1⟩ := ih e1 s1 vl s2 hwf1 h1
      rw [hvl] at st1
      rw [hs3, modifyLang_bind] at h
      obtain ⟨hv, hs⟩ := pure_ok_inv h
      refine ⟨efs2 ++ efs1, by rw [← hs, hf1, hf2]; simp, ?_⟩
      rw [← hs, ← hv]
      have cb := Steps.of_baseStep (BaseStep.storeS l w0 w s2.lang hlive)
      simpa [ECtxItem.fill] using
        ((Steps.fillItem (.storeR e1) st2).trans (Steps.fillItem (.storeL w) st1)).trans cb
    | xchg e1 e2 =>
      simp only [interpret] at h
      obtain ⟨w, s1, h2, h⟩ := bind_ok_inv h
      obtain ⟨vl, s2, h1, h⟩ := bind_ok_inv h
      obtain ⟨⟨l, w0⟩, s3, hr, h⟩ := bind_ok_inv h
      obtain ⟨hvl, hs3, hlive⟩ := readLoc_ok_inv hr
      obtain ⟨efs2, hf2, st2⟩ := ih e2 s w s1 hwf h2
      have hwf1 := interpret_wf hwf h2
      obtain ⟨efs1, hf1, st1⟩ := ih e1 s1 vl s2 hwf1 h1
      rw [hvl] at st1
      rw [hs3, modifyLang_bind] at h
      obtain ⟨hv, hs⟩ := pure_ok_inv h
      have hv' : w0 = v := hv
      refine ⟨efs2 ++ efs1, by rw [← hs, hf1, hf2]; simp, ?_⟩
      rw [← hs, ← hv']
      have cb := Steps.of_baseStep (BaseStep.xchgS l w0 w s2.lang hlive)
      simpa [ECtxItem.fill] using
        ((Steps.fillItem (.xchgR e1) st2).trans (Steps.fillItem (.xchgL w) st1)).trans cb
    | faa e1 e2 =>
      simp only [interpret] at h
      obtain ⟨w, s1, h2, h⟩ := bind_ok_inv h
      obtain ⟨vl, s2, h1, h⟩ := bind_ok_inv h
      obtain ⟨⟨l, w0⟩, s3, hr, h⟩ := bind_ok_inv h
      obtain ⟨hvl, hs3, hlive⟩ := readLoc_ok_inv hr
      obtain ⟨efs2, hf2, st2⟩ := ih e2 s w s1 hwf h2
      have hwf1 := interpret_wf hwf h2
      obtain ⟨efs1, hf1, st1⟩ := ih e1 s1 vl s2 hwf1 h1
      rw [hvl] at st1
      rw [hs3] at h
      cases w0 with
      | lit bl0 =>
        cases bl0 with
        | int i1 =>
          cases w with
          | lit bl =>
            cases bl with
            | int i2 =>
              -- expose the iota-reduced computation
              have h' : (modifyLang (State.initHeap · l 1 (some (Val.lit (.int (i1 + i2))))) >>=
                  fun _ => (Pure.pure (Val.lit (.int i1)) : InterpM Val)) s2 = (.ok v, s') := h
              rw [modifyLang_bind] at h'
              obtain ⟨hv, hs⟩ := pure_ok_inv h'
              refine ⟨efs2 ++ efs1, by rw [← hs, hf1, hf2]; simp, ?_⟩
              rw [← hs, ← hv]
              have cb := Steps.of_baseStep (BaseStep.faaS l i1 i2 s2.lang hlive)
              simpa [ECtxItem.fill] using ((Steps.fillItem (.faaR e1) st2).trans
                       (Steps.fillItem (.faaL (.lit (.int i2))) st1)).trans cb
            | _ => exact absurd h stuck_ne_ok
          | _ => exact absurd h stuck_ne_ok
        | _ => exact absurd h stuck_ne_ok
      | _ => exact absurd h stuck_ne_ok
    | cmpXchg e0 e1 e2 =>
      simp only [interpret] at h
      obtain ⟨v2, s1, h2, h⟩ := bind_ok_inv h
      obtain ⟨v1, s2, h1, h⟩ := bind_ok_inv h
      obtain ⟨vl, s3, h0, h⟩ := bind_ok_inv h
      obtain ⟨⟨l, w0⟩, s4, hr, h⟩ := bind_ok_inv h
      obtain ⟨hvl, hs4, hlive⟩ := readLoc_ok_inv hr
      obtain ⟨efs2, hf2, st2⟩ := ih e2 s v2 s1 hwf h2
      have hwf1 := interpret_wf hwf h2
      obtain ⟨efs1, hf1, st1⟩ := ih e1 s1 v1 s2 hwf1 h1
      have hwf2 := interpret_wf hwf1 h1
      obtain ⟨efs0, hf0, st0⟩ := ih e0 s2 vl s3 hwf2 h0
      rw [hvl] at st0
      rw [hs4] at h
      have h' : (if w0.compareSafe v1 = true then
                   (if (w0 == v1) = true then
                     (modifyLang (State.initHeap · l 1 (some v2)) >>= fun _ =>
                       (Pure.pure (Val.pair w0 (.lit (.bool (w0 == v1)))) : InterpM Val))
                    else (Pure.pure (Val.pair w0 (.lit (.bool (w0 == v1)))) : InterpM Val))
                 else (stuck (.cmpXchgUnsafe w0 v1) : InterpM Val)) s3 = (.ok v, s') := h
      by_cases hcs : w0.compareSafe v1 = true
      · rw [if_pos hcs] at h'
        have cb := Steps.of_baseStep
          (BaseStep.cmpXchgS l v1 v2 w0 s3.lang (w0 == v1) hlive hcs rfl)
        have cctx := ((Steps.fillItem (.cmpXchgR e0 e1) st2).trans
                      (Steps.fillItem (.cmpXchgM e0 v2) st1)).trans
                      (Steps.fillItem (.cmpXchgL v1 v2) st0)
        by_cases hb : (w0 == v1) = true
        · rw [if_pos hb] at h'
          rw [modifyLang_bind] at h'
          obtain ⟨hv, hs⟩ := pure_ok_inv h'
          refine ⟨efs2 ++ efs1 ++ efs0, by rw [← hs, hf0, hf1, hf2]; simp, ?_⟩
          rw [← hs, ← hv, hb]
          rw [hb, if_pos rfl] at cb
          simpa [ECtxItem.fill] using cctx.trans cb
        · rw [if_neg hb] at h'
          obtain ⟨hv, hs⟩ := pure_ok_inv h'
          refine ⟨efs2 ++ efs1 ++ efs0, by rw [← hs, hf0, hf1, hf2]; simp, ?_⟩
          simp only [Bool.not_eq_true] at hb
          rw [← hs, ← hv, hb]
          rw [hb, if_neg (by simp)] at cb
          simpa [ECtxItem.fill] using cctx.trans cb
      · rw [if_neg hcs] at h'; exact absurd h' stuck_ne_ok
    | allocN e1 e2 =>
      simp only [interpret] at h
      obtain ⟨w, s1, h2, h⟩ := bind_ok_inv h
      obtain ⟨nv, s2, h1, h⟩ := bind_ok_inv h
      obtain ⟨efs2, hf2, st2⟩ := ih e2 s w s1 hwf h2
      have hwf1 := interpret_wf hwf h2
      obtain ⟨efs1, hf1, st1⟩ := ih e1 s1 nv s2 hwf1 h1
      have hwf2 := interpret_wf hwf1 h1
      cases nv with
      | lit bl =>
        cases bl with
        | int n =>
          have h' : (if 0 < n then
                       (allocLoc n >>= fun l =>
                         modifyLang (State.initHeap · l n (some w)) >>= fun _ =>
                           (Pure.pure (Val.lit (.loc l)) : InterpM Val))
                     else (stuck (.allocLenNonPos n) : InterpM Val)) s2 = (.ok v, s') := h
          by_cases hn : 0 < n
          · rw [if_pos hn, allocLoc_bind, modifyLang_bind] at h'
            obtain ⟨hv, hs⟩ := pure_ok_inv h'
            refine ⟨efs2 ++ efs1, by rw [← hs, hf1, hf2]; simp, ?_⟩
            rw [← hs, ← hv]
            have cb := Steps.of_baseStep (BaseStep.allocNS n w s2.lang (Loc.mk s2.nextLoc) hn
              (fun i hi0 _ => hwf2 _ (by simp only [loc_add_n]; omega)))
            simpa [ECtxItem.fill] using ((Steps.fillItem (.allocNR e1) st2).trans
                     (Steps.fillItem (.allocNL w) st1)).trans cb
          · rw [if_neg hn] at h'; exact absurd h' stuck_ne_ok
        | _ => exact absurd h stuck_ne_ok
      | _ => exact absurd h stuck_ne_ok

/-- Successful case of Rocq's `exec_spec`. -/
theorem exec_sound {fuel : Nat} {e : Exp} {v : Val} (h : exec fuel e = .ok v) :
    ∃ tp σ, ([e], initState) -·->ₜₚ* (Exp.ofVal v :: tp, σ) := by
  rcases hrun : interpret fuel e InterpState.init with ⟨r, s'⟩
  have hr : r = .ok v := by simpa [exec, run, hrun] using h
  subst hr
  obtain ⟨efs, _, st⟩ := interpret_sound fuel e InterpState.init v s' StateWf.init hrun
  exact ⟨efs, s'.lang, by simpa [InterpState.init] using st.to_cfg []⟩

/-! ## Stuckness -/

section Stuckness
open EctxLanguage EctxItemLanguage

/-- An expression whose immediate subredexes are values is stuck exactly when no
`BaseStep` applies. Rocq's `terminal_expr_stuck`. -/
theorem stuck_of_no_baseStep {e : Exp} {σ : State}
    (hval : toVal e = none) (hsub : SubredexesAreValues e)
    (hno : ∀ obs e' σ' eₜ, ¬ BaseStep e σ obs e' σ' eₜ) :
    PrimStep.Stuck (Val := Val) (e, σ) := by
  refine ⟨hval, ?_⟩
  intro obs e' σ' eₜ hstep
  exact hno obs e' σ' eₜ (baseStep_of_primStep hstep hsub)

/-- `e` runs, forking `efs`, to a stuck expression. -/
def EventuallyStuck (e : Exp) (σ σ' : State) (efs : List Exp) : Prop :=
  ∃ e'', Steps e σ e'' σ' efs ∧ PrimStep.Stuck (Val := Val) (e'', σ')

theorem EventuallyStuck.now {e : Exp} {σ : State}
    (h : PrimStep.Stuck (Val := Val) (e, σ)) : EventuallyStuck e σ σ [] :=
  ⟨e, Steps.refl, h⟩

theorem EventuallyStuck.steps {e e₁ : Exp} {σ σ₁ σ₂ : State} {efs₁ efs₂ : List Exp}
    (hs : Steps e σ e₁ σ₁ efs₁) (h : EventuallyStuck e₁ σ₁ σ₂ efs₂) :
    EventuallyStuck e σ σ₂ (efs₁ ++ efs₂) :=
  let ⟨e'', hst, hstuck⟩ := h
  ⟨e'', hs.trans hst, hstuck⟩

theorem EventuallyStuck.fill {K : Exp → Exp} [Context K] {e : Exp} {σ σ' : State} {efs}
    (h : EventuallyStuck e σ σ' efs) : EventuallyStuck (K e) σ σ' efs :=
  let ⟨e'', hst, hstuck⟩ := h
  ⟨K e'', hst.fill, Context.stuck_fill (Val := Val) K hstuck⟩

theorem EventuallyStuck.fillItem (Ki : ECtxItem) {e : Exp} {σ σ' : State} {efs}
    (h : EventuallyStuck e σ σ' efs) : EventuallyStuck (Ki.fill e) σ σ' efs :=
  EventuallyStuck.fill (K := EvContext.fill [Ki]) h

/-- Rocq's `interp_bind_inr_inv`. -/
theorem bind_error_inv {α β} {x : InterpM α} {f : α → InterpM β}
    {s s' : InterpState} {er : InterpError} (h : (x >>= f) s = (.error er, s')) :
    x s = (.error er, s') ∨ ∃ a sx, x s = (.ok a, sx) ∧ f a sx = (.error er, s') := by
  obtain ⟨rx, sx, hx⟩ : ∃ rx sx, x s = (rx, sx) := ⟨(x s).1, (x s).2, rfl⟩
  cases rx with
  | ok a => exact .inr ⟨a, sx, hx, by rw [bind_ok x f s sx a hx] at h; exact h⟩
  | error er' =>
    rw [bind_error x f s sx er' hx] at h
    have h1 : (Except.error er' : Except InterpError β) = .error er := congrArg Prod.fst h
    have h2 : sx = s' := congrArg Prod.snd h
    simp only [Except.error.injEq] at h1
    subst h1; subst h2
    exact .inl hx

/-- `stuck` never changes the state. -/
theorem stuck_error_inv {α} {r r' : StuckReason} {s s' : InterpState}
    (h : (stuck r : InterpM α) s = (.error (.stuck r'), s')) : s' = s :=
  (congrArg Prod.snd h).symm

/-- `unsupported` is not a `stuck` verdict. -/
private theorem unsupported_ne_stuck {α} {op : String} {r : StuckReason} {s s' : InterpState}
    (h : (throw (.unsupported op) : InterpM α) s = (.error (.stuck r), s')) : False := by
  have h1 : (Except.error (InterpError.unsupported op) : Except InterpError α)
      = .error (.stuck r) :=
    congrArg Prod.fst h
  simp at h1

private theorem outOfFuel_ne_stuck {α} {r : StuckReason} {s s' : InterpState}
    (h : (throw .outOfFuel : InterpM α) s = (.error (.stuck r), s')) : False := by
  have h1 : (Except.error InterpError.outOfFuel : Except InterpError α) = .error (.stuck r) :=
    congrArg Prod.fst h
  simp at h1

private theorem pure_ne_error {α} {a : α} {er : InterpError} {s s' : InterpState}
    (h : (Pure.pure a : InterpM α) s = (.error er, s')) : False := by
  have h1 : (Except.ok a : Except InterpError α) = .error er := congrArg Prod.fst h
  simp at h1

/-- A failing `readLoc` leaves the state alone and leaves no live cell to step
on. Stated in the uniform shape of Rocq's `read_loc_inr_inv` — a single
implication rather than a "not a location or not live" disjunction — so that the
heap-operation cases of `interpret_complete` close without re-splitting. -/
theorem readLoc_error_inv {op : HeapOp} {v : Val} {s s' : InterpState} {r : StuckReason}
    (h : readLoc op v s = (.error (.stuck r), s')) :
    s' = s ∧ ∀ l w, v = .lit (.loc l) → s.lang.get? l ≠ some (some w) := by
  unfold readLoc at h
  split at h
  next l' =>
    rw [readLang_bind] at h
    rcases hg : s.lang.get? l' with _ | (_ | w')
    · exact ⟨stuck_error_inv (hg ▸ h), by rintro l w ⟨rfl⟩; rw [hg]; simp⟩
    · exact ⟨stuck_error_inv (hg ▸ h), by rintro l w ⟨rfl⟩; rw [hg]; simp⟩
    · rw [hg] at h; exact absurd h pure_ne_error
  next hne => exact ⟨stuck_error_inv h, fun l _ hc => absurd hc (hne l)⟩

/-- Prove the expression in the goal stuck: it is not a value, its subredexes
are values, and no `BaseStep` applies. -/
local macro "solve_stuck" : tactic => `(tactic|
  (refine stuck_of_no_baseStep rfl ?_ ?_
   · solve_subredex_values
   · intro obs e' σ' eₜ hstep; cases hstep <;> simp_all))

/-- Close a leaf of `interpret_complete`: `cctx` has already run `e` to the head
redex `eₕ`, the interpreter stopped there, and `eₕ` is genuinely stuck. Every
ill-typed-operand leaf of a heap or arithmetic case has this shape. -/
theorem complete_of_head_stuck {e eₕ : Exp} {σ : State} {s₀ s' : InterpState}
    {forked efs : List Exp}
    (cctx : Steps e σ eₕ s₀.lang efs) (hf : s₀.forked = forked ++ efs)
    (hstuck : PrimStep.Stuck (Val := Val) (eₕ, s₀.lang)) (hs : s' = s₀) :
    ∃ efs', s'.forked = forked ++ efs' ∧ EventuallyStuck e σ s'.lang efs' := by
  subst hs
  exact ⟨efs, hf, eₕ, cctx, hstuck⟩

/-- A "stuck" verdict corresponds to a genuinely stuck configuration. -/
theorem interpret_complete (fuel : Nat) :
    ∀ (e : Exp) (s : InterpState) (r : StuckReason) (s' : InterpState),
      StateWf s → interpret fuel e s = (.error (.stuck r), s') →
      ∃ efs, s'.forked = s.forked ++ efs ∧ EventuallyStuck e s.lang s'.lang efs := by
  induction fuel with
  | zero => intro e s r s' _ h; exact absurd h outOfFuel_ne_stuck
  | succ fuel ih =>
    intro e s r s' hwf h
    cases e with
    | val w => simp only [interpret] at h; exact absurd h pure_ne_error
    | rec_ f x b => simp only [interpret] at h; exact absurd h pure_ne_error
    | newProph => simp only [interpret] at h; exact absurd h unsupported_ne_stuck
    | resolve e0 e1 e2 => simp only [interpret] at h; exact absurd h unsupported_ne_stuck
    | fork e =>
      simp only [interpret] at h
      rw [forkThread_bind] at h
      exact absurd h pure_ne_error
    | var x =>
      simp only [interpret] at h
      have hs := stuck_error_inv h
      exact ⟨[], by rw [hs]; simp, by rw [hs]; exact EventuallyStuck.now (by solve_stuck)⟩
    | injL e =>
      simp only [interpret] at h
      rcases bind_error_inv h with h1 | ⟨w, s1, h1, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e s r s' hwf h1
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem .injL hes⟩
      · exact absurd h pure_ne_error
    | injR e =>
      simp only [interpret] at h
      rcases bind_error_inv h with h1 | ⟨w, s1, h1, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e s r s' hwf h1
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem .injR hes⟩
      · exact absurd h pure_ne_error
    | unop op e =>
      simp only [interpret] at h
      rcases bind_error_inv h with h1 | ⟨w, s1, h1, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e s r s' hwf h1
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem (.unOp op) hes⟩
      · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e s w s1 hwf h1
        rcases hev : op.eval w with _ | w'
        · rw [hev] at h
          have hs := stuck_error_inv h
          refine ⟨efs1, by rw [hs]; exact hf1, ?_⟩
          rw [hs]
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.unOp op) st1)
            (EventuallyStuck.now (e := Exp.unop op (.ofVal w)) (by solve_stuck))
        · rw [hev] at h; exact absurd h pure_ne_error
    | fst e =>
      simp only [interpret] at h
      rcases bind_error_inv h with h1 | ⟨w, s1, h1, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e s r s' hwf h1
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem .fst hes⟩
      · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e s w s1 hwf h1
        cases w with
        | pair a b => exact absurd h pure_ne_error
        | _ =>
          have hs := stuck_error_inv h
          refine ⟨efs1, by rw [hs]; exact hf1, ?_⟩
          rw [hs]
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem .fst st1)
            (EventuallyStuck.now (by solve_stuck))
    | snd e =>
      simp only [interpret] at h
      rcases bind_error_inv h with h1 | ⟨w, s1, h1, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e s r s' hwf h1
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem .snd hes⟩
      · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e s w s1 hwf h1
        cases w with
        | pair a b => exact absurd h pure_ne_error
        | _ =>
          have hs := stuck_error_inv h
          refine ⟨efs1, by rw [hs]; exact hf1, ?_⟩
          rw [hs]
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem .snd st1)
            (EventuallyStuck.now (by solve_stuck))
    | «if» e0 e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h0 | ⟨c, s1, h0, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e0 s r s' hwf h0
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem (.if e1 e2) hes⟩
      · obtain ⟨efs0, hf0, st0⟩ := interpret_sound fuel e0 s c s1 hwf h0
        have hwf1 := interpret_wf hwf h0
        cases c with
        | lit bl =>
          cases bl with
          | bool b =>
            obtain ⟨efs, hf, hes⟩ := ih _ s1 r s' hwf1 h
            refine ⟨efs0 ++ efs, by rw [hf, hf0]; simp, ?_⟩
            have cb : Steps (.if (.ofVal (.lit (.bool b))) e1 e2) s1.lang
                (if b then e1 else e2) s1.lang [] := by
              cases b
              · exact Steps.of_baseStep (BaseStep.ifFalseS e1 e2 _)
              · exact Steps.of_baseStep (BaseStep.ifTrueS e1 e2 _)
            simpa [ECtxItem.fill] using
              EventuallyStuck.steps ((Steps.fillItem (.if e1 e2) st0).trans cb) hes
          | _ =>
            have hs := stuck_error_inv h
            refine ⟨efs0, by rw [hs]; exact hf0, ?_⟩
            rw [hs]
            simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.if e1 e2) st0)
              (EventuallyStuck.now (by solve_stuck))
        | _ =>
          have hs := stuck_error_inv h
          refine ⟨efs0, by rw [hs]; exact hf0, ?_⟩
          rw [hs]
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.if e1 e2) st0)
            (EventuallyStuck.now (by solve_stuck))
    | case e0 e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h0 | ⟨w, s1, h0, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e0 s r s' hwf h0
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem (.case e1 e2) hes⟩
      · obtain ⟨efs0, hf0, st0⟩ := interpret_sound fuel e0 s w s1 hwf h0
        have hwf1 := interpret_wf hwf h0
        cases w with
        | injL a =>
          obtain ⟨efs, hf, hes⟩ := ih _ s1 r s' hwf1 h
          refine ⟨efs0 ++ efs, by rw [hf, hf0]; simp, ?_⟩
          have cb := Steps.of_baseStep (BaseStep.caseLS a e1 e2 s1.lang)
          simpa [ECtxItem.fill] using
            EventuallyStuck.steps ((Steps.fillItem (.case e1 e2) st0).trans cb) hes
        | injR a =>
          obtain ⟨efs, hf, hes⟩ := ih _ s1 r s' hwf1 h
          refine ⟨efs0 ++ efs, by rw [hf, hf0]; simp, ?_⟩
          have cb := Steps.of_baseStep (BaseStep.caseRS a e1 e2 s1.lang)
          simpa [ECtxItem.fill] using
            EventuallyStuck.steps ((Steps.fillItem (.case e1 e2) st0).trans cb) hes
        | _ =>
          have hs := stuck_error_inv h
          refine ⟨efs0, by rw [hs]; exact hf0, ?_⟩
          rw [hs]
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.case e1 e2) st0)
            (EventuallyStuck.now (by solve_stuck))
    | app e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h2 | ⟨v2, s1, h2, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e2 s r s' hwf h2
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem (.appR e1) hes⟩
      · obtain ⟨efs2, hf2, st2⟩ := interpret_sound fuel e2 s v2 s1 hwf h2
        have hwf1 := interpret_wf hwf h2
        rcases bind_error_inv h with h1 | ⟨f, s2, h1, h⟩
        · obtain ⟨efs, hf, hes⟩ := ih e1 s1 r s' hwf1 h1
          refine ⟨efs2 ++ efs, by rw [hf, hf2]; simp, ?_⟩
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.appR e1) st2)
            (EventuallyStuck.fillItem (.appL v2) hes)
        · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e1 s1 f s2 hwf1 h1
          have hwf2 := interpret_wf hwf1 h1
          have cctx := (Steps.fillItem (.appR e1) st2).trans (Steps.fillItem (.appL v2) st1)
          simp only [ECtxItem.fill] at cctx
          have hforked : s2.forked = s.forked ++ (efs2 ++ efs1) := by rw [hf1, hf2]; simp
          cases f with
          | rec_ fn x body =>
            obtain ⟨efs3, hf3, hes⟩ := ih _ s2 r s' hwf2 h
            refine ⟨efs2 ++ efs1 ++ efs3, by rw [hf3, hf1, hf2]; simp, ?_⟩
            have cb : Steps (.app (.ofVal (.rec_ fn x body)) (.ofVal v2)) s2.lang
                ((body.subst fn (.rec_ fn x body)).subst x v2) s2.lang [] :=
              Steps.of_baseStep (BaseStep.betaS fn x body v2 _ _ rfl)
            simpa [ECtxItem.fill] using EventuallyStuck.steps (cctx.trans cb) hes
          | _ =>
            exact complete_of_head_stuck cctx hforked (by solve_stuck) (stuck_error_inv h)
    | binop op e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h2 | ⟨v2, s1, h2, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e2 s r s' hwf h2
        exact ⟨efs, hf, by simpa [ECtxItem.fill] using
          EventuallyStuck.fillItem (.binOpR op e1) hes⟩
      · obtain ⟨efs2, hf2, st2⟩ := interpret_sound fuel e2 s v2 s1 hwf h2
        have hwf1 := interpret_wf hwf h2
        rcases bind_error_inv h with h1 | ⟨v1, s2, h1, h⟩
        · obtain ⟨efs, hf, hes⟩ := ih e1 s1 r s' hwf1 h1
          refine ⟨efs2 ++ efs, by rw [hf, hf2]; simp, ?_⟩
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.binOpR op e1) st2)
            (EventuallyStuck.fillItem (.binOpL op v2) hes)
        · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e1 s1 v1 s2 hwf1 h1
          have cctx := (Steps.fillItem (.binOpR op e1) st2).trans
                       (Steps.fillItem (.binOpL op v2) st1)
          simp only [ECtxItem.fill] at cctx
          have hforked : s2.forked = s.forked ++ (efs2 ++ efs1) := by rw [hf1, hf2]; simp
          rcases hev : op.eval v1 v2 with _ | v'
          · rw [hev] at h
            exact complete_of_head_stuck cctx hforked (by solve_stuck) (stuck_error_inv h)
          · rw [hev] at h; exact absurd h pure_ne_error
    | pair e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h2 | ⟨v2, s1, h2, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e2 s r s' hwf h2
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem (.pairR e1) hes⟩
      · obtain ⟨efs2, hf2, st2⟩ := interpret_sound fuel e2 s v2 s1 hwf h2
        have hwf1 := interpret_wf hwf h2
        rcases bind_error_inv h with h1 | ⟨v1, s2, h1, h⟩
        · obtain ⟨efs, hf, hes⟩ := ih e1 s1 r s' hwf1 h1
          refine ⟨efs2 ++ efs, by rw [hf, hf2]; simp, ?_⟩
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.pairR e1) st2)
            (EventuallyStuck.fillItem (.pairL v2) hes)
        · exact absurd h pure_ne_error
    | load e =>
      simp only [interpret] at h
      rcases bind_error_inv h with h1 | ⟨vl, s1, h1, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e s r s' hwf h1
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem .load hes⟩
      · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e s vl s1 hwf h1
        rcases bind_error_inv h with hr | ⟨p, s2, hr, h⟩
        · obtain ⟨hs, hcase⟩ := readLoc_error_inv hr
          have cctx := Steps.fillItem (.load) st1
          simp only [ECtxItem.fill] at cctx
          exact complete_of_head_stuck cctx hf1 (by solve_stuck) hs
        · exact absurd h pure_ne_error
    | free e =>
      simp only [interpret] at h
      rcases bind_error_inv h with h1 | ⟨vl, s1, h1, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e s r s' hwf h1
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem .free hes⟩
      · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e s vl s1 hwf h1
        rcases bind_error_inv h with hr | ⟨p, s2, hr, h⟩
        · obtain ⟨hs, hcase⟩ := readLoc_error_inv hr
          have cctx := Steps.fillItem (.free) st1
          simp only [ECtxItem.fill] at cctx
          exact complete_of_head_stuck cctx hf1 (by solve_stuck) hs
        · rw [modifyLang_bind] at h; exact absurd h pure_ne_error
    | store e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h2 | ⟨w, s1, h2, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e2 s r s' hwf h2
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem (.storeR e1) hes⟩
      · obtain ⟨efs2, hf2, st2⟩ := interpret_sound fuel e2 s w s1 hwf h2
        have hwf1 := interpret_wf hwf h2
        rcases bind_error_inv h with h1 | ⟨vl, s2, h1, h⟩
        · obtain ⟨efs, hf, hes⟩ := ih e1 s1 r s' hwf1 h1
          refine ⟨efs2 ++ efs, by rw [hf, hf2]; simp, ?_⟩
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.storeR e1) st2)
            (EventuallyStuck.fillItem (.storeL w) hes)
        · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e1 s1 vl s2 hwf1 h1
          have cctx := (Steps.fillItem (.storeR e1) st2).trans (Steps.fillItem (.storeL w) st1)
          simp only [ECtxItem.fill] at cctx
          have hforked : s2.forked = s.forked ++ (efs2 ++ efs1) := by rw [hf1, hf2]; simp
          rcases bind_error_inv h with hr | ⟨⟨l, w0⟩, s3, hr, h⟩
          · obtain ⟨hs, hcase⟩ := readLoc_error_inv hr
            exact complete_of_head_stuck cctx hforked (by solve_stuck) hs
          · obtain ⟨hvl, hs3, hlive⟩ := readLoc_ok_inv hr
            rw [hs3, modifyLang_bind] at h
            exact absurd h pure_ne_error
    | xchg e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h2 | ⟨w, s1, h2, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e2 s r s' hwf h2
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem (.xchgR e1) hes⟩
      · obtain ⟨efs2, hf2, st2⟩ := interpret_sound fuel e2 s w s1 hwf h2
        have hwf1 := interpret_wf hwf h2
        rcases bind_error_inv h with h1 | ⟨vl, s2, h1, h⟩
        · obtain ⟨efs, hf, hes⟩ := ih e1 s1 r s' hwf1 h1
          refine ⟨efs2 ++ efs, by rw [hf, hf2]; simp, ?_⟩
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.xchgR e1) st2)
            (EventuallyStuck.fillItem (.xchgL w) hes)
        · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e1 s1 vl s2 hwf1 h1
          have cctx := (Steps.fillItem (.xchgR e1) st2).trans (Steps.fillItem (.xchgL w) st1)
          simp only [ECtxItem.fill] at cctx
          have hforked : s2.forked = s.forked ++ (efs2 ++ efs1) := by rw [hf1, hf2]; simp
          rcases bind_error_inv h with hr | ⟨⟨l, w0⟩, s3, hr, h⟩
          · obtain ⟨hs, hcase⟩ := readLoc_error_inv hr
            exact complete_of_head_stuck cctx hforked (by solve_stuck) hs
          · obtain ⟨hvl, hs3, hlive⟩ := readLoc_ok_inv hr
            rw [hs3, modifyLang_bind] at h
            exact absurd h pure_ne_error
    | faa e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h2 | ⟨w, s1, h2, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e2 s r s' hwf h2
        exact ⟨efs, hf, by
          simpa [ECtxItem.fill] using EventuallyStuck.fillItem (.faaR e1) hes⟩
      · obtain ⟨efs2, hf2, st2⟩ := interpret_sound fuel e2 s w s1 hwf h2
        have hwf1 := interpret_wf hwf h2
        rcases bind_error_inv h with h1 | ⟨vl, s2, h1, h⟩
        · obtain ⟨efs, hf, hes⟩ := ih e1 s1 r s' hwf1 h1
          refine ⟨efs2 ++ efs, by rw [hf, hf2]; simp, ?_⟩
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.faaR e1) st2)
            (EventuallyStuck.fillItem (.faaL w) hes)
        · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e1 s1 vl s2 hwf1 h1
          have cctx := (Steps.fillItem (.faaR e1) st2).trans (Steps.fillItem (.faaL w) st1)
          simp only [ECtxItem.fill] at cctx
          have hforked : s2.forked = s.forked ++ (efs2 ++ efs1) := by rw [hf1, hf2]; simp
          rcases bind_error_inv h with hr | ⟨⟨l, w0⟩, s3, hr, h⟩
          · obtain ⟨hs, hcase⟩ := readLoc_error_inv hr
            exact complete_of_head_stuck cctx hforked (by solve_stuck) hs
          · obtain ⟨hvl, hs3, hlive⟩ := readLoc_ok_inv hr
            rw [hvl] at cctx
            rw [hs3] at h
            cases w0 with
            | lit bl0 =>
              cases bl0 with
              | int i1 =>
                cases w with
                | lit bl =>
                  cases bl with
                  | int i2 =>
                    have h' : (modifyLang
                        (State.initHeap · l 1 (some (Val.lit (.int (i1 + i2))))) >>=
                        fun _ => (Pure.pure (Val.lit (.int i1)) : InterpM Val)) s2 =
                        (.error (.stuck r), s') := h
                    rw [modifyLang_bind] at h'
                    exact absurd h' pure_ne_error
                  | _ =>
                    exact complete_of_head_stuck cctx hforked (by solve_stuck)
                      (stuck_error_inv h)
                | _ =>
                  exact complete_of_head_stuck cctx hforked (by solve_stuck)
                    (stuck_error_inv h)
              | _ =>
                exact complete_of_head_stuck cctx hforked (by solve_stuck)
                  (stuck_error_inv h)
            | _ =>
              exact complete_of_head_stuck cctx hforked (by solve_stuck)
                (stuck_error_inv h)

    | allocN e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h2 | ⟨w, s1, h2, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e2 s r s' hwf h2
        exact ⟨efs, hf, by simpa [ECtxItem.fill] using
          EventuallyStuck.fillItem (.allocNR e1) hes⟩
      · obtain ⟨efs2, hf2, st2⟩ := interpret_sound fuel e2 s w s1 hwf h2
        have hwf1 := interpret_wf hwf h2
        rcases bind_error_inv h with h1 | ⟨nv, s2, h1, h⟩
        · obtain ⟨efs, hf, hes⟩ := ih e1 s1 r s' hwf1 h1
          refine ⟨efs2 ++ efs, by rw [hf, hf2]; simp, ?_⟩
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.allocNR e1) st2)
            (EventuallyStuck.fillItem (.allocNL w) hes)
        · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e1 s1 nv s2 hwf1 h1
          have cctx := (Steps.fillItem (.allocNR e1) st2).trans
                       (Steps.fillItem (.allocNL w) st1)
          simp only [ECtxItem.fill] at cctx
          have hforked : s2.forked = s.forked ++ (efs2 ++ efs1) := by rw [hf1, hf2]; simp
          cases nv with
          | lit bl =>
            cases bl with
            | int n =>
              have h' : (if 0 < n then
                           (allocLoc n >>= fun l =>
                             modifyLang (State.initHeap · l n (some w)) >>= fun _ =>
                               (Pure.pure (Val.lit (.loc l)) : InterpM Val))
                         else (stuck (.allocLenNonPos n) : InterpM Val)) s2 =
                        (.error (.stuck r), s') := h
              by_cases hn : 0 < n
              · rw [if_pos hn, allocLoc_bind, modifyLang_bind] at h'
                exact absurd h' pure_ne_error
              · rw [if_neg hn] at h'
                exact complete_of_head_stuck cctx hforked (by solve_stuck) (stuck_error_inv h')
            | _ =>
              exact complete_of_head_stuck cctx hforked (by solve_stuck) (stuck_error_inv h)
          | _ =>
            exact complete_of_head_stuck cctx hforked (by solve_stuck) (stuck_error_inv h)
    | cmpXchg e0 e1 e2 =>
      simp only [interpret] at h
      rcases bind_error_inv h with h2 | ⟨v2, s1, h2, h⟩
      · obtain ⟨efs, hf, hes⟩ := ih e2 s r s' hwf h2
        exact ⟨efs, hf, by simpa [ECtxItem.fill] using
          EventuallyStuck.fillItem (.cmpXchgR e0 e1) hes⟩
      · obtain ⟨efs2, hf2, st2⟩ := interpret_sound fuel e2 s v2 s1 hwf h2
        have hwf1 := interpret_wf hwf h2
        rcases bind_error_inv h with h1 | ⟨v1, s2, h1, h⟩
        · obtain ⟨efs, hf, hes⟩ := ih e1 s1 r s' hwf1 h1
          refine ⟨efs2 ++ efs, by rw [hf, hf2]; simp, ?_⟩
          simpa [ECtxItem.fill] using EventuallyStuck.steps (Steps.fillItem (.cmpXchgR e0 e1) st2)
            (EventuallyStuck.fillItem (.cmpXchgM e0 v2) hes)
        · obtain ⟨efs1, hf1, st1⟩ := interpret_sound fuel e1 s1 v1 s2 hwf1 h1
          have hwf2 := interpret_wf hwf1 h1
          rcases bind_error_inv h with h0 | ⟨vl, s3, h0, h⟩
          · obtain ⟨efs, hf, hes⟩ := ih e0 s2 r s' hwf2 h0
            refine ⟨efs2 ++ efs1 ++ efs, by rw [hf, hf1, hf2]; simp, ?_⟩
            simpa [ECtxItem.fill] using EventuallyStuck.steps
              ((Steps.fillItem (.cmpXchgR e0 e1) st2).trans
               (Steps.fillItem (.cmpXchgM e0 v2) st1))
              (EventuallyStuck.fillItem (.cmpXchgL v1 v2) hes)
          · obtain ⟨efs0, hf0, st0⟩ := interpret_sound fuel e0 s2 vl s3 hwf2 h0
            have cctx := ((Steps.fillItem (.cmpXchgR e0 e1) st2).trans
                          (Steps.fillItem (.cmpXchgM e0 v2) st1)).trans
                          (Steps.fillItem (.cmpXchgL v1 v2) st0)
            simp only [ECtxItem.fill] at cctx
            have hforked : s3.forked = s.forked ++ (efs2 ++ efs1 ++ efs0) := by
              rw [hf0, hf1, hf2]; simp
            rcases bind_error_inv h with hr | ⟨⟨l, w0⟩, s4, hr, h⟩
            · obtain ⟨hs, hcase⟩ := readLoc_error_inv hr
              exact complete_of_head_stuck cctx hforked (by solve_stuck) hs
            · obtain ⟨hvl, hs4, hlive⟩ := readLoc_ok_inv hr
              rw [hvl] at cctx
              rw [hs4] at h
              have h' : (if w0.compareSafe v1 = true then
                           (if (w0 == v1) = true then
                             (modifyLang (State.initHeap · l 1 (some v2)) >>= fun _ =>
                               (Pure.pure (Val.pair w0 (.lit (.bool (w0 == v1)))) : InterpM Val))
                            else (Pure.pure (Val.pair w0 (.lit (.bool (w0 == v1)))) : InterpM Val))
                         else (stuck (.cmpXchgUnsafe w0 v1) : InterpM Val)) s3 =
                        (.error (.stuck r), s') := h
              by_cases hcs : w0.compareSafe v1 = true
              · rw [if_pos hcs] at h'
                by_cases hb : (w0 == v1) = true
                · rw [if_pos hb, modifyLang_bind] at h'; exact absurd h' pure_ne_error
                · rw [if_neg hb] at h'; exact absurd h' pure_ne_error
              · rw [if_neg hcs] at h'
                exact complete_of_head_stuck cctx hforked (by solve_stuck) (stuck_error_inv h')

/-- Stuck case of Rocq's `exec_spec`.

Like the success case, this is a statement about *one* execution: `e` has a run
that reaches a stuck configuration. It is not the claim that every execution
gets stuck, and it cannot be — the semantics admits any fresh location while
the interpreter always takes `nextLoc`, so a program that guesses a location
may be stuck under this allocator and fine under another. The header's
success-side blind spot has this mirror image. -/
theorem exec_stuck {fuel : Nat} {e : Exp} {r : StuckReason}
    (h : exec fuel e = .error (.stuck r)) :
    ∃ e' tp σ, ([e], initState) -·->ₜₚ* (e' :: tp, σ) ∧
      PrimStep.Stuck (Val := Val) (e', σ) := by
  rcases hrun : interpret fuel e InterpState.init with ⟨res, s'⟩
  have hres : res = .error (.stuck r) := by simpa [exec, run, hrun] using h
  subst hres
  obtain ⟨efs, _, e'', hst, hstuck⟩ :=
    interpret_complete fuel e InterpState.init r s' StateWf.init hrun
  exact ⟨e'', efs, s'.lang, by simpa [InterpState.init] using hst.to_cfg [], hstuck⟩

/-- Rocq's `exec_spec`, in its original three-way shape: a value means the
program really runs to it, a stuck verdict means it really reaches a stuck
configuration, and `outOfFuel`/`unsupported` claim nothing. -/
theorem exec_spec (fuel : Nat) (e : Exp) :
    match exec fuel e with
    | .ok v => ∃ tp σ, ([e], initState) -·->ₜₚ* (Exp.ofVal v :: tp, σ)
    | .error (.stuck _) =>
      ∃ e' tp σ, ([e], initState) -·->ₜₚ* (e' :: tp, σ) ∧
        PrimStep.Stuck (Val := Val) (e', σ)
    | .error _ => True := by
  cases h : exec fuel e with
  | ok v => exact exec_sound h
  | error er => cases er with
    | stuck r => exact exec_stuck h
    | _ => trivial

end Stuckness

end Iris.HeapLang
