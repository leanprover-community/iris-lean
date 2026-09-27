/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import IrisMath.Termination.Thunk

/-! # An event loop

This file ports `theories/examples/termination/eventloop.v` of Transfinite Iris: an event loop
with a queue of callbacks, where each callback in the queue is paid for with a time credit. The
event loop `run` terminates even if callbacks enqueue further callbacks, as long as they pay for
them (`reentrant_example`).
-/

@[expose] public noncomputable section

universe w v u

namespace Iris.Transfinite.Termination

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Ordinal

/-! ## Code -/

/-- Rocq: `new_stack`. -/
def newStack : Val := hl_val% λ _, ref(none())

/-- Rocq: `push`. -/
def push : Val := hl_val%
  λ s, λ x, let hd := !s; let p := (x, hd); s ← some(ref(p))

/-- Rocq: `pop`. -/
def pop : Val := hl_val%
  λ s, let hd := !s;
    match hd with
    | none() => none()
    | some(l) => let p := !l; let x := fst(p); s ← snd(p); some(x)

/-- Rocq: `enqueue`. -/
def enqueue : Val := push

/-- Rocq: `run`. -/
def run : Val := hl_val%
  rec run q :=
    match &pop q with
    | none() => #()
    | some(f) => (f #(); run q)

/-- Rocq: `mkqueue`. -/
def mkqueue : Val := hl_val% λ _, &newStack #()

/-! ## Specifications -/

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

variable {GF : BundledGFunctors.{u}} [Hheap : HeapLangTGS GF] [Htc : TcGS.{w} GF]

/-- Rocq: `stack_contents`. -/
def stackContents (hd : Val) : List Val → (Val → IProp GF) → IProp GF
  | [], _ => iprop(⌜hd = hl_val(none())⌝)
  | x :: xs, φ => iprop(∃ (l : Loc) (hd' : Val), ⌜hd = hl_val(some(#l))⌝ ∗
      l ↦ some hl_val((&x, &hd')) ∗ φ x ∗ stackContents hd' xs φ)

theorem stackContents_nil (hd : Val) (φ : Val → IProp GF) :
    stackContents hd [] φ = iprop(⌜hd = hl_val(none())⌝) := rfl

theorem stackContents_cons (hd x : Val) (xs : List Val) (φ : Val → IProp GF) :
    stackContents hd (x :: xs) φ = iprop(∃ (l : Loc) (hd' : Val), ⌜hd = hl_val(some(#l))⌝ ∗
      l ↦ some hl_val((&x, &hd')) ∗ φ x ∗ stackContents hd' xs φ) := rfl

/-- Rocq: `stack`. -/
def stack (l : Loc) (xs : List Val) (φ : Val → IProp GF) : IProp GF :=
  iprop(∃ hd, l ↦ some hd ∗ stackContents hd xs φ)

/-- Rocq: `new_stack_spec`. -/
theorem new_stack_spec (φ : Val → IProp GF) :
    ⊢ tcwp (ι := heapRefIrisGS) (G := Htc) .NotStuck ⊤ hl(v(&newStack) #())
      fun v => iprop(∃ l : Loc, ⌜v = hl_val(#l)⌝ ∗ stack l [] φ) := by
  simp only [stack, stackContents_nil]
  unfold newStack
  twp_pures
  twp_apply rwp_alloc
  iintro %l Hl
  iexists l
  isplitr
  · ipureintro; rfl
  iexists hl_val(none())
  iframe
  ipureintro; rfl

/-- Rocq: `push_spec`. -/
theorem push_spec (l : Loc) (xs : List Val) (φ : Val → IProp GF) (x : Val) :
    stack l xs φ ∗ φ x ⊢ rswp (src := tcSource.{w}) (ι := heapRefIrisGS) 0 .NotStuck ⊤
      hl(v(&push) #l v(&x)) fun v => iprop(⌜v = hl_val(#())⌝ ∗ stack l (x :: xs) φ) := by
  simp only [stack, stackContents_cons]
  iintro ⟨Hstack, Hφ⟩
  unfold push
  icases Hstack with ⟨%hd, Hl, Hcont⟩
  twp_pure
  twp_pures
  twp_apply rwp_load $$ Hl
  iintro Hl
  twp_pures
  twp_apply rwp_alloc
  iintro %r Hr
  twp_pures
  twp_apply rwp_store $$ Hl
  iintro Hl
  isplitr
  · ipureintro; rfl
  iexists hl_val(some(#r))
  iframe Hl
  iexists r, hd
  iframe
  ipureintro; rfl

/-- Rocq: `pop_element_spec`. -/
theorem pop_element_spec (l : Loc) (xs : List Val) (φ : Val → IProp GF) (x : Val) :
    stack l (x :: xs) φ ⊢ rswp (src := tcSource.{w}) (ι := heapRefIrisGS) 0 .NotStuck ⊤
      hl(v(&pop) #l) fun v => iprop(⌜v = hl_val(some(&x))⌝ ∗ φ x ∗ stack l xs φ) := by
  simp only [stack, stackContents_cons]
  iintro Hstack
  unfold pop
  icases Hstack with ⟨%hd, Hl, Hcont⟩
  icases Hcont with ⟨%r, %hd', %rfl, Hr, Hφ, Hcont⟩
  twp_pure
  twp_apply rwp_load $$ Hl
  iintro Hl
  twp_pures
  twp_apply rwp_load $$ Hr
  iintro Hr
  twp_pures
  twp_apply rwp_store $$ Hl
  iintro Hl
  twp_pures
  isplitr
  · ipureintro; rfl
  iframe Hφ
  iexists hd'
  iframe

/-- Rocq: `pop_empty_spec`. -/
theorem pop_empty_spec (l : Loc) (φ : Val → IProp GF) :
    stack l [] φ ⊢ rswp (src := tcSource.{w}) (ι := heapRefIrisGS) 0 .NotStuck ⊤
      hl(v(&pop) #l) fun v => iprop(⌜v = hl_val(none())⌝ ∗ stack l [] φ) := by
  simp only [stack, stackContents_nil]
  iintro Hstack
  unfold pop
  icases Hstack with ⟨%hd, Hl, %rfl⟩
  twp_pure
  twp_apply rwp_load $$ Hl
  iintro Hl
  twp_pures
  isplitr
  · ipureintro; rfl
  iexists hl_val(none())
  iframe
  ipureintro; rfl

variable [Hseq : SeqG GF]

/-- Rocq: `queue`. -/
def queue (q : Val) : IProp GF :=
  iprop(∃ l : Loc, ⌜q = hl_val(#l)⌝ ∗ NonAtomicInvariant.inv Hseq.name (nroot.@l)
    iprop(∃ xs, stack l xs fun f => iprop(tc (GF := GF) (1 : Ordinal.{w}) ∗
      tseq.{w} ⊤ hl(v(&f) #()) fun _ => iprop(True))))

instance queue_persistent (q : Val) : Persistent (queue.{w} (GF := GF) q) := by
  unfold queue; infer_instance

/-- Rocq: `run_spec`. -/
theorem run_spec (q : Val) :
    queue.{w} (GF := GF) q ∗ tc (GF := GF) 1 ⊢
      tseq.{w} ⊤ hl(v(&run) v(&q)) fun v => iprop(⌜v = hl_val(#())⌝) := by
  unfold queue tseq seq
  iintro ⟨#⟨%l, %rfl, #I⟩, Hc⟩ Hna
  unfold run
  iloeb as IH generalizing Hc Hna
  twp_pure
  twp_bind (v(&pop) #l)
  imod NonAtomicInvariant.inv_acc_open (nclose_subset_top _) (nclose_subset_top _) $$ I Hna
    with Hinv
  iapply tcwp_burn_credit rfl $$ Hc
  inext
  icases Hinv with ⟨⟨%xs, Hstack⟩, Hna, Hclose⟩
  cases xs with
  | nil =>
    ihave Hwp := pop_empty_spec $$ Hstack
    iapply rswp_wand $$ Hwp
    iintro %v ⟨%rfl, Hstack⟩
    imod Hclose $$ [Hstack Hna] with Hna
    · iframe Hna
      inext
      iexists []
      iexact Hstack
    twp_pures
    iframe Hna
    ipureintro; rfl
  | cons f xs =>
    ihave Hwp := pop_element_spec $$ Hstack
    iapply rswp_wand $$ Hwp
    iintro %v ⟨%rfl, ⟨Hone, Hwp⟩, Hstack⟩
    imod Hclose $$ [Hstack Hna] with Hna
    · iframe Hna
      inext
      iexists xs
      iexact Hstack
    twp_pures
    ihave Hwp := Hwp $$ Hna
    twp_apply rwp_wand $$ Hwp
    iintro %v ⟨Hna, -⟩
    twp_pure
    twp_pure
    iapply IH $$ Hone Hna

/-- Rocq: `enqueue_spec`. -/
theorem enqueue_spec (q f : Val) :
    queue.{w} (GF := GF) q ∗ tc (GF := GF) 1 ∗ tc (GF := GF) 1 ∗
      tseq.{w} ⊤ hl(v(&f) #()) (fun _ => iprop(True)) ⊢
      tseq.{w} ⊤ hl(v(&enqueue) v(&q) v(&f)) fun v => iprop(⌜v = hl_val(#())⌝) := by
  unfold queue
  iintro ⟨#⟨%l, %rfl, #I⟩, Hc, Hf⟩
  unfold tseq seq
  iintro Hna
  imod NonAtomicInvariant.inv_acc_open (nclose_subset_top _) (nclose_subset_top _) $$ I Hna
    with Hinv
  iapply tcwp_burn_credit rfl $$ Hc
  inext
  icases Hinv with ⟨⟨%xs, Hstack⟩, Hna, Hclose⟩
  ihave Hpush := push_spec l xs _ f $$ [Hstack Hf]
  · iframe Hstack
    iexact Hf
  unfold enqueue
  iapply rswp_strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ Hpush
  iintro %v ⟨%rfl, Hstack⟩
  imod Hclose $$ [Hstack Hna] with Hna
  · iframe Hna
    inext
    iexists (f :: xs)
    iexact Hstack
  imodintro
  iframe Hna
  ipureintro; rfl

/-- Rocq: `mkqueue_spec`. -/
theorem mkqueue_spec :
    ⊢ tseq.{w} (GF := GF) ⊤ hl(v(&mkqueue) #()) fun q => queue.{w} q := by
  unfold tseq seq
  iintro Hna
  unfold mkqueue
  twp_pure
  ihave Hwp := new_stack_spec (GF := GF) (Htc := Htc)
    (fun f => iprop(tc (GF := GF) (1 : Ordinal.{w}) ∗
      tseq.{w} ⊤ hl(v(&f) #()) fun _ => iprop(True)))
  iapply rwp_strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ Hwp
  iintro %v ⟨%l, %rfl, Hstack⟩
  ihave HI : ▷ (∃ xs, stack l xs fun f => iprop(tc (GF := GF) (1 : Ordinal.{w}) ∗
      tseq.{w} ⊤ hl(v(&f) #()) fun _ => iprop(True))) $$ [Hstack]
  · inext
    iexists []
    iexact Hstack
  imod NonAtomicInvariant.inv_alloc (p := Hseq.name) (N := nroot.@l) $$ HI with #I
  imodintro
  iframe Hna
  unfold queue
  iexists l
  isplitr
  · ipureintro; rfl
  iexact I

/-! ## An open example -/

/-- Rocq: `for_loop`. -/
def forLoop : Val := hl_val%
  rec loop f n :=
    if n ≤ #(0 : Int) then #()
    else let m := n - #1; f #(); loop f m

/-- Rocq: `example`: enqueue `n` callbacks, for a number `n` chosen by external code. -/
def openExample (external print q : Val) : Exp := hl(
  let n := v(&external) #();
  v(&forLoop) (λ _, v(&enqueue) v(&q) (λ _, v(&print) #(42 : Int))) n)

theorem nat_cast_two_mul_succ (n : Nat) :
    ((2 * (n + 1) : Nat) : Ordinal.{w}) = Order.succ (Order.succ ((2 * n : Nat) : Ordinal.{w})) := by
  rw [Order.succ_eq_add_one, Order.succ_eq_add_one, show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
  push_cast
  rfl

/-- Rocq: `example_spec`. -/
theorem example_spec (external print q : Val) :
    queue.{w} (GF := GF) q ∗ tc (GF := GF) Ordinal.omega0.{w} ∗
      tseq.{w} ⊤ hl(v(&external) #()) (fun v => iprop(∃ n : Nat, ⌜v = hl_val(#(n : Int))⌝)) ∗
      □ (∀ n : Int, tseq.{w} ⊤ hl(v(&print) #n) fun _ => iprop(True)) ⊢
      tseq.{w} ⊤ (openExample external print q) fun _ => iprop(True) := by
  iintro ⟨#Q, Hc, Hwp, #Hprint⟩
  unfold tseq seq openExample
  iintro Hna
  twp_bind (v(&external) #())
  ihave Hwp := Hwp $$ Hna
  twp_apply rwp_wand $$ Hwp
  iintro %v ⟨Hna, %n, %rfl⟩
  twp_pure
  twp_pure
  twp_pure
  iapply tc_weaken (β := ((2 * n : Nat) : Ordinal.{w})) rfl (Ordinal.natCast_lt_omega0 _).le
  iframe Hc
  iintro Hc
  iinduction n generalizing Hc Hna with
  | zero =>
    twp_rec
    twp_pures
    rw [decide_eq_true (show ((0 : Nat) : Int) ≤ 0 by simp)]
    twp_pures
    iframe Hna
  | succ n ih =>
    rw [nat_cast_two_mul_succ]
    icases (tc_succ _).mp $$ Hc with ⟨Hc, Ho⟩
    icases (tc_succ _).mp $$ Hc with ⟨Hc, Ho'⟩
    twp_rec
    twp_pures
    rw [decide_eq_false (show ¬ (((n + 1 : Nat) : Int) ≤ 0) by omega)]
    twp_pures
    twp_bind (v(&enqueue) v(&q) _)
    ihave Hen := enqueue_spec (Htc := Htc) q hl_val(λ _, v(&print) #(42 : Int)) $$ [Ho Ho']
    · iframe Q Ho Ho'
      unfold tseq seq
      iintro Hna
      twp_pures
      iapply Hprint $$ %42 Hna
    unfold tseq seq
    ihave Hen := Hen $$ Hna
    twp_apply rwp_wand $$ Hen
    iintro %v ⟨Hna, -⟩
    twp_pure
    twp_pure
    rw [show (((n + 1 : Nat) : Int) - 1) = (n : Int) by omega]
    iapply ih $$ Hc Hna

/-! ## A reentrant example -/

/-- Rocq: `reentrant_example`: a callback that enqueues another callback. -/
def reentrantExample (print : Val) : Exp := hl(
  let q := v(&mkqueue) #();
  let f := (λ _, v(&enqueue) q (λ _, v(&print) #(42 : Int)));
  v(&enqueue) q f;
  v(&run) q)

/-- `enqueue_spec` in weakest precondition form, for `twp_apply`. -/
theorem enqueue_rwp (q f : Val) (Φ : Val → IProp GF) :
    ⊢ queue.{w} (GF := GF) q -∗ tc (GF := GF) 1 -∗ tc (GF := GF) 1 -∗
      tseq.{w} ⊤ hl(v(&f) #()) (fun _ => iprop(True)) -∗ NonAtomicInvariant.own Hseq.name ⊤ -∗
      (∀ v, NonAtomicInvariant.own Hseq.name ⊤ ∗ ⌜v = hl_val(#())⌝ -∗ Φ v) -∗
      rwp (src := tcSource.{w}) (ι := heapRefIrisGS) .NotStuck ⊤ hl(v(&enqueue) v(&q) v(&f)) Φ := by
  iintro Hq Hc1 Hc2 Hf Hna HΦ
  ihave H := enqueue_spec (Htc := Htc) q f $$ [Hq Hc1 Hc2 Hf]
  · iframe
  unfold tseq seq
  ihave H := H $$ Hna
  iapply rwp_wand $$ H HΦ

omit Hheap Hseq in
theorem tc_nat_succ (n : Nat) :
    tc (GF := GF) ((n + 1 : Nat) : Ordinal.{w}) ⊣⊢ tc (GF := GF) (n : Ordinal.{w}) ∗ tc 1 := by
  rw [Nat.cast_succ, ← Order.succ_eq_add_one]
  exact tc_succ _

/-- Rocq: `reentrant_example_spec`. -/
theorem reentrant_example_spec (print : Val) :
    tc (GF := GF) Ordinal.omega0.{w} ∗
      □ (∀ n : Int, tseq.{w} ⊤ hl(v(&print) #n) fun _ => iprop(True)) ⊢
      tseq.{w} ⊤ (reentrantExample print) fun _ => iprop(True) := by
  iintro ⟨Hc, #Hprint⟩
  unfold reentrantExample
  have Hmk := mkqueue_spec (GF := GF) (Htc := Htc) (Hseq := Hseq)
  unfold tseq seq at Hmk ⊢
  iintro Hna
  twp_bind (v(&mkqueue) #())
  ihave H := Hmk $$ Hna
  twp_apply rwp_wand $$ H
  iintro %q ⟨Hna, #Hq⟩
  twp_pures
  iapply tc_weaken (β := ((5 : Nat) : Ordinal.{w})) rfl (Ordinal.natCast_lt_omega0 _).le
  iframe Hc
  iintro Hc
  icases (tc_nat_succ 4).mp $$ Hc with ⟨Hc, Hc5⟩
  icases (tc_nat_succ 3).mp $$ Hc with ⟨Hc, Hc4⟩
  icases (tc_nat_succ 2).mp $$ Hc with ⟨Hc, Hc3⟩
  icases (tc_nat_succ 1).mp $$ Hc with ⟨Hc, Hc2⟩
  icases (tc_nat_succ 0).mp $$ Hc with ⟨-, Hc1⟩
  twp_apply enqueue_rwp $$ Hq Hc1 Hc2 [Hc3 Hc4 Hprint] Hna
  · unfold tseq seq
    iintro Hna
    twp_pures
    twp_apply enqueue_rwp $$ Hq Hc3 Hc4 [Hprint] Hna
    · unfold tseq seq
      iintro Hna
      twp_pures
      iapply Hprint $$ %42 Hna
    iintro %v ⟨Hna, -⟩
    iframe Hna
  iintro %v ⟨Hna, %rfl⟩
  twp_pures
  ihave H := run_spec (Htc := Htc) q $$ [Hc5]
  · iframe Hq Hc5
  unfold tseq seq
  ihave H := H $$ Hna
  iapply rwp_wand $$ H
  iintro %v ⟨Hna, -⟩
  iframe Hna

end Iris.Transfinite.Termination
