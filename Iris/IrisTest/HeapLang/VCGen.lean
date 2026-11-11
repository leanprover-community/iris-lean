/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.ProgramLogic.VCGen
public import Iris.HeapLang.VCGen
public import Iris.Examples.HeapLang

@[expose] public section

/-!
# Examples

HeapLang programs verified with `vcgen`, among them the heap programs of `Iris.Examples.HeapLang`
(`counter`, `swap`, `fibonacci`), which iris-lean defines without specifications.

Specifications come in two forms:

* **Frame form** `hl⦃ P ⦄ e ⦃ fun _ => P' ⦄`, for a call whose result the caller ignores.
  The frameproc frames every resource of the caller that `P` does not mention (`client_spec`).
* **Texan form** `hl⦃ P ∗ (P' -∗ Q v) ⦄ e ⦃ Q ⦄`, quantified over `Q`, for a call that returns
  `v`. The continuation `Q` receives the value `v` itself, so later specifications match on it
  (`fact_spec`, `loop_spec`).

A recursive function is verified by induction. The induction hypothesis is passed to `vcgen` as
the specification of the recursive call, after the top-level call is unfolded (`rec_call₂`, or the
β-specification for the shape of the function).
-/

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Lean.Order Std.WP Iris.VCGen Iris.HeapLang.VCGen
open Iris.Examples.HeapLang (counter)

set_option experimental.vcgen true
set_option linter.heapLang.freeVars false

namespace IrisTest.VCGen

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF]

/-! ## Pure programs -/

example : hl⦃ (BIBase.emp : IProp GF) ⦄ hl(if #1 < #2 then #3 else #4) ⦃ fun v => ⌜v = hl_val(#3)⌝ ⦄ := by
  vcgen

example : hl⦃ (BIBase.emp : IProp GF) ⦄
    hl(let x := #1; let y := x + #2; let f := (λ z, z + x + y); f (f #10))
    ⦃ fun v => ⌜v = hl_val(#18)⌝ ⦄ := by
  vcgen

/-! ## Masks and stuckness

The program part of a triple takes the forms of iris's `WP`: `e @ E` at mask `E`, and `e @ E ?` at
stuckness `MaybeStuck`. -/

example (E : CoPset) :
    hl⦃ (BIBase.emp : IProp GF) ⦄ hl(if #1 < #2 then #3 else #4) @ E ⦃ fun v => ⌜v = hl_val(#3)⌝ ⦄ := by
  vcgen

example (E : CoPset) :
    hl⦃ (BIBase.emp : IProp GF) ⦄ hl(#1 + #2) @ E ? ⦃ fun v => ⌜v = hl_val(#3)⌝ ⦄ := by
  vcgen

/-! ## Heap programs -/

theorem counter_spec : hl⦃ (BIBase.emp : IProp GF) ⦄ counter ⦃ fun v => ⌜v = hl_val(#1)⌝ ⦄ := by
  unfold counter
  vcgen

/-- `Iris.Examples.HeapLang.swap` as a value, so that a caller's substitution leaves it intact. -/
def swapV : Val := hl_val(λ l1 l2, let tmp := !l1; l1 ← !l2; l2 ← tmp)

theorem swap_spec (l₁ l₂ : Loc) (a b : Val) :
    hl⦃ iprop(l₁ ↦ some a ∗ l₂ ↦ some b) ⦄ hl(v(&swapV) #l₁ #l₂)
      ⦃ fun _ => iprop(l₁ ↦ some b ∗ l₂ ↦ some a) ⦄ := by
  unfold swapV
  vcgen with finish

/-- A caller of `swap` that owns a third cell. -/
def client : Exp := hl(λ l₁ l₂ l₃, v(&swapV) l₁ l₂; !l₃ + !l₁)

theorem client_spec (l₁ l₂ l₃ : Loc) :
    hl⦃ iprop(l₁ ↦ some hl_val(#1) ∗ l₂ ↦ some hl_val(#2) ∗ l₃ ↦ some hl_val(#3)) ⦄
      hl(&client #l₁ #l₂ #l₃)
    ⦃ fun v => ⌜v = hl_val(#5)⌝ ⊓
        iprop(l₁ ↦ some hl_val(#2) ∗ l₂ ↦ some hl_val(#1) ∗ l₃ ↦ some hl_val(#3)) ⦄ := by
  unfold client
  vcgen [swap_spec] with finish

/-! ## Recursion -/

def factV : Val := hl_val(rec fact n := if n ≤ #0 then #1 else n * fact (n - #1))

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

@[grind =] theorem fact_zero : fact 0 = 1 := rfl

theorem fact_of_pos (k : Int) (hk : 0 < k) : (fact k.toNat : Int) = k * fact (k - 1).toNat := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, k = n + 1 := ⟨(k - 1).toNat, by omega⟩
  simp [fact]

theorem fact_spec (N : Nat) : ∀ k : Int, 0 ≤ k → k.toNat < N → ∀ Q : Val → IProp GF,
    hl⦃ Q (.lit (.int (fact k.toNat))) ⦄ hl(v(&factV) #k) ⦃ Q ⦄ := by
  induction N with
  | zero => intro k _ h; omega
  | succ N ih =>
    intro k hk hN Q
    unfold factV at ih ⊢
    exact rec_call₁ _ _ _ _ (by vcgen [ih] with finish [fact_of_pos])

/-- Add `k + (k - 1) + ⋯ + 1` to the cell `l`. -/
def addDownV : Val :=
  hl_val(rec loop l := λ k, if k ≤ #0 then #() else (l ← !l + k; loop l (k - #1)))

def tri : Nat → Int
  | 0 => 0
  | n + 1 => (n + 1 : Int) + tri n

@[grind =] theorem tri_zero : tri 0 = 0 := rfl

theorem tri_of_pos (k : Int) (hk : 0 < k) : tri k.toNat = k + tri (k - 1).toNat := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, k = n + 1 := ⟨(k - 1).toNat, by omega⟩
  simp [tri]

theorem addDown_spec (N : Nat) : ∀ (l : Loc) (k acc : Int), 0 ≤ k → k.toNat < N →
    hl⦃ (l ↦ some (Val.lit (.int acc)) : IProp GF) ⦄ hl(v(&addDownV) #l #k)
      ⦃ fun _ => l ↦ some (Val.lit (.int (acc + tri k.toNat))) ⦄ := by
  induction N with
  | zero => intro l k acc _ h; omega
  | succ N ih =>
    intro l k acc hk hN
    unfold addDownV at ih ⊢
    exact rec_call₂ _ _ _ _ _ _ (by vcgen [ih] with finish [tri_of_pos])

/-! ## `fibonacci`

`Iris.Examples.HeapLang.fibonacci` keeps its state in three cells and loops through a local
recursive closure that captures them. The loop specification names that closure as `vcgen`
builds it: its body is the loop body under the substitution of the cells and the bound. -/

def loopBody : Exp :=
  hl(if !i < n then
        let tmp := !b;
        b ← !a + !b;
        a ← tmp;
        i ← !i + #1;
        loop #()
      else
        !a)

/-- `Iris.Examples.HeapLang.fibonacci` with its loop body named. -/
def fibV : Val := hl_val(λ n,
    let a := ref(#0);
    let b := ref(#1);
    let i := ref(#0);
    (rec loop _ := &loopBody) #())

def fib : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

@[grind =] theorem fib_zero : fib 0 = 0 := rfl
@[grind =] theorem fib_one : fib 1 = 1 := rfl

theorem fib_succ_succ (j : Int) (hj : 0 ≤ j) :
    fib ((j + 1).toNat + 1) = fib j.toNat + fib (j.toNat + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, j = m := ⟨j.toNat, by omega⟩
  simp [fib]

/-- The loop closure, after `vcgen` substituted the cells `a b i` and the bound `n`. -/
abbrev loopClo (n : Int) (la lb li : Loc) : Val :=
  .rec_ (.named "loop") .anon
    (msubst (dropB (.named "loop") .anon
      [("i", .lit (.loc li)), ("b", .lit (.loc lb)), ("a", .lit (.loc la)), ("n", .lit (.int n))])
      loopBody)

theorem loop_spec (n : Int) (la lb li : Loc) (N : Nat) :
    ∀ (j x y : Int), 0 ≤ j → j ≤ n → (n - j).toNat < N →
      x = fib j.toNat → y = fib (j.toNat + 1) → ∀ Q : Val → IProp GF,
      hl⦃ iprop(la ↦ some (Val.lit (.int x)) ∗ lb ↦ some (Val.lit (.int y)) ∗
          li ↦ some (Val.lit (.int j)) ∗ Q (Val.lit (.int (fib n.toNat)))) ⦄
        (Exp.app (ToVal.ofVal (loopClo n la lb li)) (ToVal.ofVal (.lit .unit))) ⦃ Q ⦄ := by
  induction N with
  | zero => intro j _ _ _ h; omega
  | succ N ih =>
    intro j x y hj hjn hN hx hy Q
    unfold loopClo at ih ⊢
    refine ⟨PartialOrder.rel_trans ?_ (beta_msubst_na_spec _ _ _ _).le_wp⟩
    unfold loopBody at ih ⊢
    vcgen [ih] with finish [fib_succ_succ]

theorem fib_spec (n : Int) (hn : 0 ≤ n) (Q : Val → IProp GF) :
    hl⦃ Q (Val.lit (.int (fib n.toNat))) ⦄ hl(v(&fibV) #n) ⦃ Q ⦄ := by
  have := fun la lb li => loop_spec (GF := GF) n la lb li ((n + 1).toNat)
  unfold loopClo loopBody at this
  unfold fibV loopBody
  vcgen [this] with finish

end IrisTest.VCGen
