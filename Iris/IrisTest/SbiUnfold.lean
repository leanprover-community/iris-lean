/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.BI.SbiUnfold

@[expose] public section

/-!
# Tests for `sbi_unfold`

Each test states the goal `sbi_unfold` is expected to leave as a hypothesis, so
that `exact h` pins the interpretation the instances produce. The tests in
`RocqTests` mirror `tests/sbi_unfold.v`, including the placement of every down
closure.
-/

namespace IrisTest
open Iris BI OFE CMRA

/-- The interpretation `sbi_unfold` gives to `▷`. Only used to state the expected
goals below: writing the `match` under a `∃` binder makes the binder part of it. -/
private def laterP (φ : Nat → Prop) : Nat → Prop
  | 0 => True
  | m + 1 => φ m

section RocqTests
variable [Sbi PROP] {A : Type _} [OFE A] (x y z : A)

/-! ### These should *not* include a `∀ m ≤ n` -/

/- `test_impl` -/
example (h : ∀ n, x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z) :
    x ≡ y ⊢@{PROP} iprop(y ≡ z → x ≡ z) := by
  sbi_unfold; exact h

/- `test_impl_impl_and` -/
example (h : ∀ n, x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z ∧ z ≡{n}≡ x) :
    ⊢@{PROP} iprop(x ≡ y → y ≡ z → x ≡ z ∧ z ≡ x) := by
  sbi_unfold; exact h

/- `test_exist_impl`, with the `∃` in the hypothesis -/
example (h : ∀ n, (∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) → x ≡{n}≡ z) :
    ⊢@{PROP} iprop((∃ y, x ≡ y ∧ y ≡ z) → x ≡ z) := by
  sbi_unfold; exact h

/- `test_exist_impl`, with the `∃` in the conclusion -/
example (h : ∀ n, x ≡{n}≡ z → ∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) :
    ⊢@{PROP} iprop(x ≡ z → ∃ y, x ≡ y ∧ y ≡ z) := by
  sbi_unfold; exact h

/- `test_si_pure_exist`. The `<si_pure>` leaves are transparent, so this gives
the same goal as the version without them. -/
example (h : ∀ n, (∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) → x ≡{n}≡ z) :
    ⊢@{PROP} iprop(<si_pure> (∃ y, <si_pure> (x ≡ y) ∧ y ≡ z) → x ≡ z) := by
  sbi_unfold; exact h

/- `test_equiv_exist` -/
example (h : ∀ n, x ≡{n}≡ z ↔ ∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) :
    x ≡ z ⊣⊢@{PROP} iprop(∃ y, x ≡ y ∧ y ≡ z) := by
  sbi_unfold; exact h

/- `test_iff_exist` -/
example (h : ∀ n, x ≡{n}≡ z ↔ ∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) :
    ⊢@{PROP} iprop(x ≡ z ↔ ∃ y, x ≡ y ∧ y ≡ z) := by
  sbi_unfold; exact h

/- `test_wand_iff_exist` -/
example (h : ∀ n, x ≡{n}≡ z ↔ ∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) :
    ⊢@{PROP} iprop(x ≡ z ∗-∗ ∃ y, x ≡ y ∧ y ≡ z) := by
  sbi_unfold; exact h

/- `test_iff_exist_later` -/
example (h : ∀ n, laterP (fun m => x ≡{m}≡ z) n
                    ↔ ∃ y, laterP (fun m => x ≡{m}≡ y ∧ y ≡{m}≡ z) n) :
    ⊢@{PROP} iprop(▷ (x ≡ z) ∗-∗ ∃ y, ▷ (x ≡ y ∧ y ≡ z)) := by
  sbi_unfold; exact h

/-! ### These should include a `∀ m ≤ n`

An implication under an `∃`, or under a `∀` in a hypothesis, cannot avoid the
closure: neither connective commutes with `∀`. -/

/- `test_exist_impl` -/
example (h : ∀ n, x ≡{n}≡ z → ∃ y, ∀ m ≤ n, x ≡{m}≡ y → y ≡{m}≡ z) :
    ⊢@{PROP} iprop(x ≡ z → ∃ y, x ≡ y → y ≡ z) := by
  sbi_unfold; exact h

/- `test_forall_impl` -/
example (h : ∀ n, (∀ y, ∀ m ≤ n, x ≡{m}≡ y → y ≡{m}≡ z) → x ≡{n}≡ z) :
    ⊢@{PROP} iprop((∀ y, x ≡ y → y ≡ z) → x ≡ z) := by
  sbi_unfold; exact h

end RocqTests

section LeanTests
variable [Sbi PROP] [CMRA A] [OFE B]

/- `prod_validI`. -/
example (x : A × A) (h : ∀ n, ✓{n} x ↔ ✓{n} x.1 ∧ ✓{n} x.2) :
    ✓ x ⊣⊢@{PROP} ✓ x.1 ∧ ✓ x.2 := by
  sbi_unfold; exact h

/- The example from the module docstring: nested implications contribute no
closure. -/
example (x y : A × A) (h : ∀ n, x.1 ≼{n} y.1 → x.2 ≼{n} y.2 → x ≼{n} y) :
    ⊢@{PROP} iprop(x.1 ≼ y.1 → x.2 ≼ y.2 → x ≼ y) := by
  sbi_unfold; exact h

/- `⌜_⌝` and `∧`. -/
example (a b : B) (φ : Prop) (h : ∀ n, φ ∧ a ≡{n}≡ b → a ≡{n}≡ b) :
    iprop(⌜φ⌝ ∧ a ≡ b) ⊢@{PROP} iprop(a ≡ b) := by
  sbi_unfold; exact h

example : ⊢@{PROP} iprop(∃ (_h : True), ⌜True⌝) := by
  sbi_unfold
  exact fun _ => ⟨True.intro, True.intro⟩

/- `∗` becomes `∧`. -/
example (a b : B) (h : ∀ n, a ≡{n}≡ b ∧ b ≡{n}≡ a → a ≡{n}≡ b) :
    iprop((a ≡ b) ∗ (b ≡ a)) ⊢@{PROP} iprop(a ≡ b) := by
  sbi_unfold; exact h

/- `-∗` becomes `→`, and the conclusion of an entailment keeps no closure. -/
example (a b : B) (h : ∀ n, a ≡{n}≡ b → a ≡{n}≡ b → b ≡{n}≡ a) :
    iprop(a ≡ b) ⊢@{PROP} iprop((a ≡ b) -∗ (b ≡ a)) := by
  sbi_unfold; exact h

/- A closure next to a leaf under `∧` still merges away, because `∧` passes the
indicator down to both conjuncts. -/
example (a b c d : B) (h : ∀ n, (a ≡{n}≡ b → c ≡{n}≡ d) ∧ c ≡{n}≡ d) :
    ⊢@{PROP} iprop((a ≡ b → c ≡ d) ∧ (c ≡ d)) := by
  sbi_unfold; exact h

/- A `▷` in the hypothesis of an implication needs no closure either. -/
example (a b c d e f : B)
    (h : ∀ n, laterP (fun m => a ≡{m}≡ b) n → c ≡{n}≡ d → e ≡{n}≡ f) :
    ⊢@{PROP} iprop(▷ (a ≡ b) → (c ≡ d → e ≡ f)) := by
  sbi_unfold; exact h

/- Under `∨` the closure stays: `∨` does not commute with `∀`. -/
example (a b c d : B) (h : ∀ n, (∀ m ≤ n, a ≡{m}≡ b → c ≡{m}≡ d) ∨ a ≡{n}≡ b) :
    ⊢@{PROP} iprop((a ≡ b → c ≡ d) ∨ (a ≡ b)) := by
  sbi_unfold; exact h

/- A goal in the model itself: the low-priority `SiProp` instance applies. -/
example (Pi Qi : SiProp) (h : ∀ n, Pi.holds n ∧ Qi.holds n → Pi.holds n) :
    iprop(Pi ∧ Qi) ⊢@{SiProp} Pi := by
  sbi_unfold; exact h

/- A `match` has to be case split before unfolding. -/
example (mx : Option B) :
    (match mx with | none => iprop(⌜True⌝) | some a => iprop(a ≡ a)) ⊢@{PROP}
      (match mx with | none => iprop(⌜True⌝) | some a => iprop(a ≡ a)) := by
  cases mx <;> sbi_unfold <;> intro _ <;> exact id

/- `sbi_unfold` fails on a goal that is not a BI entailment. -/
example : True := by
  fail_if_success sbi_unfold
  trivial

end LeanTests

end IrisTest
