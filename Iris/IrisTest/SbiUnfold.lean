/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.Cmra
public meta import Iris.BI.SbiUnfold

@[expose] public section

/-!
# Golden tests for `sbi_norm`
-/

namespace IrisTest.SbiUnfold
open Iris Iris.BI Iris.OFE Iris.CMRA

variable [Sbi PROP] [CMRA A] [OFE B]


/-- `prod_validI`. -/
example (x : A × A) :
    (✓ x ⊣⊢@{PROP} ✓ x.1 ∧ ✓ x.2)
      ↔ (∀ n, ✓{n} x ↔ ✓{n} x.1 ∧ ✓{n} x.2) := by
  simp only [sbi_norm]

/-- The example from the header of Rocq's `sbi_unfold.v`. Nested implications
would each contribute a down closure; `downClose_imp` removes them. -/
example (x y : A × A) :
    (⊢@{PROP} x.1 ≼ y.1 → x.2 ≼ y.2 → x ≼ y)
      ↔ (∀ n, x.1 ≼{n} y.1 → x.2 ≼{n} y.2 → x ≼{n} y) := by
  simp only [sbi_norm]

/-- `⌜_⌝` and `∧`. -/
example (a b : B) (φ : Prop) :
    (iprop(⌜φ⌝ ∧ a ≡ b) ⊢@{PROP} iprop(a ≡ b))
      ↔ (∀ n, φ ∧ a ≡{n}≡ b → a ≡{n}≡ b) := by
  simp only [sbi_norm]

/-- `∗` becomes `∧`. -/
example (a b : B) :
    (iprop((a ≡ b) ∗ (b ≡ a)) ⊢@{PROP} iprop(a ≡ b))
      ↔ (∀ n, a ≡{n}≡ b ∧ b ≡{n}≡ a → a ≡{n}≡ b) := by
  simp only [sbi_norm]

/-- `-∗` becomes `→`, and the conclusion of an entailment keeps no down closure. -/
example (a b : B) :
    (iprop(a ≡ b) ⊢@{PROP} iprop((a ≡ b) -∗ (b ≡ a)))
      ↔ (∀ n, a ≡{n}≡ b → a ≡{n}≡ b → b ≡{n}≡ a) := by
  simp only [sbi_norm]

/-- `↔` stays an `↔`. -/
example (a b : B) :
    (⊢@{PROP} iprop((a ≡ b) ↔ (b ≡ a))) ↔ (∀ n, a ≡{n}≡ b ↔ b ≡{n}≡ a) := by
  simp only [sbi_norm]

/-- Two down closures under a `∧` merge, then the leading `∀ n` absorbs them.
The adjunction cannot reach this case; `downClose_and` is what handles it. -/
example (a b c d : B) :
    (⊢@{PROP} iprop((a ≡ b → c ≡ d) ∧ (c ≡ d → a ≡ b)))
      ↔ (∀ n, (a ≡{n}≡ b → c ≡{n}≡ d) ∧ (c ≡{n}≡ d → a ≡{n}≡ b)) := by
  simp only [sbi_norm]

/-- A down closure under `∀` merges. -/
example (a b : B) :
    (⊢@{PROP} iprop(∀ i : Nat, (a ≡ b → ⌜i = 0⌝)))
      ↔ (∀ n, ∀ i : Nat, a ≡{n}≡ b → i = 0) := by
  simp only [sbi_norm]

/-- Under `∨` the closure stays, and prints as `∀ m ≤ n`. `∨` does not commute
with `∀`, so Rocq leaves the same residue. -/
example (a b c d : B) :
    (⊢@{PROP} iprop((a ≡ b → c ≡ d) ∨ (a ≡ b)))
      ↔ (∀ n, (∀ m ≤ n, a ≡{m}≡ b → c ≡{m}≡ d) ∨ a ≡{n}≡ b) := by
  simp only [sbi_norm]
  simp only [sbi_model]

/-- `▷` at an unknown step index. -/
example (a b : B) :
    (⊢@{PROP} iprop(▷ (a ≡ b))) ↔ (∀ n, SiProp.laterP (fun m => a ≡{m}≡ b) n) := by
  simp only [sbi_norm]

/-- `∃`. -/
example (a : B) :
    (⊢@{PROP} iprop(∃ c : B, a ≡ c)) ↔ (∀ n, ∃ c : B, a ≡{n}≡ c) := by
  simp only [sbi_norm]

section RocqTests
variable [Sbi PROP] {A : Type _} [OFE A] (x y z : A)

/-! ### These should *not* include a `∀ m ≤ n` -/

/-- `test_impl` -/
example : (x ≡ y ⊢@{PROP} iprop(y ≡ z → x ≡ z))
    ↔ (∀ n, x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z) := by
  simp only [sbi_norm]

/-- `test_impl_impl_and` -/
example : (⊢@{PROP} iprop(x ≡ y → y ≡ z → x ≡ z ∧ z ≡ x))
    ↔ (∀ n, x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z ∧ z ≡{n}≡ x) := by
  simp only [sbi_norm]

/-- `test_exist_impl`, with the `∃` in the hypothesis -/
example : (⊢@{PROP} iprop((∃ y, x ≡ y ∧ y ≡ z) → x ≡ z))
    ↔ (∀ n, (∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) → x ≡{n}≡ z) := by
  simp only [sbi_norm]

/-- `test_exist_impl`, with the `∃` in the conclusion -/
example : (⊢@{PROP} iprop(x ≡ z → ∃ y, x ≡ y ∧ y ≡ z))
    ↔ (∀ n, x ≡{n}≡ z → ∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) := by
  simp only [sbi_norm]

/-- `test_si_pure_exist`. Folding stops at a `<si_pure>` leaf, so this gives the
same goal as the version without one. -/
example : (⊢@{PROP} iprop(<si_pure> (∃ y, <si_pure> (x ≡ y) ∧ y ≡ z) → x ≡ z))
    ↔ (∀ n, (∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) → x ≡{n}≡ z) := by
  simp only [sbi_norm]

/-- `test_equiv_exist` -/
example : (x ≡ z ⊣⊢@{PROP} iprop(∃ y, x ≡ y ∧ y ≡ z))
    ↔ (∀ n, x ≡{n}≡ z ↔ ∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) := by
  simp only [sbi_norm]

/-- `test_iff_exist` -/
example : (⊢@{PROP} iprop(x ≡ z ↔ ∃ y, x ≡ y ∧ y ≡ z))
    ↔ (∀ n, x ≡{n}≡ z ↔ ∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) := by
  simp only [sbi_norm]

/-- `test_wand_iff_exist` -/
example : (⊢@{PROP} iprop(x ≡ z ∗-∗ ∃ y, x ≡ y ∧ y ≡ z))
    ↔ (∀ n, x ≡{n}≡ z ↔ ∃ y, x ≡{n}≡ y ∧ y ≡{n}≡ z) := by
  simp only [sbi_norm]

/-- `test_iff_exist_later` -/
example : (⊢@{PROP} iprop(▷ (x ≡ z) ∗-∗ ∃ y, ▷ (x ≡ y ∧ y ≡ z)))
    ↔ (∀ n, SiProp.laterP (fun m => x ≡{m}≡ z) n
              ↔ ∃ y, SiProp.laterP (fun m => x ≡{m}≡ y ∧ y ≡{m}≡ z) n) := by
  simp only [sbi_norm]

/-! ### These should include a `∀ m ≤ n`

An implication under an `∃`, or under a `∀` in a hypothesis, cannot merge
outward: neither connective commutes with `∀`. The closure that stays is what
`sbi_model` writes out. -/

/-- `test_exist_impl` -/
example : (⊢@{PROP} iprop(x ≡ z → ∃ y, x ≡ y → y ≡ z))
    ↔ (∀ n, x ≡{n}≡ z → ∃ y, ∀ m ≤ n, x ≡{m}≡ y → y ≡{m}≡ z) := by
  simp only [sbi_norm]
  simp only [sbi_model]

/-- `test_forall_impl`. Rocq leaves the closure inside the `∀ y`; we merge the
`∀ y` into the closure first, so the two binders come out in the other order. -/
example : (⊢@{PROP} iprop((∀ y, x ≡ y → y ≡ z) → x ≡ z))
    ↔ (∀ n, (∀ m ≤ n, ∀ y, x ≡{m}≡ y → y ≡{m}≡ z) → x ≡{n}≡ z) := by
  simp only [sbi_norm]
  simp only [sbi_model]

end RocqTests

end IrisTest.SbiUnfold
