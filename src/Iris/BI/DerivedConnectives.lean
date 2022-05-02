import Iris.BI.Interface

namespace Iris.BI

macro:25 "⊢ " P:term:26 : term => `(emp ⊢ $P)
macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => `(`[iprop| $P] ≡ `[iprop| $Q])

syntax:27 term:28 " ↔ " term:28 : term
syntax:27 term:28 " ∗-∗ " term:28 : term

macro_rules
  | `(`[iprop| $P ↔ $Q]) => `(`[iprop| ($P → $Q) ∧ ($Q → $P)])
  | `(`[iprop| $P ∗-∗ $Q]) => `(`[iprop| ($P -∗ $Q) ∧ ($Q -∗ $P)])

end Iris.BI
