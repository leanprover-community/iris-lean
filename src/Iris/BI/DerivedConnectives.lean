import Iris.BI.Interface

namespace Iris.BI.DerivedConnectives

macro:25 "⊢ " P:iprop:26 : term => `(emp ⊢ $P)

syntax:27 iprop:28  " ↔ "  iprop:28 : iprop
syntax:27 iprop:28 " ∗-∗ " iprop:28 : iprop

macro_rules
  | `(`[iprop| $P ↔ $Q]) => `(`[iprop| ($P → $Q) ∧ ($Q → $P)])
  | `(`[iprop| $P ∗-∗ $Q]) => `(`[iprop| ($P -∗ $Q) ∧ ($Q -∗ $P)])

end Iris.BI.DerivedConnectives
