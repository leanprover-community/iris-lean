import Iris.BI

namespace Iris.Tests
open Iris.BI

variable (p : Bool) (φ : Prop)
variable [BI PROP] (P Q R : PROP) (Ψ : Nat → PROP) (Φ : Nat → Nat → PROP)

-- Interface
#check P ⊢ Q

#check `[iprop| emp]

#check `[iprop| ⌜φ⌝]

#check `[iprop| P ∧ Q]
#check `[iprop| P ∧ (Q ∧ R)]

#check `[iprop| P ∨ Q]
#check `[iprop| P ∨ (Q ∨ R)]

#check `[iprop| P → Q]
#check `[iprop| P → (Q → R)]
#check `[iprop| (P ∧ Q) → R]
#check `[iprop| P → (Q ∧ R)]

#check `[iprop| ∀ x, Ψ x]
#check `[iprop| ∀ (x : Nat), Ψ x]
#check `[iprop| ∀ x y, Φ x y]
#check `[iprop| ∀ (x : Nat) (y : Nat), Φ x y]
#check `[iprop| ∀ (x y : Nat), Φ x y]

#check `[iprop| ∃ x, Ψ x]
#check `[iprop| ∃ (x : Nat), Ψ x]
#check `[iprop| ∃ x y, Φ x y]
#check `[iprop| ∃ (x : Nat) (y : Nat), Φ x y]
#check `[iprop| ∃ (x y : Nat), Φ x y]

#check `[iprop| P ∗ Q]
#check `[iprop| P ∗ (Q ∗ R)]

#check `[iprop| P -∗ Q]
#check `[iprop| P -∗ (Q -∗ R)]
#check `[iprop| (P ∗ Q) -∗ R]
#check `[iprop| P -∗ (Q ∗ R)]

#check `[iprop| <pers> P]
#check `[iprop| (<pers> P) ∧ Q]
#check `[iprop| P ∗ (<pers> Q)]

#check `[iprop| True]
#check `[iprop| False]

#check `[iprop| ¬P]
#check `[iprop| (¬P) ∧ Q]

-- Term
#check `[iprop| Ψ `[term| 1 + 1]]
#check `[iprop| Ψ (1 + 1)]

#check `[iprop| if p then □ P else P]
#check `[iprop| (□ P : PROP)]

-- Derived Connectives
#check ⊢ P
#check P ⊣⊢ Q

#check `[iprop| P ↔ Q]
#check `[iprop| (P ∧ Q) ↔ (Q ∧ P)]

#check `[iprop| P ∗-∗ Q]
#check `[iprop| (P ∗ Q) ∗-∗ (Q ∗ P)]

#check `[iprop| <affine> P]
#check `[iprop| (<affine> P) ∧ Q]
#check `[iprop| P ∗ (<affine> Q)]

#check `[iprop| <absorb> P]
#check `[iprop| (<absorb> P) ∧ Q]
#check `[iprop| P ∗ (<absorb> Q)]

#check `[iprop| □ P]
#check `[iprop| (□ P) ∧ Q]
#check `[iprop| P ∗ (□ Q)]

#check `[iprop| <pers>?p P]
#check `[iprop| (<pers>?p P) ∧ Q]
#check `[iprop| P ∗ (<pers>?p Q)]

#check `[iprop| <affine>?p P]
#check `[iprop| (<affine>?p P) ∧ Q]
#check `[iprop| P ∗ (<affine>?p Q)]

#check `[iprop| <absorb>?p P]
#check `[iprop| (<absorb>?p P) ∧ Q]
#check `[iprop| P ∗ (<absorb>?p Q)]

#check `[iprop| □?p P]
#check `[iprop| (□?p P) ∧ Q]
#check `[iprop| P ∗ (□?p Q)]

end Iris.Tests
