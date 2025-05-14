/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.BIBase

namespace Iris.Tests
open Iris.BI

/-! This file contains tests for the predefined separation logic notations. -/

variable (p : Bool) (φ : Prop)
variable [BIBase PROP] (P Q R : PROP) (Ψ : Nat → PROP) (Φ : Nat → Nat → PROP)

/-! ## Interface -/

/-- info: P ⊢ Q : Prop -/
#guard_msgs in #check P ⊢ Q

/-- info: iprop(emp) : ?m.103 -/
#guard_msgs in #check iprop(emp)

/-- info: iprop(⌜φ⌝) : ?m.144 -/
#guard_msgs in #check iprop(⌜φ⌝)

/-- info: iprop(P ∧ Q) : PROP -/
#guard_msgs in #check iprop(P ∧ Q)
/-- info: iprop(P ∧ Q ∧ R) : PROP -/
#guard_msgs in #check iprop(P ∧ (Q ∧ R))

/-- info: iprop(P ∨ Q) : PROP -/
#guard_msgs in #check iprop(P ∨ Q)
/-- info: iprop(P ∨ Q ∨ R) : PROP -/
#guard_msgs in #check iprop(P ∨ (Q ∨ R))

/-- info: iprop(P → Q) : PROP -/
#guard_msgs in #check iprop(P → Q)
/-- info: iprop(P → Q → R) : PROP -/
#guard_msgs in #check iprop(P → (Q → R))
/-- info: iprop(P ∧ Q → R) : PROP -/
#guard_msgs in #check iprop((P ∧ Q) → R)
/-- info: iprop(P → Q ∧ R) : PROP -/
#guard_msgs in #check iprop(P → (Q ∧ R))

/-- info: iprop(∀ x, Ψ x) : PROP -/
#guard_msgs in #check iprop(∀ x, Ψ x)
/-- info: iprop(∀ x, Ψ x) : PROP -/
#guard_msgs in #check iprop(∀ (x : Nat), Ψ x)
/-- info: iprop(∀ x y, Φ x y) : PROP -/
#guard_msgs in #check iprop(∀ x y, Φ x y)
/-- info: iprop(∀ x y, Φ x y) : PROP -/
#guard_msgs in #check iprop(∀ (x : Nat) (y : Nat), Φ x y)
/-- info: iprop(∀ x y, Φ x y) : PROP -/
#guard_msgs in #check iprop(∀ (x y : Nat), Φ x y)

/-- info: iprop(∃ x, Ψ x) : PROP -/
#guard_msgs in #check iprop(∃ x, Ψ x)
/-- info: iprop(∃ x, Ψ x) : PROP -/
#guard_msgs in #check iprop(∃ (x : Nat), Ψ x)
/-- info: iprop(∃ x y, Φ x y) : PROP -/
#guard_msgs in #check iprop(∃ x y, Φ x y)
/-- info: iprop(∃ x y, Φ x y) : PROP -/
#guard_msgs in #check iprop(∃ (x : Nat) (y : Nat), Φ x y)
/-- info: iprop(∃ x y, Φ x y) : PROP -/
#guard_msgs in #check iprop(∃ (x y : Nat), Φ x y)

/-- info: iprop(P ∗ Q) : PROP -/
#guard_msgs in #check iprop(P ∗ Q)
/-- info: iprop(P ∗ Q ∗ R) : PROP -/
#guard_msgs in #check iprop(P ∗ (Q ∗ R))

/-- info: iprop(P -∗ Q) : PROP -/
#guard_msgs in #check iprop(P -∗ Q)
/-- info: iprop(P -∗ Q -∗ R) : PROP -/
#guard_msgs in #check iprop(P -∗ (Q -∗ R))
/-- info: iprop(P ∗ Q -∗ R) : PROP -/
#guard_msgs in #check iprop((P ∗ Q) -∗ R)
/-- info: iprop(P -∗ Q ∗ R) : PROP -/
#guard_msgs in #check iprop(P -∗ (Q ∗ R))

/-- info: iprop(<pers> P) : PROP -/
#guard_msgs in #check iprop(<pers> P)
/-- info: iprop(<pers> P ∧ Q) : PROP -/
#guard_msgs in #check iprop((<pers> P) ∧ Q)
/-- info: iprop(P ∗ <pers> Q) : PROP -/
#guard_msgs in #check iprop(P ∗ (<pers> Q))

/-- info: iprop(True) : ?m.1425 -/
#guard_msgs in #check iprop(True)
/-- info: iprop(False) : ?m.1466 -/
#guard_msgs in #check iprop(False)

/-- info: iprop(¬P) : PROP -/
#guard_msgs in #check iprop(¬P)
/-- info: iprop(¬P ∧ Q) : PROP -/
#guard_msgs in #check iprop((¬P) ∧ Q)

/-! ## Term -/

/-- info: if true = true then Ψ 1 else iprop(False) : PROP -/
#guard_msgs in #check iprop(if true then term(Ψ 1) else False)
/-- info: Ψ (1 + 1) : PROP -/
#guard_msgs in #check iprop(Ψ (1 + 1))

/-- info: if p = true then iprop(□ P) else P : PROP -/
#guard_msgs in #check iprop(if p then □ P else P)
/-- info: iprop(□ P) : PROP -/
#guard_msgs in #check iprop((□ P : PROP))

/-! ## Derived Connectives -/

/-- info: ⊢ P : Prop -/
#guard_msgs in #check ⊢ P
/-- info: P ⊣⊢ Q : Prop -/
#guard_msgs in #check P ⊣⊢ Q

/-- info: iprop(P ↔ Q) : PROP -/
#guard_msgs in #check iprop(P ↔ Q)
/-- info: iprop(P ∧ Q ↔ Q ∧ P) : PROP -/
#guard_msgs in #check iprop((P ∧ Q) ↔ (Q ∧ P))

/-- info: iprop(P ∗-∗ Q) : PROP -/
#guard_msgs in #check iprop(P ∗-∗ Q)
/-- info: iprop(P ∗ Q ∗-∗ Q ∗ P) : PROP -/
#guard_msgs in #check iprop((P ∗ Q) ∗-∗ (Q ∗ P))

/-- info: iprop(<affine> P) : PROP -/
#guard_msgs in #check iprop(<affine> P)
/-- info: iprop(<affine> P ∧ Q) : PROP -/
#guard_msgs in #check iprop((<affine> P) ∧ Q)
/-- info: iprop(P ∗ <affine> Q) : PROP -/
#guard_msgs in #check iprop(P ∗ (<affine> Q))

/-- info: iprop(<absorb> P) : PROP -/
#guard_msgs in #check iprop(<absorb> P)
/-- info: iprop(<absorb> P ∧ Q) : PROP -/
#guard_msgs in #check iprop((<absorb> P) ∧ Q)
/-- info: iprop(P ∗ <absorb> Q) : PROP -/
#guard_msgs in #check iprop(P ∗ (<absorb> Q))

/-- info: iprop(□ P) : PROP -/
#guard_msgs in #check iprop(□ P)
/-- info: iprop(□ P ∧ Q) : PROP -/
#guard_msgs in #check iprop((□ P) ∧ Q)
/-- info: iprop(P ∗ □ Q) : PROP -/
#guard_msgs in #check iprop(P ∗ (□ Q))

/-- info: iprop(<pers>?p P) : PROP -/
#guard_msgs in #check iprop(<pers>?p P)
/-- info: iprop(<pers>?p P ∧ Q) : PROP -/
#guard_msgs in #check iprop((<pers>?p P) ∧ Q)
/-- info: iprop(P ∗ <pers>?p Q) : PROP -/
#guard_msgs in #check iprop(P ∗ (<pers>?p Q))

/-- info: iprop(<affine>?p P) : PROP -/
#guard_msgs in #check iprop(<affine>?p P)
/-- info: iprop(<affine>?p P ∧ Q) : PROP -/
#guard_msgs in #check iprop((<affine>?p P) ∧ Q)
/-- info: iprop(P ∗ <affine>?p Q) : PROP -/
#guard_msgs in #check iprop(P ∗ (<affine>?p Q))

/-- info: iprop(<absorb>?p P) : PROP -/
#guard_msgs in #check iprop(<absorb>?p P)
/-- info: iprop(<absorb>?p P ∧ Q) : PROP -/
#guard_msgs in #check iprop((<absorb>?p P) ∧ Q)
/-- info: iprop(P ∗ <absorb>?p Q) : PROP -/
#guard_msgs in #check iprop(P ∗ (<absorb>?p Q))

/-- info: iprop(□?p P) : PROP -/
#guard_msgs in #check iprop(□?p P)
/-- info: iprop(□?p P ∧ Q) : PROP -/
#guard_msgs in #check iprop((□?p P) ∧ Q)
/-- info: iprop(P ∗ □?p Q) : PROP -/
#guard_msgs in #check iprop(P ∗ (□?p Q))

end Iris.Tests
