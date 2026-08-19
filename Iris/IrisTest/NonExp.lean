/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.BI
public import Iris.Algebra

@[expose] public section

namespace IrisTest
open Iris BI OFE

/- Tests the contractive and nonexp tactics -/
section contractive

variable [OFE α] [BI PROP] [BILaterContractive PROP]

/- Identity is non-expansive. -/
example : NonExpansive (fun x : α => x) where
  ne := by nonexp

/- `nonexp` should also work when directly called on a NonExpansive goal -/
example : NonExpansive (fun x : α => x) := by nonexp

/- Constant functions are non-expansive. -/
example (y : α) : NonExpansive (fun _ : α => y) where
  ne := by nonexp

/- A non-expansive function with every occurrence of `x` guarded by ▷. -/
example (f : PROP → PROP) [NonExpansive f] : Contractive (fun x => iprop(▷ (f x) ∧ ▷ (f x))) where
  distLater_dist := by contractive

/- A non-expansive function remains contractive under additional ▷s. -/
example (f : PROP → PROP) [NonExpansive f] : Contractive (fun x => iprop(▷ ▷ (f x))) where
  distLater_dist := by contractive

/- `contractive` should also work when directly called on a `Contractive` goal -/
example (f : PROP → PROP) [NonExpansive f] : Contractive (fun x => iprop(▷ ▷ (f x))) := by contractive

/- A contractive function is also non-expansive. -/
example (f : α → α) [Contractive f] : NonExpansive f where
  ne := by nonexp

/- Fails because `x` occurs outside a ▷. -/
/-- error: tactic 'contractive' failed -/
#guard_msgs in
example : Contractive (fun x : α => x) where
  distLater_dist := by
    contractive

/- Fails because one occurrence of `x` is unguarded. -/
/-- error: tactic 'contractive' failed -/
#guard_msgs in
example (f : α → α) [Contractive f] : Contractive (fun x => (f x, x)) where
  distLater_dist := by
    contractive

end contractive
