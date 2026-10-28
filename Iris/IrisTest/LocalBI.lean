/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.LocalBI

@[expose] public section

namespace IrisTest
open Iris

section Defaults

#guard_msgs in
local bi Nat

example : bi% = Nat := rfl

/--
warning: `local bi` overrides an existing default proposition type
Disable this warning with `set_option iris.localBi.warnOnOverride false`.
-/
#guard_msgs in
local bi Bool

example : bi% = Bool := rfl

section Nested

#guard_msgs in
set_option iris.localBi.warnOnOverride false in
local bi (List Nat)

example : bi% = List Nat := rfl

end Nested

example : bi% = Bool := rfl

/--
warning: `local bi` overrides an existing default proposition type
Disable this warning with `set_option iris.localBi.warnOnOverride false`.
-/
#guard_msgs in
local bi Nat

example : bi% = Nat := rfl

end Defaults

-- With no default, `bi%` can still be inferred from context.
example : (true : bi%) = true := rfl

section Application

#guard_msgs in
local bi (List Nat)

example : bi% = List Nat := rfl

end Application

/-- error: `bi` must be `local`: it sets the proposition type of the current section -/
#guard_msgs in
scoped bi Nat

end IrisTest
