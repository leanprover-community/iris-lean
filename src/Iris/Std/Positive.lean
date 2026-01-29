/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/

/-! # Positive Names

Reference: `stdpp/theories/positive.v`

Invariant names need a countable supply of identifiers that support suffix-based
namespace reasoning. Rather than using binary-encoded positive integers, we model
names as lists of encoded components, which makes the suffix structure (needed by
`Namespace` and `nclose`) directly available as list operations.

## Main Definitions

- `NameComponent` — encoded namespace components (lists of natural numbers)
- `Positive` — invariant names, represented as lists of components
-/

namespace Iris

/-- Encoded namespace components. -/
abbrev NameComponent := List Nat

/-- Positive names, represented as lists of name components. -/
abbrev Positive := List NameComponent

end Iris
