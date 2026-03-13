/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Lean

/-!
# Rocq Alias Command

A command for creating `@[deprecated]` aliases at the root namespace with the exact Rocq name,
used to document Rocq↔Lean name correspondence when porting Iris.

## Usage

```
namespace ExclAuth
theorem agreeN ... := ...
rocq_alias excl_auth_agreeN := ExclAuth.agreeN
end ExclAuth
```

This creates a root-level `excl_auth_agreeN` that is a deprecated alias for `ExclAuth.agreeN`.
-/

open Lean

/-- Creates a `@[deprecated]` `abbrev` at the root namespace with the given Rocq name,
    pointing to the given Lean declaration. -/
syntax "rocq_alias " ident " := " ident : command

macro_rules
  | `(rocq_alias $rocqName := $leanName) => do
    let rootName := mkIdentFrom rocqName (`_root_ ++ rocqName.getId)
    `(@[deprecated $leanName (since := "")]
      abbrev $rootName := @$leanName)
