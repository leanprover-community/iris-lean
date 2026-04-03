/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

import Lean

/-!
# Rocq Alias Attribute

An attribute for creating aliases in the `Rocq` namespace with the exact Rocq name,
used to document Rocq↔Lean name correspondence when porting Iris.

## Usage

```
namespace ExclAuth
@[rocq_alias excl_auth_agreeN]
theorem agreeN ... := ...
end ExclAuth
```

This creates `Rocq.excl_auth_agreeN` as a `@[deprecated]` alias for `ExclAuth.agreeN`.
-/

open Lean Elab Command

/-- Creates a `@[deprecated]` alias in the `Rocq` namespace with the given Rocq name. -/
syntax (name := rocq_alias) "rocq_alias" ident : attr

initialize registerBuiltinAttribute {
  name := `rocq_alias
  descr := "Creates a @[deprecated] alias in the Rocq namespace for Rocq↔Lean name correspondence"
  applicationTime := .afterTypeChecking
  add := fun declName stx _kind => do
    let `(attr| rocq_alias $rocqId) := stx
      | throwError "invalid @[rocq_alias] syntax"
    let aliasName := `Rocq ++ rocqId.getId
    let env ← getEnv
    if env.find? aliasName |>.isSome then
      throwError s!"duplicate rocq_alias: `{aliasName}` already exists"
    let some info := env.find? declName
      | throwError s!"unknown declaration '{declName}'"
    let levels := info.levelParams.map mkLevelParam
    let value := mkConst declName levels
    match info with
    | .thmInfo val =>
      addDecl (.thmDecl {
        name := aliasName
        levelParams := val.levelParams
        type := val.type
        value := value
      })
    | _ =>
      addDecl (.defnDecl {
        name := aliasName
        levelParams := info.levelParams
        type := info.type
        value := value
        hints := .abbrev
        safety := .safe
      })
    Elab.addDeclarationRangesFromSyntax aliasName stx rocqId
    let declIdent := mkIdent declName
    let depStx ← `(attr| deprecated $declIdent (since := "ported into iris-lean"))
    Attribute.add aliasName `deprecated depStx .global
}
