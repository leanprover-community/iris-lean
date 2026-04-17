/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

module

public meta import Lean
import Iris.Std.RocqAlias

/-!
# Rocq Ignore Command

A command for marking Rocq definitions as intentionally not ported.

## Usage

```
#rocq_ignore rocq_name "Reason"
```
-/

open Lean Elab Command

/-- Environment extension tracking all `#rocq_ignore` entries as `(rocqName, reason)` pairs. -/
meta initialize rocqIgnoreExt : SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (fun acc a => a.foldl Array.push acc) #[]
  }

/-- Mark a Rocq definition as intentionally not ported. -/
@[expose]
elab "#rocq_ignore" id:ident reason:str : command => do
  modifyEnv (rocqIgnoreExt.addEntry · (id.getId, reason.getString))
