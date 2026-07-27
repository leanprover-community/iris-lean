/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Zongyuan Liu
-/
module

import Lean
public meta import Lean

/-!
# Rocq Porting Infrastructure

`@[rocq_alias]` attribute and `#rocq_ignore`, `#rocq_ignore_file`, `#rocq_concept`
commands for tracking porting progress from Iris-Rocq to Iris-Lean.

## Rocq Alias Attribute

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

## Naming Convention

The name given to `@[rocq_alias]` must be the **fully qualified Rocq name**.
If the Rocq definition lives inside a `Module`, include the module prefix.
Rocq `Section`s do not affect name qualification.

For example, in Rocq:
```
Module bi.
  Lemma absorbingly_timeless P : ...
End bi.
```
the fully qualified name is `bi.absorbingly_timeless`, so the alias should be:
```
@[rocq_alias bi.absorbingly_timeless]
```

Conversely, definitions inside a `Section` (not a `Module`) are **not** prefixed:
```
Section internal_eq.
  Lemma internal_eq_ne : ...
End internal_eq.
```
Here the name is just `internal_eq_ne`, so:
```
@[rocq_alias internal_eq_ne]
```

Definitions outside the main `iris/` package carry a package prefix.
For the heap_lang package (`iris_heap_lang/` upstream) write:
```
@[rocq_alias heap_lang.pointsto]
```
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

-- ============================================================================
-- Porting Commands
-- ============================================================================

/-- Path to the shared porting configuration, relative to the Lake workspace
root (the `Iris/` directory Lake runs builds from). -/
private meta def configPath : System.FilePath :=
  ".." / "scripts" / "porting_config.json"

/-- Read the valid Rocq source directories from `scripts/porting_config.json`.

Each tracked package contributes its own name plus one entry per immediate
subdirectory, both following the package's configured `prefix` -- so they read
exactly like the alias names: `heap_lang` and `heap_lang.lib` alongside
`@[rocq_alias heap_lang.pointsto]`. The package that goes unprefixed contributes
its folders bare (`proofmode`), which cannot collide because at most one package
may claim the unprefixed namespace.

Sharing the file with `scripts/check_porting.py` is what keeps the directory
names accepted here from drifting from the directories the report tracks.

The config is read when this module is loaded, so edits to it take effect
without a rebuild. A long-running process that already loaded the module -- an
editor's language server, say -- keeps the list it started with until restarted. -/
private meta def readValidRocqFolders : IO (List String) := do
  let src ← IO.FS.readFile configPath
  let .ok json := Json.parse src
    | throw <| IO.userError s!"{configPath}: not valid JSON"
  let .ok packages := json.getObjVal? "packages" >>= Json.getArr?
    | throw <| IO.userError s!"{configPath}: missing 'packages' array"
  let mut valid := #[]
  for p in packages do
    let pre := (p.getObjVal? "prefix" >>= Json.getStr?).toOption.getD ""
    -- The package itself: the prefix without its trailing dot.
    let name := pre.dropEndWhile (· == '.') |>.toString
    if !name.isEmpty then valid := valid.push name
    if let .ok fs := p.getObjVal? "folders" >>= Json.getArr? then
      for f in fs do
        if let .ok s := f.getStr? then valid := valid.push s!"{pre}{s}"
  return valid.toList

/-- Valid Rocq source directories, read once from the shared config. -/
private meta initialize validRocqFolders : List String ← readValidRocqFolders

private meta def checkRocqFolder (folder : Syntax) : CommandElabM Unit := do
  let name := folder.getId.toString
  unless validRocqFolders.contains name do
    throwErrorAt folder
      "unknown Rocq folder '{name}', expected one of: {", ".intercalate validRocqFolders}"

/-- Environment extension tracking all `#rocq_ignore` entries as `(rocqName, reason)` pairs. -/
public meta initialize rocqIgnoreExt : SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (fun acc a => a.foldl Array.push acc) #[]
  }

/-- Ignore a single Rocq definition by name. The name follows the same
convention as `@[rocq_alias]`, so definitions outside the main `iris/` package
carry a package prefix.

```
#rocq_ignore rocq_name "Reason"
#rocq_ignore heap_lang.pretty_int "Rocq-specific pretty printing"
```
-/
@[expose]
elab "#rocq_ignore" id:ident reason:str : command => do
  modifyEnv (rocqIgnoreExt.addEntry · (id.getId, reason.getString))

/-- Environment extension tracking all `#rocq_ignore_file` entries as `(folder, file, reason)` triples. -/
public meta initialize rocqIgnoreFileExt : SimplePersistentEnvExtension (String × String × String) (Array (String × String × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (fun acc a => a.foldl Array.push acc) #[]
  }

/-- Ignore all definitions in a Rocq file. The folder names an upstream Rocq
source directory, written with the owning package's prefix so that it reads like
the alias names: `heap_lang` for that package, `heap_lang.lib` for its
subdirectory, and bare (`algebra`, `base_logic`, `bi`, `program_logic`,
`proofmode`, `si_logic`) for the unprefixed `iris` package. The file is relative
to the named directory.

```
#rocq_ignore_file proofmode "tokens.v" "Rocq-specific tokenizer"
#rocq_ignore_file heap_lang.lib "diverge.v" "Not needed"
#rocq_ignore_file heap_lang "pretty.v" "Rocq-specific pretty printing"
```
-/
@[expose]
elab "#rocq_ignore_file" folder:ident file:str reason:str : command => do
  checkRocqFolder folder
  modifyEnv (rocqIgnoreFileExt.addEntry · (folder.getId.toString, file.getString, reason.getString))

/-- A concept entry: `(dir, feature, subfeature?, status, reason)`. -/
public abbrev ConceptEntry := String × String × Option String × Name × String

/-- Environment extension tracking all `#rocq_concept` entries. -/
public meta initialize rocqConceptExt : SimplePersistentEnvExtension ConceptEntry (Array ConceptEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (fun acc a => a.foldl Array.push acc) #[]
  }

/-- Track a Rocq concept (feature or sub-feature) that doesn't map to individual
definitions. The folder names an upstream Rocq source directory, as for
`#rocq_ignore_file`. Status must be `ported` or `missing`. An optional
sub-feature string creates a nested entry under the feature in the HTML report.

```
#rocq_concept proofmode "IPM Tactics" ported "Implemented via Lean macro"
#rocq_concept proofmode "IPM Tactics" "iIntros" ported "Implemented as iIntro"
```
-/
@[expose]
elab "#rocq_concept" folder:ident feature:str sub:(str)? status:ident reason:str : command => do
  checkRocqFolder folder
  let statusName := status.getId
  unless statusName == `ported || statusName == `missing || statusName == `ignored do
    throwErrorAt status "status must be 'ported' or 'missing' or 'ignored', got '{statusName}'"
  let sub := sub.map (·.getString)
  modifyEnv (rocqConceptExt.addEntry · (folder.getId.toString, feature.getString, sub, statusName, reason.getString))
