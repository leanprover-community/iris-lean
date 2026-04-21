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

/-- Valid top-level Rocq source directories. -/
private meta def validRocqFolders : List Name :=
  [`algebra, `base_logic, `bi, `program_logic, `proofmode, `si_logic]

private meta def checkRocqFolder (folder : Syntax) : CommandElabM Unit := do
  let name := folder.getId
  unless validRocqFolders.contains name do
    throwErrorAt folder
      "unknown Rocq folder '{name}', expected one of: {", ".intercalate (validRocqFolders.map toString)}"

/-- Environment extension tracking all `#rocq_ignore` entries as `(rocqName, reason)` pairs. -/
public meta initialize rocqIgnoreExt : SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (fun acc a => a.foldl Array.push acc) #[]
  }

/-- Ignore a single Rocq definition by name.

```
#rocq_ignore rocq_name "Reason"
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

/-- Ignore all definitions in a Rocq file. The folder is a top-level Rocq source
directory keyword (`algebra`, `base_logic`, `bi`, `program_logic`, `proofmode`,
`si_logic`). The file is relative to that folder.

```
#rocq_ignore_file proofmode "tokens.v" "Rocq-specific tokenizer"
```
-/
@[expose]
elab "#rocq_ignore_file" folder:ident file:str reason:str : command => do
  checkRocqFolder folder
  modifyEnv (rocqIgnoreFileExt.addEntry · (folder.getId.toString, file.getString, reason.getString))

public inductive Status where
  | Ported
  | Missing
  | DependsOn (deps: Array Name)

/-- A concept entry: `(dir, feature, subfeature?, status, reason)`. -/
public abbrev ConceptEntry := String × String × Option String × Status × String

/-- Environment extension tracking all `#rocq_concept` entries. -/
public meta initialize rocqConceptExt : SimplePersistentEnvExtension ConceptEntry (Array ConceptEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (fun acc a => a.foldl Array.push acc) #[]
  }

public syntax status := "ported" <|> "missing" <|> ("depends_on" "[" ident,+ "]")

syntax (name := rocq_concept) "#rocq_concept" ident str (str)? status str : command

variable {m : Type → Type} [Monad m] [MonadError m] in
meta def parseStatus : TSyntax `status → m Status 
| `(status| ported) =>  return .Ported
| `(status| missing) => return .Missing
| `(status| depends_on [ $[$deps:ident],* ]) => return .DependsOn (deps.map (·.raw.getId))
| stx => throwErrorAt stx s!"unsupported status: {stx.raw.getId}"

/-- Track a Rocq concept (feature or sub-feature) that doesn't map to individual
definitions. The folder is a top-level Rocq source directory keyword (`algebra`,
`base_logic`, `bi`, `program_logic`, `proofmode`, `si_logic`). Status must be
`ported` or `missing`. An optional sub-feature string creates a nested entry
under the feature in the HTML report.

```
#rocq_concept proofmode "IPM Tactics" ported "Implemented via Lean macro"
#rocq_concept proofmode "IPM Tactics" "iIntros" ported "Implemented as iIntro"
```
-/
@[expose]
elab "#rocq_concept" folder:ident feature:str sub:(str)? status:status reason:str : command => do
  checkRocqFolder folder
  let status ← parseStatus status
  let sub := sub.map (·.getString)
  modifyEnv (rocqConceptExt.addEntry · (folder.getId.toString, feature.getString, sub, status, reason.getString))
