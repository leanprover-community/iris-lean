/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
import Lean.Data.Name
import Lean.Util.Path
import Lean.Elab.ParseImportsFast
import Std.Data.HashMap
import Std.Data.HashSet

/-!
This script has two functions.

### Recursive check for missing imports

The first functionality is to check that the modules of a library (e.g. `Iris`, `IrisMath`)
are imported by the entry-point files of the directories containing them.

The project is assumed to be organised so that every directory `Foo` is accompanied by
a module `Foo.lean` acting as its entry point: `Iris/BI/` by `Iris/BI.lean`,
`Iris/BI/BigOp/` by `Iris/BI/BigOp.lean`, and so on. The check is therefore recursive:
for every directory, its entry point must transitively import every module below it.
Directories listed in `detachedDirs` are the only exception, see below.

### Check that all modules imports `Init.lean`

The second functionality is to check that every module of a library
(e.g. `Iris`, `IrisMath`) directly or transitively imports the initialisation
module of that library, e.g. `Iris.Init`.

`Init.lean` collects the imports that set up the environment of the library (options,
attributes, notation, linters, ...), so it has to be reached from every module of the
library. The only modules exempt from this are the ones `Init.lean` itself depends on:
these are reachable *from* `Init` and could not import it without creating a cycle.

### Usage

Run the script using `lake exe check-imports <LibraryName>`. For example,
`lake exe check-imports Iris` checks `Iris.lean` against all of `Iris/`, then
`Iris/Algebra.lean` against `Iris/Algebra/`, and so on down the tree. It then
checks that all modules under `Iris/` imports `Iris/Init.lean`.
- Use the flag `--entry-points-only` for the first check only.
- Use the flag `--init-only` for the second check only.

Returns `0` if all checks pass, `1` if any of the checks fails, or
`2` if the check fails for another reason (e.g. module not found).
-/

open System (FilePath)
open Lean SearchPath

/--
Search path used to resolve a module to a source file of this package.
Imports of `Init`, `Std`, `Batteries` or `Qq` resolve to `none` here and are
hence not followed.
-/
private def srcPath : SearchPath := [⟨"."⟩]

/-- The source file of a module, e.g. `Iris.BI` to `./Iris/BI.lean`. -/
private def moduleFile (mod : Name) : FilePath :=
  modToFilePath ⟨"."⟩ mod "lean"

/-- The directory holding the submodules of a module, e.g. `Iris.BI` to `./Iris/BI`. -/
private def moduleDir (mod : Name) : FilePath :=
  (moduleFile mod).withExtension ""

/-- Directories whose entry point is deliberately *not* imported by the entry point of
their parent directory, e.g. `Iris/Algebra.lean` does not import `Iris/Algebra/Lib.lean`. -/
private def detachedDirs : Array Name :=
  #[`Iris.Algebra.Lib, `Iris.BI.Lib, `Iris.HeapLang.Lib, `Iris.Instances.Lib]

/-- All modules of the library, i.e. `root` and everything in its directory, sorted. -/
private def libraryModules (root : Name) : IO (Array Name) := do
  let collect : StateT (Array Name) IO PUnit :=
    forEachModuleInDir (moduleDir root) fun mod => modify (·.push (root ++ mod))
  let ⟨_, mods⟩ ← collect.run #[]
  return (mods.push root).qsort (·.toString < ·.toString)

/-- The import graph of the given modules. -/
private def importGraph (modules : Array Name) : IO (Std.HashMap Name (Array Name)) := do
  let mut graph := ∅
  for m in modules do
    let some file ← findModuleWithExt srcPath "lean" m | continue
    let header ← parseImports' (← IO.FS.readFile file) file.toString
    graph := graph.insert m (header.imports.map (·.module))
  return graph

/-- Transitive closure of the import graph starting from `entry`. -/
private def reachableFrom (graph : Std.HashMap Name (Array Name)) (entry : Name) :
    Std.HashSet Name := Id.run do
  let mut visited : Std.HashSet Name := ∅
  let mut frontier := #[entry]
  while !frontier.isEmpty do
    let current := frontier
    frontier := #[]
    for mod in current do
      unless visited.contains mod do
        visited := visited.insert mod
        frontier := frontier ++ graph.getD mod #[]
  return visited

/-- Reports the modules of `missing` under the given heading. -/
private def report (heading : String) (missing : Array Name) : IO PUnit := do
  IO.eprintln heading
  for mod in missing do
    IO.eprintln s!"  {mod}"

/-- Every entry point must transitively import the modules of its own directory. -/
private def checkEntryPoints (root : Name) (all : Array Name)
    (graph : Std.HashMap Name (Array Name)) : IO Bool := do
  -- Every namespace with at least one module strictly below it, i.e. every directory
  let mut dirs := #[root]
  let mut seen : Std.HashSet Name := (∅ : Std.HashSet Name).insert root
  for mod in all do
    let mut dir := mod.getPrefix
    while root.isPrefixOf dir && !seen.contains dir do
      seen := seen.insert dir
      dirs := dirs.push dir
      dir := dir.getPrefix
  let mut ok := true
  let mut checked := 0
  for dir in dirs.qsort (·.toString < ·.toString) do
    unless (← (moduleFile dir).pathExists) do
      IO.eprintln s!"check-imports: no entry-point file {moduleFile dir} \
        for directory {moduleDir dir}."
      ok := false
      continue
    checked := checked + 1
    let reachable := reachableFrom graph dir
    -- The modules that the entry point of the directory `dir` must import
    let expected := all.filter fun mod => mod != dir && dir.isPrefixOf mod &&
      !(detachedDirs.any fun d => d.getPrefix == dir && d.isPrefixOf mod)
    let missing := expected.filter (!reachable.contains ·)
    unless missing.isEmpty do
      report s!"check-imports: {missing.size} file(s) under {dir} are never imported \
        (directly or transitively) from {moduleFile dir}:" missing
      ok := false
  if ok then
    IO.println s!"check-imports: all {all.size} modules of {root} are imported from the \
      entry point of their directory ({checked} entry points checked)."
  return ok

/--
  Every module must transitively import `Init`, unless `Init` depends on it.
  When `minimalOnly` is `true`, only print the minimal set of modules that should import `Init`.
-/
private def checkInit (root : Name) (all : Array Name)
    (graph : Std.HashMap Name (Array Name)) (minimalOnly : Bool) : IO Bool := do
  let init := root ++ `Init
  -- The reversed import graph: reachability from `init` in it is the set of importers
  let mut rev := ∅
  for ⟨module, imports⟩ in graph do
    for i in imports do
      rev := rev.insert i ((rev.getD i #[]).push module)
  let importers := reachableFrom rev init
  -- The modules that `init` itself depends on; these cannot import it back
  let dependencies := reachableFrom graph init
  let expected := all.filter (!dependencies.contains ·)
  if minimalOnly then
    -- The modules with no non-exempt import: importing `init` from these suffices
    let minimal := expected.filter fun mod =>
      (graph.getD mod #[]).all fun i => dependencies.contains i || !graph.contains i
    report s!"check-imports: it suffices to import `{init}` in {minimal.size} module(s):" minimal
    return true
  let missing := expected.filter (!importers.contains ·)
  unless missing.isEmpty do
    report s!"check-imports: {missing.size} module(s) of {root} never import (directly \
      or transitively) {moduleFile init}:" missing
    -- Importing `init` from the modules with no non-exempt import suffices to fix this
    report s!"check-imports: it suffices to add `import {init}` to:" <|
      expected.filter fun mod =>
        (graph.getD mod #[]).all fun i => dependencies.contains i || !graph.contains i
    return false
  IO.println s!"check-imports: all {expected.size} modules of {root} import {init} \
    ({all.size - expected.size - 1} module(s) exempt as imports of {init})."
  return true

def main (args : List String) : IO UInt32 := do
  let ⟨entryPoints, initModule, minimalOnly, libName?⟩ := match args with
    | ["--entry-points-only", lib] => (true, false, false, some lib)
    | ["--init-only", lib] => (false, true, false, some lib)
    | ["--minimal-init", lib] => (false, true, true, some lib)
    | [lib] => (true, true, false, some lib)
    | _ => (false, false, false, none)
  let some libName := libName?
    | do IO.eprintln "usage: check-imports [--entry-points-only | --init-only | \
        --minimal-init] <LibraryName> (e.g. `lake exe check-imports Iris`)"
      return 2
  let root := libName.toName
  unless (← (moduleFile root).pathExists) && (← (moduleDir root).isDir) do
    IO.eprintln s!"check-imports: expected an entry-point file {moduleFile root} \
      next to a directory {moduleDir root}."
    return 2
  if initModule && !(← (moduleFile (root ++ `Init)).pathExists) then
    IO.eprintln s!"check-imports: no initialisation file \
      {moduleFile (root ++ `Init)} for {root}."
    return 2
  let all ← libraryModules root
  let graph ← importGraph all
  let mut ok := true
  if entryPoints then
    ok := (← checkEntryPoints root all graph) && ok
  if initModule then
    ok := (← checkInit root all graph minimalOnly) && ok
  return if ok then 0 else 1
