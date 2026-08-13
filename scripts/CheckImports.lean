/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
import Lean.Data.Name
import Lean.Util.Path
import Lean.Elab.ParseImportsFast
import Std.Data.HashMap
import Std.Data.HashSet

/-
This script checks that the modules of a library (e.g. `Iris`, `IrisMath`) are
imported by the entry-point files of the directories containing them.

The project is assumed to be organised so that every directory `Foo` is accompanied by
a module `Foo.lean` acting as its entry point: `Iris/BI/` by `Iris/BI.lean`,
`Iris/BI/BigOp/` by `Iris/BI/BigOp.lean`, and so on. The check is therefore recursive:
for every directory, its entry point must transitively import every module below it.
Directories listed in `detachedDirs` are the only exception, see below.

Run the script using `lake exe check-imports <LibraryName>`. For example,
`lake exe check-imports Iris` checks `Iris.lean` against all of `Iris/`, then
`Iris/Algebra.lean` against `Iris/Algebra/`, and so on down the tree.

Returns `0` if all modules are imported, `1` if that list is non-empty, or
`2` if the check fails for another reason (e.g. module not found).
-/

open System (FilePath)
open Lean SearchPath

/-- Root of the package sources: the module `A.B` lives in `<srcDir>/A/B.lean`. -/
private def srcDir : FilePath := ⟨"."⟩

/-- Search path used to resolve a module to a source file *of this package*. Imports of
`Init`, `Std`, `Batteries` or `Qq` resolve to `none` here and are hence not followed. -/
private def srcPath : SearchPath := [⟨"."⟩]

/-- The source file of a module, e.g. `Iris.BI` to `./Iris/BI.lean`. -/
private def moduleFile (mod : Name) : FilePath :=
  modToFilePath srcDir mod "lean"

/-- The directory holding the submodules of a module, e.g. `Iris.BI` to `./Iris/BI`. -/
private def moduleDir (mod : Name) : FilePath :=
  (moduleFile mod).withExtension ""

/-- These are not modules and should be excluded from the check everywhere. -/
private def excludedModules : Array Name :=
  #[`Iris.ProofMode.Porting, `Iris.Std.DumpPortingData]

/--
Directories whose entry point is deliberately *not* imported by the entry point of
their parent directory, e.g. `Iris/Algebra.lean` does not import `Iris/Algebra/Lib.lean`.

Such a directory is exempt from the check of its immediate parent only: every further
ancestor still has to reach it (`Iris.lean` imports `Iris/Algebra/Lib.lean` directly),
and its own entry point still has to cover everything below it.
-/
private def detachedDirs : Array Name :=
  #[`Iris.Algebra.Lib, `Iris.BI.Lib, `Iris.HeapLang.Lib, `Iris.Instances.Lib]

/-- Checks whether the module is excluded from the check. -/
private def isExcluded (mod : Name) : Bool :=
  excludedModules.any (·.isPrefixOf mod)

/-- Checks whether `mod` is exempt from the check performed for the entry point `entry`. -/
private def isSkipped (entry mod : Name) : Bool :=
  isExcluded mod || detachedDirs.any fun dir => dir.getPrefix == entry && dir.isPrefixOf mod

/--
All modules whose source file lies in the directory of `root`, sorted by name.
For `root = Iris`, the file `Iris/BI/Lemmas.lean` yields the module `Iris.BI.Lemmas`.
-/
private def modulesUnder (root : Name) : IO (Array Name) := do
  let collect : StateT (Array Name) IO PUnit :=
    forEachModuleInDir (moduleDir root) fun mod => modify (·.push (root ++ mod))
  let (_, mods) ← collect.run #[]
  return mods.qsort (·.toString < ·.toString)

/-- The import graph of the given modules. -/
private def importGraph (modules : Array Name) : IO (Std.HashMap Name (Array Name)) := do
  let mut graph := ∅
  for m in modules do
    -- Find the direct imports of `module`
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

/-- Every namespace with at least one module strictly below it, i.e. every directory of
the library, including `root` itself. Sorted, so that a directory precedes its children. -/
private def directoriesUnder (root : Name) (all : Array Name) : Array Name := Id.run do
  let mut dirs := #[root]
  let mut seen : Std.HashSet Name := (∅ : Std.HashSet Name).insert root
  for mod in all do
    -- Add the chain of directories from the one containing `mod` up to `root`
    let mut dir := mod.getPrefix
    while root.isPrefixOf dir && !seen.contains dir do
      seen := seen.insert dir
      dirs := dirs.push dir
      dir := dir.getPrefix
  return dirs.qsort (·.toString < ·.toString)

def main (args : List String) : IO UInt32 := do
  match args with
  | [libName] =>
    let root := libName.toName
    -- Check the validity of the argument (top-level entry point module)
    unless (← (moduleFile root).pathExists) && (← (moduleDir root).isDir) do
      IO.eprintln s!"check-imports: expected an entry-point file {moduleFile root} \
        next to a directory {moduleDir root}."
      return 2
    -- Find all modules under the top-level directory
    let all ← modulesUnder root
    let graph ← importGraph (all.push root)
    let mut ok := true
    let mut checked := 0
    for dir in directoriesUnder root all do
      if isExcluded dir then continue
      unless (← (moduleFile dir).pathExists) do
        IO.eprintln s!"check-imports: no entry-point file {moduleFile dir} \
          for directory {moduleDir dir}."
        ok := false
        continue
      checked := checked + 1
      let reachable := reachableFrom graph dir
      -- The modules of `all` that the entry point of the directory `dir` must import
      let expectedUnder := all.filter
        fun mod => mod != dir && dir.isPrefixOf mod && !isSkipped dir mod
      let missing := expectedUnder.filter (!reachable.contains ·)
      unless missing.isEmpty do
        IO.eprintln s!"check-imports: {missing.size} file(s) under {dir} are never \
          imported (directly or transitively) from {moduleFile dir}:"
        for mod in missing do
          IO.eprintln s!"  {mod}"
        ok := false
    if ok then
      IO.println s!"check-imports: all {all.size} modules under {root} are imported \
        from the entry point of their directory ({checked} entry points checked)."
    return if ok then 0 else 1
  -- Return error for invalid arguments
  | _ =>
    IO.eprintln "usage: check-imports <LibraryName> (e.g. `lake exe check-imports Iris`)"
    return 2
