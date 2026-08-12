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
This script checks that every module of a library (e.g. `Iris`, `IrisMath`) directly or
transitively imports the initialisation module of that library, e.g. `Iris.Init`.

`Init.lean` collects the imports that set up the environment of the library (options,
attributes, notation, linters, ...), so it has to be reached from every module of the
library. The only modules exempt from this are the ones `Init.lean` itself depends on:
these are reachable *from* `Init` and could not import it without creating a cycle.

Run the script using `lake exe check-init <LibraryName>`. For example,
`lake exe check-init Iris` checks every module under `Iris/` (and `Iris.lean` itself)
against `Iris/Init.lean`.

Returns `0` if all modules import the initialisation module, `1` if that list is
non-empty, or `2` if the check fails for another reason (e.g. module not found).
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

/--
The reversed import graph: `m` is an edge target of each of its imports. Reachability in
this graph from a module `i` is exactly the set of modules that (transitively) import `i`.
-/
private def reverseGraph (graph : Std.HashMap Name (Array Name)) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut rev := ∅
  for (mod, imports) in graph do
    for i in imports do
      rev := rev.insert i ((rev.getD i #[]).push mod)
  return rev

def main (args : List String) : IO UInt32 := do
  match args with
  | [libName] =>
    let root := libName.toName
    let init := root ++ `Init
    -- Check the validity of the argument (top-level entry point module)
    unless (← (moduleFile root).pathExists) && (← (moduleDir root).isDir) do
      IO.eprintln s!"check-init: expected an entry-point file {moduleFile root} \
        next to a directory {moduleDir root}."
      return 2
    -- Check that the initialisation module exists
    unless (← (moduleFile init).pathExists) do
      IO.eprintln s!"check-init: no initialisation file {moduleFile init} for {root}."
      return 2
    -- Find all modules under the top-level directory, plus the top-level entry point
    let all := (← modulesUnder root).push root
    let graph ← importGraph all
    -- The modules that reach `init` by importing it, directly or transitively
    let importers := reachableFrom (reverseGraph graph) init
    -- The modules that `init` itself depends on; these cannot import it back
    let dependencies := reachableFrom graph init
    -- The modules of the library that are subject to the check, and the ones that fail it
    let expected := all.filter (!dependencies.contains ·)

    let minimal := expected.filter fun mod =>
      (graph.getD mod #[]).all fun i => dependencies.contains i || !graph.contains i
    IO.eprintln s!"check-init: minimal set of modules to import {moduleFile init}:"
    for m in minimal do
      IO.eprintln s!"  {m}"

    let exempt := all.filter fun mod => mod != init && dependencies.contains mod
    let missing := expected.filter (!importers.contains ·)
    unless missing.isEmpty do
      IO.eprintln s!"check-init: {missing.size} module(s) of {root} never import \
        (directly or transitively) {moduleFile init}:"
      for mod in missing do
        IO.eprintln s!"  {mod}"
      return 1
    IO.println s!"check-init: all {expected.size} modules of {root} import {init} \
      ({exempt.size} module(s) exempt as imports of {init})."
    return 0
  -- Return error for invalid arguments
  | _ =>
    IO.eprintln "usage: check-init <LibraryName> (e.g. `lake exe check-init Iris`)"
    return 2
