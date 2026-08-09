/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/

/-
This script checks that all modules under a directory (e.g. `Iris`, `IrisMath`)
are imported by the corresponding entry-point file (e.g. `Iris.lean`, `IrisMath.lean`).

Run the script using `lake exe check-imports <LibraryName>`. For example,
`lake exe check-imports Iris` checks that every `.lean` file under `Iris/` is
reachable from `Iris.lean`.

Returns `0` if all modules are imported, `1` if that list is non-empty, or
`2` if the check fails for another reason (e.g. module not found).
-/

open System (FilePath)

abbrev leanSuffix := ".lean"

/-- Convert path name to module name (e.g. `Iris/BI/BIBase.lean` to `Iris.BI.BIBase`). -/
private def pathToModule (p : FilePath) : String :=
  let s := p.toString
  let s := if s.endsWith leanSuffix then s.dropEnd leanSuffix.length else s
  (s.replace "\\" "/").replace "/" "."

/-- Convert module name to path name (e.g. `Iris.BI.BIBase` to `Iris/BI/BIBase.lean`). -/
private def moduleToPath (m : String) : FilePath :=
  FilePath.mk (m.replace "." "/" ++ leanSuffix)

/-- Recursively collect all `.lean` files under `dir`. -/
private partial def collectLeanFiles (dir : FilePath) : IO (List FilePath) := do
  let mut acc := []
  for entry in (← dir.readDir) do
    let p := entry.path
    if (← p.isDir) then
      acc := acc ++ (← collectLeanFiles p)
    else if p.extension == some "lean" then
      acc := p :: acc
  return acc

/-- Given a line of code that imports a module, return the imported module name. -/
private def importOfLine (line : String) : Option String :=
  -- Strip trailing comments on the line
  let line := ((line.splitOn "--").headD line).trimAscii
  -- Normalise tabs to spaces
  let toks := ((line.replace "\t" " ").splitOn " ").filter (· ≠ "")
  -- Strip leading modifiers
  let rec dropMods : List String → List String
    | "public" :: rest => dropMods rest
    | "meta" :: rest => dropMods rest
    | "private" :: rest => dropMods rest
    | rest => rest
  -- Remove the leading `import` keyword
  match dropMods toks with
  | "import" :: modName :: _ => some modName
  | _ => none

private def parseImports (contents : String) : List String :=
  (contents.splitOn "\n").filterMap importOfLine

/--
Transitive closure of the import graph, following files that exist on
disk starting from the given worklist.
-/
private partial def reachableModules (visited : List String) (paths : List FilePath) :
    IO (List String) := do
  match paths with
  | [] => return visited
  | path :: paths => do
    if ← path.pathExists then
      let newMods := (parseImports <| ← IO.FS.readFile path).filter (!visited.contains ·)
      let visited := newMods.foldl (fun acc m => m :: acc) visited
      reachableModules visited (newMods.map moduleToPath ++ paths)
    else
      reachableModules visited paths

def main (args : List String) : IO UInt32 := do
  match args.find? (fun a => !a.startsWith "-") with
  | none =>
    IO.eprintln
      "usage: check-imports <LibraryName> (e.g. `lake exe check-imports Iris`)"
    return 2
  | some libName =>
    let rootFile := FilePath.mk <| libName ++ leanSuffix
    let rootDir := FilePath.mk libName
    -- Traverse the directory to collect all the modules
    let expected := (← collectLeanFiles rootDir).map pathToModule
    -- Check if any modules under the directory are not imported by the entry-point module
    let unimported := expected.filter (!(← reachableModules [] [rootFile]).contains ·)
    if unimported.isEmpty then
      IO.println s!"check-imports: all {expected.length} modules under \
        {rootDir} are imported from {rootFile}."
      return 0
    else
      IO.eprintln s!"check-imports: {unimported.length} file(s) under \
        {rootDir} are never imported (directly or transitively) from {rootFile}:"
      for m in unimported do
        IO.eprintln s!"  {m}"
      return 1
