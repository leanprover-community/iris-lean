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

/-- These are not modules and should be excluded from the check. -/
private def excludedModules : List String :=
  ["Iris.ProofMode.Porting", "Iris.Std.DumpPortingData"]

/-- Checks whether `moduleName` has a prefix `modulePrefix`. -/
private def isUnderModule (modulePrefix moduleName : String) : Bool :=
  moduleName == modulePrefix || moduleName.startsWith (modulePrefix ++ ".")

/-- Checks whether the module is excluded from the check. -/
private def isExcluded (moduleName : String) : Bool :=
  excludedModules.any (isUnderModule · moduleName)

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

/--
Check that `rootFile` transitively imports every module under `rootDir`,
ignoring modules for which the predicate `skip` holds.
Reports any that are missing, and returns `true` iff the check passes.
-/
private def checkDir (rootFile rootDir : FilePath) (skip : String → Bool) : IO Bool := do
  let expected := ((← collectLeanFiles rootDir).map pathToModule).filter (!skip ·)
  let reachable ← reachableModules [] [rootFile]
  let unimported := expected.filter (!reachable.contains ·)
  if unimported.isEmpty then
    IO.println s!"check-imports: all {expected.length} modules under \
      {rootDir} are imported from {rootFile}."
    return true
  else
    IO.eprintln s!"check-imports: {unimported.length} file(s) under \
      {rootDir} are never imported (directly or transitively) from {rootFile}:"
    for m in unimported do
      IO.eprintln s!"  {m}"
    return false

/-- The immediate subdirectories of `dir`, sorted for deterministic output. -/
private def immediateSubdirs (dir : FilePath) : IO (List FilePath) := do
  let mut acc := []
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then acc := entry.path :: acc
  return (acc.toArray.qsort (·.toString < ·.toString)).toList

def main (args : List String) : IO UInt32 := do
  match args.find? (fun a => !a.startsWith "-") with
  | none =>
    IO.eprintln
      "usage: check-imports <LibraryName> (e.g. `lake exe check-imports Iris`)"
    return 2
  | some libName =>
    let rootFile := FilePath.mk <| libName ++ leanSuffix
    let rootDir := FilePath.mk libName
    -- Check imports by the top-level entry-point module
    let mut ok := (← checkDir rootFile rootDir isExcluded)
    -- Check imports in immediate sub-modules (useful when they are also entry-point modules)
    if args.contains "--subdirs" then
      for subDir in (← immediateSubdirs rootDir) do
        let subFile := FilePath.mk <| subDir.toString ++ leanSuffix
        if ← subFile.pathExists then
          let libPrefix := pathToModule subDir ++ ".Lib"
          ok := ok &&
            (← checkDir subFile subDir (fun m => isExcluded m || isUnderModule libPrefix m))
        else
          IO.eprintln s!"check-imports: no entry-point file {subFile} for directory {subDir}."
          ok := false

    return if ok then 0 else 1
