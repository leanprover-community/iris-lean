/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

module

meta import Lean
public meta import Iris.Std.RocqPorting

/-!
# Dump Porting Data

A lean_exe that loads the Iris environment, collects all porting data
(`@[rocq_alias]`, `#rocq_ignore`, `#rocq_ignore_file`, `#rocq_concept`)
and writes them to a JSON file.

Usage: `lake exe dumpPortingData [output-path]`
Default output: `.lake/porting_data.json`
-/

open Lean

/-- Extract the target constant name from a declaration's value expression.
    For aliases created by `@[rocq_alias]`, the value is `mkConst leanName levels`. -/
meta def extractTargetName (info : ConstantInfo) : Option Name :=
  match info with
  | .thmInfo val => val.value.constName?
  | .defnInfo val => val.value.constName?
  | _ => none

/-- Collect all `Rocq.*` aliases from the environment and return `(rocqName, leanName)` pairs.
    Each `@[rocq_alias foo]` creates a declaration `Rocq.foo` whose value points to the Lean name. -/
meta def collectRocqAliases (env : Environment) : Array (Name × Name) :=
  env.constants.fold (init := #[]) fun acc name info =>
    if name.getRoot == `Rocq then
      match extractTargetName info with
      | some target =>
        let rocqName := name.replacePrefix `Rocq .anonymous
        acc.push (rocqName, target)
      | none => acc
    else acc

/-- Convert a Name to a dot-separated string without guillemets. -/
private meta def nameToRocqStr (n : Name) : String :=
  n.toString (escape := false)

/-- Build a JSON object from collected data. -/
meta def buildJson (aliases : Array (Name × Name))
    (ignores : Array (Name × String))
    (ignoredFiles : Array (String × String × String))
    (concepts : Array ConceptEntry) : Json :=
  let aliasArr := aliases.map fun (rocq, lean) =>
    Json.mkObj [("rocq", nameToRocqStr rocq), ("lean", lean.toString)]
  let ignoreArr := ignores.map fun (rocq, reason) =>
    Json.mkObj [("rocq", nameToRocqStr rocq), ("reason", reason)]
  let ignoreFileArr := ignoredFiles.map fun (folder, file, reason) =>
    Json.mkObj [("folder", folder), ("file", file), ("reason", reason)]
  let conceptArr := concepts.map fun (folder, feature, sub, status, reason) =>
    Json.mkObj [("folder", folder), ("feature", feature),
      ("subfeature", match sub with | some s => Json.str s | none => Json.null),
      ("status", status.toString), ("reason", reason)]
  Json.mkObj [("aliases", Json.arr aliasArr), ("ignores", Json.arr ignoreArr),
    ("ignored_files", Json.arr ignoreFileArr), ("concepts", Json.arr conceptArr)]

/-- Discover all `.lean` source files under a directory and convert to module names.
    E.g., `src/Iris/BI/Sbi.lean` → `Iris.BI.Sbi` -/
meta partial def discoverModules (srcDir : System.FilePath) : IO (Array Name) := do
  let mut result : Array Name := #[]
  let mut worklist : Array (System.FilePath × Name) := #[(srcDir / "Iris", `Iris)]
  while h : worklist.size > 0 do
    let (dir, modPrefix) := worklist[0]
    worklist := worklist.eraseIdx 0
    for entry in (← dir.readDir) do
      if (← entry.path.isDir) then
        worklist := worklist.push (entry.path, modPrefix ++ entry.fileName.toName)
      else if entry.fileName.endsWith ".lean" then
        let stem := (entry.fileName.dropEnd 5).toString
        result := result.push (modPrefix ++ stem.toName)
  return result

public meta unsafe def main (args : List String) : IO Unit := do
  let outputPath := args.head? |>.getD ".lake/porting_data.json"
  -- Initialize Lean
  Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  -- Discover all Iris .olean modules to bypass `module` re-export filtering.
  -- `module` files don't re-export declarations created by privately-imported
  -- metaprograms like @[rocq_alias], so we import every module directly.
  let srcDir : System.FilePath := "src"
  let modules ← discoverModules srcDir
  let env ← importModules (modules.map ({ module := · }))
    {} (trustLevel := 1024) (loadExts := true)
  -- Collect aliases from Rocq namespace
  let aliases := collectRocqAliases env
  -- Collect ignores from the environment extension
  let ignores := rocqIgnoreExt.getState env
  -- Collect ignored files from the environment extension
  let ignoredFiles := rocqIgnoreFileExt.getState env
  -- Collect concepts from the environment extension
  let concepts := rocqConceptExt.getState env
  -- Build and write JSON
  let json := buildJson aliases ignores ignoredFiles concepts
  IO.FS.writeFile outputPath (json.pretty ++ "\n")
  IO.println s!"Wrote {aliases.size} aliases, {ignores.size} ignores, {ignoredFiles.size} ignored files, and {concepts.size} concepts to {outputPath}"
