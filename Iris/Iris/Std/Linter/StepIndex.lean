/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Linter.Basic
public meta import Lean.Elab.Command
public meta import Lean.Elab.InfoTree.Util

meta section

namespace Iris.Std.Linter

public register_option linter.iris.stepIndex : Bool := {
  defValue := true
  descr := "warn about two step indices in scope"
}

namespace StepIndexLinter

open Lean Elab Command Meta Linter

def sidx? (e : Expr) : Option Expr :=
  match e.cleanupAnnotations with
  | .app (.const `Iris.SIdx _) i => some i
  | _ => none

def rival (mctx : MetavarContext) (lctx : LocalContext) (d : LocalDecl) (i : Expr) :
    Option LocalDecl :=
  lctx.findDecl? fun d' => do
    let i' ← sidx? (instantiateMVarsCore mctx d'.type).1
    guard (d'.index < d.index)
    if let (.fvar x, .fvar y) := (i, i') then
      guard <| x == y || (lctx.find? x).map (·.userName) != (lctx.find? y).map (·.userName)
    return d'

def globalSIdx : CoreM (List Name) := do
  let erased ← getErasedInstances
  let some t := (← getGlobalInstancesIndex).root.find? (.const `Iris.SIdx 1) | return []
  return t.foldValues (init := []) fun ns e =>
    ns ++ (e.globalName?.filter (e.synthOrder.isEmpty && !erased.contains ·)).toList

def stepIndex : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.iris.stepIndex (← getLinterOptions) do return
  let some range := stx.getRange? | return
  let infos := (← getInfoTrees).foldl (init := #[]) fun acc t =>
    t.foldInfo (init := acc) fun ci i acc => acc.push (ci, i)
  let types := infos.filterMap fun
    | (ci, .ofTermInfo ti) => do
      guard ((sidx? ti.expr).isSome && ti.stx.getPos?.any range.contains)
      return ((instantiateMVarsCore ci.mctx ti.expr).1, ti.stx)
    | _ => none
  let mut seen : Std.HashSet String.Pos.Raw := {}
  for (ci, info) in infos do
    match info with
    | .ofCommandInfo { stx := cmd, .. } =>
      unless cmd.isOfKind ``Parser.Command.declaration || cmd.isOfKind ``Parser.Command.attribute do
        continue
      let insts ← liftCoreM <| withEnv ci.env globalSIdx
      if insts.length > 1 then
        Linter.logLint linter.iris.stepIndex cmd
          m!"Several global step indices {insts}: which one `OFE α` uses depends on \
            priorities and names."
    | .ofTermInfo { isBinder := true, expr := .fvar x, lctx, stx := bstx, .. } =>
      let some d := lctx.find? x | continue
      let ty := (instantiateMVarsCore ci.mctx d.type).1
      let some i := sidx? ty | continue
      let some d' := rival ci.mctx lctx d i | continue
      let ref := (types.find? (·.1 == ty)).elim bstx (·.2)
      let some pos := ref.getPos?.filter range.contains | continue
      if seen.contains pos then continue
      seen := seen.insert pos
      Linter.logLint linter.iris.stepIndex ref <|
        .withContext { env := ci.env, mctx := ci.mctx, lctx, opts := ci.options }
          m!"Two step indices in scope, `{d'.type}` and `{d.type}`: `OFE α` uses the last one."
    | _ => pure ()

initialize addLinter stepIndex

end Iris.Std.Linter.StepIndexLinter
