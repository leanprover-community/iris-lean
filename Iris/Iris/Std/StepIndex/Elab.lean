/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public meta import Lean.Elab.App
public import Iris.Std.StepIndex.Registry

/-!
# `local stepindex` and its elaborator

The `stepindex` command, and the scoped elaborator and delaborator that fill in and hide the step
index of `@[indexed]` declarations (see `Iris.Algebra.StepIndex`). The elaborator runs on every
application and identifier of a sugared section. 
-/

namespace Iris.StepIndex

open Lean Elab Term

/-- The constants that `f` names, with their `@[indexed]` data. -/
meta def indexedHeads (f : Ident) : TermElabM (List (Name × Option IndexedInfo)) := do
  let table := indexedExt.getState (← getEnv)
  -- fast path
  let .str _ last := f.getId.eraseMacroScopes | return []
  unless table.lasts.contains (.mkSimple last) do return []
  if (← isLocalIdent? f).isSome then return []
  -- from a notation or macro: pre-resolved
  if let .ident _ _ _ pre := f.raw then
    let ns := pre.filterMap fun | .decl n [] => some n | _ => none
    unless ns.isEmpty do return ns.map fun n => (n, table.decls.find? n)
  return (← resolveGlobalName f.getId).filterMap fun (n, fields) =>
    if fields.isEmpty then some (n, table.decls.find? n) else none

/-- The identifier of a head `C` or `C.{u, …}`. -/
meta def headIdent? (f : Syntax) : Option Ident :=
  if f.isIdent then some ⟨f⟩
  else if f.isOfKind ``Parser.Term.explicitUniv && f[0].isIdent then some ⟨f[0]⟩
  else none

/-- Elaborates `C args` as `C (SI := stepindex%) args` for an `@[indexed]` `C`, unless `args` already
name `SI`. An overloaded `C` becomes a choice node. -/
meta def elabIndexed (stx : Syntax) (head : Syntax) (args : Array Syntax)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let some f := headIdent? head | throwUnsupportedSyntax
  let heads ← indexedHeads f
  unless heads.any (·.2.isSome) do throwUnsupportedSyntax
  let headFor (n : Name) : Syntax :=
    let c := mkCIdentFrom f n
    if head.isIdent then c else head.setArg 0 c
  let mut alts : Array Syntax := #[]
  for (n, i?) in heads do
    let h := if heads.length == 1 then head else headFor n
    let args ← match i? with
      | some i =>
        if args.any fun a => a.isOfKind ``Parser.Term.namedArgument &&
            a[1].getId.eraseMacroScopes == i.name then
          throwUnsupportedSyntax
        pure (#[(← `(Parser.Term.namedArgument| ($(mkIdent i.name) := stepindex%))).raw] ++ args)
      | none => pure args
    alts := alts.push (Syntax.mkApp ⟨h⟩ (args.map (⟨·⟩)))
  let stx' := if h : alts.size = 1 then alts[0] else mkNode choiceKind alts
  withMacroExpansion stx stx' <| elabTerm stx' expectedType?

/-- `C args` for an `@[indexed]` `C`. -/
@[scoped term_elab app] public meta def elabIndexedApp : TermElab := fun stx expectedType? =>
  elabIndexed stx stx[0] stx[1].getArgs expectedType?

/-- A bare `C` or `C.{u, …}` for an `@[indexed]` `C`. -/
@[scoped term_elab ident, scoped term_elab explicitUniv]
public meta def elabIndexedIdent : TermElab := fun stx expectedType? =>
  elabIndexed stx stx #[] expectedType?

/-- Whether `si` is the section's step index. -/
public meta def isSectionSI (si : Term) : CoreM Bool := do
  let n := siExt.getState (← getEnv)
  return !n.isAnonymous && si.raw.isIdent && si.raw.getId == n

open PrettyPrinter Delaborator SubExpr in
/-- Prints `C SI args` as `C args` when `SI` is the section's step index. -/
@[scoped delab app] public meta def delabIndexedApp : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some i := (indexedExt.getState (← getEnv)).decls.find? c | failure
  let some p := i.explicitPos | failure
  guard (e.getAppNumArgs > i.argIdx)
  unless ← isSectionSI (← withNaryArg i.argIdx delab) do failure
  let stx : Term ← Lean.PrettyPrinter.Delaborator.delabApp
  let `($f $args*) := stx | return stx
  return Syntax.mkApp f (args.eraseIdxIfInBounds p)

end Iris.StepIndex

namespace Iris

public section
open Lean Parser in
/-- `local stepindex T` makes `T` the section's step index: `@[indexed]` declarations take it when
theirs is not given, and print without it.

```
local stepindex Nat
variable [CMRA α]          -- CMRA Nat α
example (x : α) : ✓ x → ✓ x := id
```
-/
syntax (name := stepindexCmd) Term.attrKind &"stepindex " term : command
end

open Lean Elab Command in
@[command_elab stepindexCmd]
public meta def elabStepindex : CommandElab := fun stx => do
  let `(command| $k:attrKind stepindex $T:term) := stx | throwUnsupportedSyntax
  unless (← liftMacroM <| toAttributeKind k) == .local do
    throwError "`stepindex` must be `local`: it sets the step index of the current section"
  unless T.raw.isIdent do
    throwError "`stepindex` expects an identifier, but got{indentD T}\n\n\
      Introduce an abbreviation first, e.g. `abbrev MySI := ...` then `local stepindex MySI`."
  runTermElabM fun _ => do
    let Te ← Term.elabType T
    unless (← Meta.trySynthInstance (← Meta.mkAppM `Iris.SIdx #[Te])) matches .some _ do
      throwError "`stepindex` requires a `SIdx` instance for{indentExpr Te}"
  siExt.add T.raw.getId .local
  elabCommand (← `(command| open scoped Iris.StepIndex))

end Iris
