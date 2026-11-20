/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Sergei Stepanenko
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public meta import Lean.Elab.App
public import Iris.Std.StepIndex.Registry

/-!
# `local stepindex` and its elaborator

The `local stepindex` command is used to configure a default type of step indices in a section.
Step index types to be filled in with section default are configured with the `@[indexed SI]`
attribute.
-/

namespace Iris.StepIndex

open Lean Elab Term Meta

meta def examinedKey : Name := addMacroScope `Iris.StepIndex `examined 1

/-- Fill all placeholders that were marked as step index types with the default step index type. -/
meta def fillStepIndex : TermElabM Unit := do
  -- Only run when there are pending mvars, the term is unexamined, and there is a default index.
  let pending := (← get).pendingMVars
  let some head := pending.head? | return
  let examined? := (← getMCtx).userNames.find? examinedKey
  if examined? == some head then return
  let n := siExt.getState (← getEnv)
  if n.isAnonymous then return
  modifyMCtx fun mctx => { mctx with userNames := mctx.userNames.insert examinedKey head }
  let decls := indexedExt.getState (← getEnv)
  -- Collect entries to be filled
  let mut new := #[]
  let mut indices := #[]
  for m in pending do
    if some m == examined? then break
    let some s ← getSyntheticMVarDecl? m | continue
    unless s.kind matches .typeClass .. do continue
    let type ← instantiateMVars (← m.getDecl).type
    new := new.push (m, type)
    let a? ← m.withContext <| withReducible <| forallTelescopeReducing type fun _ body => do
      let body ← whnfR body
      let .const c _ := body.getAppFn | return none
      let some i := if c == `Iris.SIdx then some 0 else (decls.find? c).map (·.argIdx)
        | return none
      return if i < body.getAppNumArgs then some (body.getArg! i) else none
    if let some a := a? then
      if a.isMVar then indices := indices.push a
  -- Stop if there is nothing to do. Otherwise, fill all entries with `SI`
  if indices.isEmpty then return
  let si ← elabSectionSI n
  for a in indices do
    if (← instantiateMVars a).isMVar then discard <| isDefEq a si
  -- Eagerly allow typeclass synthesis to proceed
  for (m, type) in new.reverse do
    if (← instantiateMVars type) != type then
      try
        if ← m.withContext <| synthesizeInstMVarCore m then
          modify fun s => { s with syntheticMVars := s.syntheticMVars.erase m }
      catch
        | .error .. => pure ()
        | ex => throw ex

/-- Runs the elaborator, then fills in the step indices that it left unresolved. -/
meta def withStepIndex (k : TermElab) : TermElab := fun stx expectedType? => do
  let e ← k stx expectedType?
  fillStepIndex
  return e

section TermElab

/- ## Step Index Elaborators

This section registers general-purpose term elaborators which walk through all expressions,
and specialize any step index arguments to be the section default.

IMPORTANT: The elaborators are scoped. It is possible to disable them completely by closing the
`Iris.StepIndex` scope. A `local stepindex` command opens this scope automatically.
-/

@[scoped term_elab app]
public meta def elabIndexedApp : TermElab := withStepIndex elabApp

@[scoped term_elab ident]
public meta def elabIndexedIdent : TermElab := withStepIndex elabIdent

@[scoped term_elab explicitUniv]
public meta def elabIndexedExplicitUniv : TermElab := withStepIndex elabExplicitUniv

@[scoped term_elab proj]
public meta def elabIndexedProj : TermElab := withStepIndex elabProj

@[scoped term_elab pipeProj]
public meta def elabIndexedPipeProj : TermElab := withStepIndex elabPipeProj

@[scoped term_elab dotIdent]
public meta def elabIndexedDotIdent : TermElab := withStepIndex elabDotIdent

@[scoped term_elab choice]
public meta def elabIndexedChoice : TermElab := withStepIndex elabChoice

end TermElab

/-- Whether `si` is the section's step index `n`, compared as terms. -/
meta def isSectionSI (n : Name) (si : Expr) : MetaM Bool := do
  let ref ← if n.getRoot == `_root_ then
      mkConstWithLevelParams (n.replacePrefix `_root_ .anonymous)
    else match (← getLCtx).findDeclRev? fun d =>
        if d.userName == n && d.type.isSort then some d else none with
      | some d => pure d.toExpr
      | none => return false
  withNewMCtxDepth <| withReducible <| isDefEq si ref

open PrettyPrinter Delaborator SubExpr in
/-- Prints `C (SI := T) args` when the step index `T` of an `@[indexed]` `C` is not the section's. -/
@[scoped delab app] public meta def delabIndexedApp : Delab := do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some i := (indexedExt.getState (← getEnv)).find? c | failure
  guard (e.getAppNumArgs > i.argIdx)
  let n := siExt.getState (← getEnv)
  guard !n.isAnonymous
  let si ← instantiateMVars (e.getArg! i.argIdx)
  guard !si.hasMVar
  if ← isSectionSI n si then failure
  -- print the step index as a named argument
  let pos := (← getPos).pushNaryArg e.getAppNumArgs i.argIdx
  withReader (fun ctx => { ctx with
      optionsPerPos := ctx.optionsPerPos.insert pos
        ((ctx.optionsPerPos.getD pos {}).setBool `pp.analysis.namedArg true) }) delabApp

end Iris.StepIndex

namespace Iris

public section
open Lean Parser in
/-- `local stepindex T` makes `T` the section's step index: a step index that is not determined
otherwise is taken to be `T`.

```
local stepindex Nat
variable [CMRA α]          -- CMRA (SI := Nat) α
example (x : α) : ✓ x → ✓ x := id
```
-/
syntax (name := stepindexCmd) Term.attrKind &"stepindex " term : command
end

open Lean Elab Meta Command in
@[command_elab stepindexCmd]
public meta def elabStepindex : CommandElab := fun stx => do
  let `(command| $k:attrKind stepindex $T:term) := stx | throwUnsupportedSyntax
  unless (← liftMacroM <| toAttributeKind k) == .local do
    throwError "`stepindex` must be `local`: it sets the step index of the current section"
  unless T.raw.isIdent do
    throwError "`stepindex` expects an identifier, but got{indentD T}\n\n\
      Introduce an abbreviation first, e.g. `abbrev MySI := ...` then `local stepindex MySI`."
  let n ← runTermElabM fun _ => do
    let Te ← Term.elabType T
    unless (← trySynthInstance (← mkAppM `Iris.SIdx #[Te])) matches .some _ do
      throwError "`stepindex` requires a `SIdx` instance for{indentExpr Te}"
    -- a section variable is stored by name, a constant by its full name
    let n := T.raw.getId
    if Te.isFVar then return n
    let .const c _ := Te.getAppFn | throwError "`stepindex` expects a section variable or a constant"
    return `_root_ ++ c
  siExt.add n .local
  elabCommand (← `(command| open scoped Iris.StepIndex))

end Iris
