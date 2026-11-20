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

The `stepindex` command, and the scoped elaborators that fill in step indices (see
`Iris.Algebra.StepIndex`). Applications and identifiers of a sugared section are elaborated as
usual; a step index that this leaves undetermined, with an instance problem waiting for it, is then
unified with the section's.
-/

namespace Iris.StepIndex

open Lean Elab Term Meta

meta def examinedKey : Name := `_iris_stepindex_examined

meta def fillStepIndex : TermElabM Unit := do
  let pending := (← get).pendingMVars
  let some head := pending.head? | return
  let examined? := (← getMCtx).userNames.find? examinedKey
  if examined? == some head then return
  let n := siExt.getState (← getEnv)
  if n.isAnonymous then return
  modifyMCtx fun mctx => { mctx with userNames := mctx.userNames.insert examinedKey head }
  let decls := indexedExt.getState (← getEnv)
  let mut new := #[]
  let mut indices := #[]
  for m in pending do
    if some m == examined? then break
    let some s ← getSyntheticMVarDecl? m | continue
    unless s.kind matches .typeClass .. do continue
    let type ← instantiateMVars (← m.getDecl).type
    new := new.push (m, type)
    let body := type.getForallBody
    let .const c _ := body.getAppFn | continue
    let some i := if c == `Iris.SIdx then some 0 else (decls.find? c).map (·.argIdx) | continue
    if i < body.getAppNumArgs then
      let a := body.getArg! i
      if a.isMVar then indices := indices.push a
  if indices.isEmpty then return
  let si ← elabTerm (mkIdent n) none
  for a in indices do
    if (← instantiateMVars a).isMVar then discard <| isDefEq a si
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

-- The elaborators below have no docstrings: hovering any identifier would show them.

-- `f args`.
@[scoped term_elab app] public meta def elabIndexedApp : TermElab := withStepIndex elabApp

-- `c`, `x.f`.
@[scoped term_elab ident] public meta def elabIndexedIdent : TermElab := withStepIndex elabIdent

-- `c.{u, …}`.
@[scoped term_elab explicitUniv]
public meta def elabIndexedExplicitUniv : TermElab := withStepIndex elabExplicitUniv

-- `(e).f`, `e.1`.
@[scoped term_elab proj] public meta def elabIndexedProj : TermElab := withStepIndex elabProj

-- `e |>.f args`.
@[scoped term_elab pipeProj]
public meta def elabIndexedPipeProj : TermElab := withStepIndex elabPipeProj

-- `.f`.
@[scoped term_elab dotIdent]
public meta def elabIndexedDotIdent : TermElab := withStepIndex elabDotIdent

-- An overloaded notation.
@[scoped term_elab choice] public meta def elabIndexedChoice : TermElab := withStepIndex elabChoice

/-- Whether `si` is the section's step index `n`, compared as terms. -/
meta def isSectionSI (n : Name) (si : Expr) : MetaM Bool := do
  let ref ← match (← getLCtx).findFromUserName? n with
    | some d => pure d.toExpr
    | none =>
      let some c := (← resolveGlobalName n).find? (·.2.isEmpty) | return false
      mkConstWithLevelParams c.1
  withNewMCtxDepth <| withReducible <| isDefEq si ref

open PrettyPrinter Delaborator SubExpr in
/-- Prints `C (SI := T) args` when the step index `T` of an `@[indexed]` `C` is not the section's. -/
@[scoped delab app] public meta def delabIndexedApp : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some i := (indexedExt.getState (← getEnv)).find? c | failure
  guard (e.getAppNumArgs > i.argIdx)
  let n := siExt.getState (← getEnv)
  guard !n.isAnonymous
  let si ← instantiateMVars (e.getArg! i.argIdx)
  guard !si.hasMVar
  if ← isSectionSI n si then failure
  let siStx ← withNaryArg i.argIdx delab
  let stx ← delabApp
  match stx with
  | `($f:ident $args*) => `($f:ident ($(mkIdent i.name) := $siStx) $args*)
  | `($f:ident) => `($f:ident ($(mkIdent i.name) := $siStx))
  | _ => return stx

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
