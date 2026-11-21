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

/-- The step index argument of `e`, when `e` is `SIdx SI` or an `@[indexed]` constant applied to
its step index. -/
meta def indexArg? (e : Expr) : CoreM (Option Expr) := do
  let .const c _ := e.getAppFn | return none
  let decls := indexedExt.getState (← getEnv)
  let some i := if c == `Iris.SIdx then some 0 else (decls.find? c).map (·.argIdx) | return none
  return if i < e.getAppNumArgs then some (e.getArg! i) else none

/-- Fills the unknown step indices of the term `e` just elaborated with the section's step index.
They are found in two places:
* `e` itself, when it is an `@[indexed]` constant, e.g. `@HasDist ?SI α`;
* the instance arguments created while elaborating `e`, e.g. `?i : SIdx ?SI` in
  `@OFE.eq_dist ?SI ?i α ?o x y`. These are the instance problems added to `pendingMVars` since the
  last call. -/
meta def fillStepIndex (e : Expr) : TermElabM Unit := do
  let n := siExt.getState (← getEnv)
  if n.isAnonymous then return
  let mut indices := (← indexArg? e).toArray
  -- The new instance problems: those in front of the last examined one.
  let pending := (← get).pendingMVars
  let examined? := (← getMCtx).userNames.find? examinedKey
  let mut new := #[]
  let mut probs := #[]
  if let some head := pending.head? then
    if examined? != some head then
      modifyMCtx fun mctx => { mctx with userNames := mctx.userNames.insert examinedKey head }
      for m in pending do
        if some m == examined? then break
        let some s ← getSyntheticMVarDecl? m | continue
        unless s.kind matches .typeClass .. do continue
        let type ← instantiateMVars (← m.getDecl).type
        new := new.push (m, type)
        -- the step index, seeing through binders and reducible aliases such as `HasDistᵢ SI α`
        let a? ← m.withContext <| withReducible <| forallTelescopeReducing type fun _ body => do
          indexArg? (← whnfR body)
        if let some a := a? then
          indices := indices.push a
          probs := probs.push (m, a, s)
  -- Fill the unknown ones with the section's step index
  let unknown ← indices.filterM fun a => return (← instantiateMVars a).isMVar
  if unknown.isEmpty then return
  let some si ← sectionSI? n | do
    -- not in scope: leave them to unification, and explain the ones that stay unknown
    for (m, a, s) in probs do
      if (← instantiateMVars a).isMVar then
        let s := { s with kind := .typeClass (some (notInScope n)) }
        modify fun st => { st with syntheticMVars := st.syntheticMVars.insert m s }
  for a in unknown do
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

/-- Runs the core elaborator `k`, then fills in the step indices that it left unresolved. Another
`term_elab` for the same syntax kind does not run in a `local stepindex` section. -/
meta def withStepIndex (k : TermElab) : TermElab := fun stx expectedType? => do
  let e ← k stx expectedType?
  fillStepIndex e
  return e

section TermElab

/- ## Step Index Elaborators

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

/-- Whether `si` is the section's step index `n`, compared as terms at any universe levels. -/
meta def isSectionSI (n : Name) (si : Expr) : MetaM Bool :=
  withNewMCtxDepth (allowLevelAssignments := true) do
    let some ref ← sectionSI? n | return false
    withReducible <| isDefEq si ref

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
