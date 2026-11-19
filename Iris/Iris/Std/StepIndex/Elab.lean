/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.Elab.AuxDef
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public import Iris.Std.StepIndex.Registry

/-!
# `@[indexed]`, `local stepindex`, and their notations

`@[indexed SI]` gives a declaration `C` with a step index binder `SI` a scoped notation `Cᵢ` (in
`Iris.StepIndex`): `Cᵢ`, alone or applied, stands for `C (SI := stepindex%)`, so that the step
index is known before instance search runs. The applied form takes the arguments in, so that named
arguments such as `Cᵢ (α := X)` go to `C`. `local stepindex T` opens these notations, together with a delaborator that prints `C T args`
back as `Cᵢ args`. `C` itself is unchanged.

Spellings: the declaration name without a leading `Iris.`, followed by `ᵢ`. A type (a class or
structure, or anything else ending in a sort) is also spelled by its last component, e.g. both
`OFE.Homᵢ` and `Homᵢ`; any other declaration only by its qualified name, e.g. `OFE.eq_distᵢ`.
-/

namespace Iris.StepIndex

open Lean

/-- The notation spellings of `decl` (see the module docstring). -/
meta def spellingsOf (decl : Name) (isType : Bool) : Array String :=
  let n := decl.replacePrefix `Iris .anonymous
  let qualified := n.toString (escape := false) ++ "ᵢ"
  if isType && !n.isAtomic then #[n.getString! ++ "ᵢ", qualified] else #[qualified]

/-- The step index binder `si` of `decl`, and the spellings of its notation. -/
meta def indexedInfo? (decl si : Name) : MetaM (Option IndexedInfo) := do
  Meta.forallTelescope (← getConstInfo decl).type fun xs body => do
    let mut expl := 0
    for i in [:xs.size] do
      let d ← xs[i]!.fvarId!.getDecl
      if d.userName == si then
        return some { argIdx := i,
                      explicitPos := if d.binderInfo.isExplicit then some expl else none,
                      spellings := spellingsOf decl body.isSort }
      if d.binderInfo.isExplicit then expl := expl + 1
    return none

/-- The syntax kind of the notation `tok` of `decl`, bare or applied. -/
meta def notationKind (decl : Name) (tok : String) (applied : Bool) : Name :=
  .str `Iris.StepIndex s!"{decl} {tok}{if applied then " app" else ""}"

/--
Expands the notation `tok.{us} args` of `decl` (universes and arguments optional) to
`decl.{us} (si := stepindex%) args`, where `si` is the step index binder.
-/
public meta def expandIndexedNotation (decl si : Name) : Macro := fun stx => do
  let c := mkCIdentFrom stx[0] decl (canonical := true)
  let us := stx[1].getArgs  -- empty, or `.{`, levels, `}`
  let head : Term := ⟨if us.isEmpty then c.raw else mkNode ``Parser.Term.explicitUniv (#[c] ++ us)⟩
  let args : Array Term := if stx.getNumArgs > 2 then stx[2].getArgs.map (⟨·⟩) else #[]
  `($head ($(mkIdent si) := stepindex%) $args*)

section
open Elab Command

/-- Declares the scoped notations `toks` of `decl`, each bare and applied, with optional universes,
and the macro that expands them. -/
meta def addIndexedNotations (decl si : Name) (toks : Array String) : CoreM Unit :=
  liftCommandElabM do
    let ns := mkIdent `Iris.StepIndex
    elabCommand (← `(namespace $ns))
    for tok in toks do
      let bare := mkIdent (.mkSimple (notationKind decl tok false).getString!)
      let applied := mkIdent (.mkSimple (notationKind decl tok true).getString!)
      let tok := Syntax.mkStrLit tok
      elabCommand (← `(scoped syntax:max (name := $bare) $tok:str (noWs ".{" level,+ "}")? : term))
      elabCommand (← `(scoped syntax:lead (name := $applied)
        $tok:str (noWs ".{" level,+ "}")? (Lean.Parser.Term.argument)+ : term))
    -- an antiquotation, since `@[scoped macro k]` would parse `macro` as the command
    let kind ← `(Parser.Term.attrKind| scoped)
    let attrs ← (toks.flatMap fun tok => #[notationKind decl tok false, notationKind decl tok true])
      |>.mapM fun k => `(Parser.Term.attrInstance| $kind:attrKind macro $(mkIdent k))
    elabCommand (← `(@[$attrs,*] public aux_def indexed $(mkIdent decl) : Macro :=
      expandIndexedNotation $(quote decl) $(quote si)))
    elabCommand (← `(end $ns))

end

/--
`@[indexed SI]` marks a declaration whose step index is its binder `SI` (explicit or implicit,
possibly a section variable), to be filled in by `local stepindex T` sections: there the notation
`Cᵢ a` elaborates as `C (SI := T) a`, and `C T a` prints back as `Cᵢ a`.
-/
meta initialize registerBuiltinAttribute {
  name := `indexed
  descr := "the step index of this declaration is filled in by `local stepindex` sections"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "`@[indexed]` must be global"
    let some si ← Attribute.Builtin.getIdent? stx
      | throwError "`@[indexed]` takes the name of the step index binder, e.g. `@[indexed SI]`"
    let some i ← (indexedInfo? decl si.getId).run'
      | throwError "`@[indexed {si}]`: `{decl}` has no binder `{si}`"
    modifyEnv (indexedExt.addEntry · (decl, i))
    addIndexedNotations decl si.getId i.spellings
}

open PrettyPrinter Delaborator SubExpr in
/-- Prints `C SI args` with the notation of `C` when `SI` is the section's step index. -/
@[scoped delab app] public meta def delabIndexedApp : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some i := (indexedExt.getState (← getEnv)).find? c | failure
  let some tok := i.spellings[0]? | failure
  let si := siExt.getState (← getEnv)
  guard (!si.isAnonymous && e.getAppNumArgs > i.argIdx)
  let `($n:ident) ← withNaryArg i.argIdx delab | failure
  guard (n.getId == si)
  let args ← match ← delabApp with
    | `($_:ident $args*) => pure (args.map (·.raw))
    | `($_:ident) => pure #[]
    | _ => failure
  let args := match i.explicitPos with
    | some p => args.eraseIdxIfInBounds p
    | none => args
  if args.isEmpty then
    return ⟨mkNode (notationKind c tok false) #[mkAtom tok, mkNullNode]⟩
  return ⟨mkNode (notationKind c tok true) #[mkAtom tok, mkNullNode, mkNullNode args]⟩

end Iris.StepIndex

namespace Iris

public section
open Lean Parser in
/-- `local stepindex T` makes `T` the section's step index: there the notation `Cᵢ` of an
`@[indexed]` declaration `C` stands for `C (SI := T)`, and `C T` prints as `Cᵢ`.

```
local stepindex Nat
variable [OFEᵢ α]          -- OFE Nat α
example (x y : α) : x = y ↔ ∀ n, x ≡{n}≡ y := OFE.eq_distᵢ
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
