/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.ScopedEnvExtension
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.Elab.Syntax
public meta import Lean.Elab.BuiltinCommand
public meta import Lean.Elab.Quotation.Precheck

/-!
# Step Index Registry

The step index type of the current scope, set by `local stepindex T` (see `Iris.Algebra.StepIndex`).
The `Iris.StepIndexSugar` notations read it through `stepindex%`.
-/

open Lean Elab Command Tactic

/-- The step index type of the current scope (`Name.anonymous` when none is set). -/
public meta initialize siExt : SimpleScopedEnvExtension Name Name ←
  registerSimpleScopedEnvExtension {
    addEntry _ n := n
    initial := Name.anonymous
  }

/-- Show the step index type of the current scope. -/
@[expose] elab "#stepindex?" : command => do
  match siExt.getState (← getEnv) with
  | .anonymous => logInfo m!"No step index declared."
  | si => logInfo m!"{si}"

/--
`stepindex%` elaborates to the step index type of the current scope (set by `local stepindex T`).
The `Iris.StepIndexSugar` notations expand to it, so that the step index is read at the use site.
It elaborates to a hole when no step index is set.
-/
@[expose] elab "stepindex%" : term <= expectedType? => do
  match siExt.getState (← getEnv) with
  | .anonymous => Term.elabTerm (← `(_)) expectedType?
  | n => Term.elabTerm (mkIdent n) expectedType?

/--
`SI : stepindex (Type _)` marks `SI` as a step index binder, like `outParam` marks an output:
`@[indexed]` declarations take theirs from the `local stepindex` section. It elaborates to its
argument with a metadata marker (no constant to unfold), so it costs nothing in unification.
-/
@[expose] elab "stepindex " t:term:max : term => do
  let e ← Term.elabType t
  return .mdata (KVMap.empty.insert `iris.stepindex (.ofBool true)) e

/-- Whether a binder type carries the `stepindex` marker. -/
public meta def isStepIndexBinder : Expr → Bool
  | .mdata m _ => m.getBool `iris.stepindex
  | _ => false

/-- Where an `@[indexed]` declaration takes its step index: the binder whose type is
`stepindex (Type _)`. -/
public structure IndexedInfo where
  /-- The binder name of the step index. -/
  name : Name
  /-- Its position among all arguments. -/
  argIdx : Nat
  /-- Its position among the explicit arguments, or `none` when it is not explicit. -/
  explicitPos : Option Nat
  deriving Inhabited, Repr

/-- Indexed declarations and the declaration that first generated each notation spelling. -/
public meta structure IndexedTable where
  decls : NameMap IndexedInfo := {}
  notations : NameMap Name := {}
  deriving Inhabited

/-- Relative spellings of an indexed declaration. The full name is reserved for explicit use. -/
public meta def indexedSpellings (n : Name) : List Name :=
  let cs := if n.isAtomic then n.components else n.components.tail!
  (List.range cs.length).map fun i => (cs.drop i).foldl (· ++ ·) .anonymous

/-- Add an indexed declaration and its relative notation spellings. Fully qualified names remain
ordinary identifiers, providing access to the explicit API. -/
public meta def IndexedTable.insert (t : IndexedTable) (n : Name) (i : IndexedInfo) : IndexedTable :=
  { decls := t.decls.insert n i,
    notations := (indexedSpellings n).foldl
      (fun m s => if m.contains s then m else m.insert s n) t.notations }

/-- The `@[indexed]` declarations. -/
public meta initialize indexedExt :
    SimplePersistentEnvExtension (Name × IndexedInfo) IndexedTable ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun t (n, i) => t.insert n i
    addImportedFn := fun as => as.foldl (fun t a => a.foldl (fun t (n, i) => t.insert n i) t) {}
  }

/-- Independent modules may both generate a parser for the same spelling. Only the first owner
in the combined environment parses it; the shared elaborator still resolves every declaration. -/
public meta def indexedNotationGuard (owner spelling : Name) : Parser.Parser where
  fn ctx s := if (indexedExt.getState ctx.env).notations.find? spelling == some owner then s
    else s.mkUnexpectedError "inactive step-index notation"

@[combinator_parenthesizer indexedNotationGuard]
public meta def indexedNotationGuard.parenthesizer (_owner _spelling : Name) :
    PrettyPrinter.Parenthesizer := pure ()

@[combinator_formatter indexedNotationGuard]
public meta def indexedNotationGuard.formatter (_owner _spelling : Name) :
    PrettyPrinter.Formatter := pure ()

/-- Recover ordinary application syntax from a generated notation. Explicit `@` applications
are represented separately so that they bypass specialization. -/
public meta def indexedNotationParts (stx : Syntax) : Ident × Term × Array Syntax × Bool := Id.run do
  let explicit := stx[0].getAtomVal == "@"
  let offset := if explicit then 1 else 0
  let f : Ident := ⟨stx[offset]⟩
  let head : Term := if stx[offset + 1].getNumArgs == 0 then f
    else ⟨mkNode ``Parser.Term.explicitUniv (#[f] ++ stx[offset + 1].getArgs)⟩
  let head := if explicit then ⟨mkNode ``Parser.Term.explicit #[stx[0], head]⟩ else head
  let args := if stx.getNumArgs == offset + 3 then stx[offset + 2].getArgs else #[]
  return (f, head, args, explicit)

/-- Construct an application without adding an empty application node. -/
public meta def applyIndexedNotationArgs (head : Term) (args : Array Syntax) : Syntax :=
  if args.isEmpty then head else Syntax.mkApp head (args.map (⟨·⟩))

/-- Expand a generated name notation, leaving argument elaboration to Lean. The application
notation captures its arguments so named arguments are supplied before implicit arguments are
inserted. There is no registration on the general `app`, `ident`, or `explicitUniv` syntax. -/
public meta def elabIndexedNotation : Term.TermElab := fun stx expectedType? => do
  let (f, head, args, explicit) := indexedNotationParts stx
  if explicit || (← Term.isLocalIdent? f).isSome then
    return ← Term.elabTerm (applyIndexedNotationArgs head args) expectedType?
  let table := indexedExt.getState (← getEnv)
  let .ident _ _ _ pre := f.raw | throwUnsupportedSyntax
  let resolved := pre.filterMap fun | .decl n [] => some (n, []) | _ => none
  let heads ← if resolved.isEmpty then resolveGlobalName f.getId else pure resolved
  let mut alts : Array Syntax := #[]
  for (n, fields) in heads do
    if !fields.isEmpty then continue
    let resolved := mkCIdentFrom f n
    let head := if head.raw.isIdent then resolved.raw else head.raw.setArg 0 resolved
    let mut args := args
    if let some i := table.decls.find? n then
      unless args.any fun a => a.isOfKind ``Parser.Term.namedArgument &&
          a[1].getId.eraseMacroScopes == i.name do
        let named ← `(Parser.Term.namedArgument| ($(mkIdent i.name) := stepindex%))
        args := #[named] ++ args
    alts := alts.push (applyIndexedNotationArgs ⟨head⟩ args)
  let expanded := if alts.isEmpty then applyIndexedNotationArgs head args
    else if alts.size == 1 then alts[0]!
    else mkNode choiceKind alts
  Term.withMacroExpansion stx expanded <| Term.elabTerm expanded expectedType?

/-- Precheck the original identifier and arguments in syntax quotations. -/
public meta def precheckIndexedNotation : Term.Quotation.Precheck := fun stx => do
  let (_, head, args, _) := indexedNotationParts stx
  Term.Quotation.precheck (applyIndexedNotationArgs head args)

/-- Generate scoped, nonreserved name and application notations for one relative spelling.
The application parser has ordinary application precedence, so `g C a` still means `(g C) a`.
The bare name parser also works in argument position. -/
public meta def addIndexedNotation (decl : Name) (spelling : Name) (idx : Nat) : CommandElabM Unit :=
    withNamespace `Iris.StepIndexSugar do
  -- Derive auxiliary names from the declaration, so independent modules can generate the same
  -- short spelling without declaring the same parser constant.
  let kind := decl ++ .mkSimple s!"stepIndexNotation{idx}"
  let guardName := kind ++ `guard
  elabCommand (← `(
    public meta def $(mkIdent (`_root_ ++ guardName)) : Lean.Parser.Parser :=
      indexedNotationGuard $(quote decl) $(quote spelling)))
  -- Keep an actual identifier child, so quotations preserve its hygiene and resolved names.
  let token ← `(Lean.ParserDescr.binary `andthen
    (Lean.ParserDescr.unary `lookahead
      (Lean.ParserDescr.nonReservedSymbol $(quote spelling.toString) true))
    (Lean.ParserDescr.parser ``Lean.Parser.ident))
  let token ← `(Lean.ParserDescr.binary `andthen $token (Lean.ParserDescr.parser $(quote guardName)))
  let head ← `(Lean.ParserDescr.binary `andthen $token
    (Lean.ParserDescr.unary `optional (Lean.ParserDescr.parser ``Lean.Parser.Term.explicitUnivSuffix)))
  for (suffix, head) in [(Name.anonymous, head),
      (`explicit, ← `(Lean.ParserDescr.binary `andthen (Lean.ParserDescr.symbol "@") $head))] do
    let kind := kind ++ suffix
    for (suffix, prec, body) in [(Name.anonymous, Parser.maxPrec, head),
        (`app, Parser.leadPrec, ← `(Lean.ParserDescr.binary `andthen $head
          (Lean.ParserDescr.unary `many1 (Lean.ParserDescr.parser ``Lean.Parser.Term.argument))))] do
      elabCommand (← `(
        @[scoped term_parser high] public meta def $(mkIdent (`_root_ ++ kind ++ suffix)) :
            Lean.ParserDescr := Lean.ParserDescr.node $(quote kind) $(quote prec) $body))
    elabCommand (← `(
      @[term_elab $(mkIdent kind)] public meta def $(mkIdent (`_root_ ++ kind ++ `expand)) :
          Lean.Elab.Term.TermElab := elabIndexedNotation))
    elabCommand (← `(
      @[quot_precheck $(mkIdent kind)] public meta def $(mkIdent (`_root_ ++ kind ++ `precheck)) :
          Lean.Elab.Term.Quotation.Precheck := precheckIndexedNotation))

/--
`@[indexed]` marks a declaration whose step index (the binder of type `stepindex (Type _)`, explicit
or implicit, possibly a section variable) is filled in by `local stepindex T` sections: there `C a`
elaborates as `C T a` (or `C (SI := T) a` for an implicit step index) and prints back as `C a`.
-/
meta initialize registerBuiltinAttribute {
  name := `indexed
  descr := "the step index of this declaration is filled in by `local stepindex` sections"
  applicationTime := .afterTypeChecking
  add := fun decl _ kind => do
    unless kind == .global do throwError "`@[indexed]` must be global"
    let info ← getConstInfo decl
    let r ← Meta.MetaM.run' <| Meta.forallTelescope info.type fun xs _ => do
      let mut expl := 0
      let mut r : Option IndexedInfo := none
      for i in [:xs.size] do
        let d ← xs[i]!.fvarId!.getDecl
        if r.isNone && isStepIndexBinder d.type then
          r := some { name := d.userName, argIdx := i,
                      explicitPos := if d.binderInfo.isExplicit then some expl else none }
        if d.binderInfo.isExplicit then expl := expl + 1
      return r
    let some i := r
      | throwError "`@[indexed]`: `{decl}` has no step index binder of type `stepindex (Type _)`"
    let table := indexedExt.getState (← getEnv)
    let spellings := indexedSpellings decl |>.filter fun n => !table.notations.contains n
    modifyEnv (indexedExt.addEntry · (decl, i))
    liftCommandElabM do
      for (spelling, idx) in spellings.zipIdx do
        addIndexedNotation decl spelling idx
}
