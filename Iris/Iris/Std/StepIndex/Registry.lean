/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Sergei Stepanenko
-/
module

public meta import Lean.ScopedEnvExtension
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# Step Index Registry

Enviornment extension to track the default step index type. Set it with `local stepindex T` and
read it through `stepindex%`. See also `Elab.lean` for how local step indices are used.
-/

open Lean Elab Command Tactic Term Meta

/-- The step index type of the current scope: the name of a section variable, or a global constant
written `_root_.C`. `Name.anonymous` when none is set. -/
public meta initialize siExt : SimpleScopedEnvExtension Name Name ←
  registerSimpleScopedEnvExtension {
    addEntry _ n := n
    initial := .anonymous
  }

/-- Elaborates the step index `n` stored in `siExt`. A section variable is the innermost local of
that name whose type is a universe: a binder `{SI : Type _}` rebinds it, but `(SI : Nat)` does not. -/
public meta def elabSectionSI (n : Name) : TermElabM Expr := do
  if n.getRoot == `_root_ then return ← elabTerm (mkIdent n) none
  let some d := (← getLCtx).findDeclRev? fun d =>
      if d.userName == n && d.type.isSort then some d else none
    | throwError "the section step index `{n}` is not in scope here; \
        mention it in the statement or `include {n}`"
  return d.toExpr

/-- Display the step index type of the current scope. -/
@[expose] elab "#stepindex?" : command => do
  match siExt.getState (← getEnv) with
  | .anonymous => logInfo m!"No step index declared."
  | si => logInfo m!"{si.replacePrefix `_root_ .anonymous}"

/--
`stepindex%` elaborates to the step index type of the current scope. Elaborates to `T` in a section
where `local stepindex T` is set, and to a hole otherwise.
-/
@[expose] elab "stepindex%" : term <= expectedType? => do
  match siExt.getState (← getEnv) with
  | .anonymous => elabTerm (← `(_)) expectedType?
  | n => do
    let si ← elabSectionSI n
    discard <| isDefEq (← inferType si) expectedType?
    return si

/-- Where an `@[indexed SI]` declaration takes its step index: the implicit binder `SI`. -/
public structure IndexedInfo where
  /-- The binder name of the step index. -/
  name : Name
  /-- Its position among all arguments. -/
  argIdx : Nat
  deriving Inhabited, Repr

public meta initialize indexedExt :
    SimplePersistentEnvExtension (Name × IndexedInfo) (NameMap IndexedInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun t (n, i) => t.insert n i
    addImportedFn := fun as => as.foldl (fun t a => a.foldl (fun t (n, i) => t.insert n i) t) {}
  }

/--
`@[indexed SI]` marks a declaration generic over the type of step indices, ie. the type `SI` should
be specialized to the type `T` in any section where `local stepindex T` is set.

Step index types must be declared as implicit binders. If you want explicitly bound index types that
also use the `indexed` attribute, you should define the explicit version as an abbreviation for
the implicit one. For example:
```lean
@[indexed SI, rocq_alias Dist]
class HasDist {SI : Type _} (α : Type _) where
  dist : SI → α → α → Prop
abbrev HasDistᵢ (SI : Type _) (α : Type _) := HasDist (SI := SI) α
```
-/
meta initialize registerBuiltinAttribute {
  name := `indexed
  descr := "the step index of this declaration is filled in by `local stepindex` sections"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwAttrMustBeGlobal `indexed kind
    let some si ← Attribute.Builtin.getIdent? stx
      | throwError "`@[indexed]` expects the name of the step index binder, e.g. `@[indexed SI]`"
    let n := si.getId
    let info ← getConstInfo decl
    -- Find the argument whose name matches the supplied name and record its argument index.
    let r ← MetaM.run' <| forallTelescope info.type fun xs _ => do
      for i in [:xs.size] do
        let d ← xs[i]!.fvarId!.getDecl
        if d.userName == n then
          return some ({ name := n, argIdx := i }, d.binderInfo)
      return none
    -- Check that the binder exists, and is not explicit.
    let some (i, binderInfo) := r
      | throwError "`@[indexed]`: `{decl}` has no binder named `{n}`"
    if binderInfo.isExplicit then
      throwError "`@[indexed]`: the step index `{i.name}` of `{decl}` must be implicit, \
        a `local stepindex` section cannot fill in an explicit argument"
    modifyEnv (indexedExt.addEntry · (decl, i))
}
