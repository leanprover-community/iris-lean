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

The step index type of the current scope, set by `local stepindex T` (see `Iris.Std.StepIndex.Elab`).
Notations read it through `stepindex%`.
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
Notations expand to it, so that the step index is read at the use site.
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

/-- Where an `@[indexed]` declaration takes its step index: the implicit binder whose type is
`stepindex (Type _)`. -/
public structure IndexedInfo where
  /-- The binder name of the step index. -/
  name : Name
  /-- Its position among all arguments. -/
  argIdx : Nat
  deriving Inhabited, Repr

/-- The `@[indexed]` declarations. -/
public meta initialize indexedExt :
    SimplePersistentEnvExtension (Name × IndexedInfo) (NameMap IndexedInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun t (n, i) => t.insert n i
    addImportedFn := fun as => as.foldl (fun t a => a.foldl (fun t (n, i) => t.insert n i) t) {}
  }

/--
`@[indexed]` marks a declaration over a step index (the implicit binder of type
`stepindex (Type _)`, possibly a section variable). `local stepindex T` sections consult it for
classes: there an instance problem of an `@[indexed]` class whose step index nothing else determines
takes `T`, so that `[C a]` elaborates as `[C (SI := T) a]`.
-/
meta initialize registerBuiltinAttribute {
  name := `indexed
  descr := "the step index of this declaration is filled in by `local stepindex` sections"
  applicationTime := .afterTypeChecking
  add := fun decl _ kind => do
    unless kind == .global do throwError "`@[indexed]` must be global"
    let info ← getConstInfo decl
    let r ← Meta.MetaM.run' <| Meta.forallTelescope info.type fun xs _ => do
      for i in [:xs.size] do
        let d ← xs[i]!.fvarId!.getDecl
        if isStepIndexBinder d.type then
          return some (({ name := d.userName, argIdx := i } : IndexedInfo), d.binderInfo)
      return none
    let some (i, binderInfo) := r
      | throwError "`@[indexed]`: `{decl}` has no step index binder of type `stepindex (Type _)`"
    if binderInfo.isExplicit then
      throwError "`@[indexed]`: the step index `{i.name}` of `{decl}` must be implicit, \
        a `local stepindex` section cannot fill in an explicit argument"
    modifyEnv (indexedExt.addEntry · (decl, i))
}
