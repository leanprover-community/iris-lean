/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

import Lean
public meta import Lean

/-!
# Step Index Registry

An attribute holding a default type for step indices that can be registered per-section.
-/

open Lean Elab Command Tactic

/-- Extension used to track the current default type for step indices -/
public meta initialize siExt : SimpleScopedEnvExtension Name Name ←
  registerSimpleScopedEnvExtension {
    addEntry _ n := n
    initial := Name.anonymous
  }

/--
`stepindex T` declares `T` to be the default step index type used by Iris notation. It is
required to be scoped as either `local` or `scoped`: `global` indices are not permitted.
-/
@[expose] elab kind:Lean.Parser.Term.attrKind "stepindex" x:ident : command => do
  let attrK := (← liftMacroM <| toAttributeKind kind)
  match attrK with
  | .local | .scoped  => siExt.add x.getId attrK
  | _ => throwError "stepindex must be either `scoped` or `local`."

/-- Query the type of step indices -/
@[expose] elab "#stepindex?" : command => do logInfo m!"{siExt.getState (← getEnv)}"

/--
`stepindex%` elaborates to the step index type in scope, resolved **eagerly** as a term.
-/
@[expose] elab "stepindex%" : term => do
  let n := siExt.getState (← getEnv)
  if n.isAnonymous then
    throwError "stepindex%: no step index in scope; declare one with `local stepindex T`"
  Term.elabTerm (mkIdent n) none

/--
Close a goal with the step index type in scope, resolved at the use site.

Does nothing when there is no goal left: as the default value of a parameter this tactic runs
even if that parameter was already determined by unification, which must not be an error.
-/
@[expose] elab "infer_stepindex" : tactic => do
  if (← getGoals).isEmpty then return
  match siExt.getState (← getEnv) with
  | .anonymous =>
    throwError "infer_stepindex: no step index in scope; declare one with `local stepindex T`"
  | n => evalTactic (← `(tactic| exact $(mkIdent n)))
