/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

import Iris.Init
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-! # `local bi PROP`: local defaults for PROP types. -/

open Lean Elab Command Term

namespace Iris

public section

/-- Store the proposition type of the current section, as written in `local bi PROP`. -/
meta initialize biExt : SimpleScopedEnvExtension Syntax (Option Syntax) ←
  registerSimpleScopedEnvExtension {
    addEntry _ s := some s
    initial := none
  }

/-- The proposition type set by `local bi`, or a hole when none is set. -/
@[expose] elab "bi%" : term => do
  match biExt.getState (← getEnv) with
  | none => elabTerm (← `(_)) none
  | some T => elabType T

/-- `local bi T` marks `T` as the default proposition type in the section. -/
syntax (name := biCmd) Lean.Parser.Term.attrKind &"bi " term : command

@[command_elab biCmd]
meta def elabBiCmd : CommandElab := fun stx => do
  let `(command| $k:attrKind bi $T:term) := stx | throwUnsupportedSyntax
  unless (← liftMacroM <| toAttributeKind k) == .local do
    throwError "`bi` must be `local`: it sets the proposition type of the current section"
  biExt.add T .local

end
end Iris
