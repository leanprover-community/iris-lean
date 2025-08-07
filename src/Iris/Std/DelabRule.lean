/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Lean.PrettyPrinter.Delaborator

namespace Iris.Std
open Lean Lean.Macro

-- macro for adding unexpanders for function applications
open Lean.Parser.Term in
private def matchAlts' := leading_parser matchAlts

syntax "delab_rule" ident matchAlts' : command
macro_rules
  | `(delab_rule $f $[| $p => $s]*) => do
    let f := f.getId
    if f.isAnonymous then
      throwUnsupported
    let f ← match ← Macro.resolveGlobalName f with
      | [(name, [])] => pure name
      | _           => throwUnsupported

    let (p : TSyntaxArray `term) := p
    if p.any (· matches `(`($$_))) then
      `(@[app_unexpander $(mkIdent f)]
        def unexpand : Lean.PrettyPrinter.Unexpander
          $[| $p => $s]*)
    else
      `(@[app_unexpander $(mkIdent f)]
        def unexpand : Lean.PrettyPrinter.Unexpander
          $[| $p => $s]*
          | _ => throw ())

/- Suggested fix
syntax "delab_rule" ident matchAlts' : command
macro_rules
  | `(delab_rule $f $[| $p => $s]*) => do
    let f := f.getId
    if f.isAnonymous then
      throwUnsupported
    let f ← match ← Macro.resolveGlobalName f with
      | [(name, [])] => pure name
      | _           => throwUnsupported

    `(@[app_unexpander $(mkIdent f)]
      def unexpand : Lean.PrettyPrinter.Unexpander
        $[| $p => $s]*
        | _ => throw ())
-/
