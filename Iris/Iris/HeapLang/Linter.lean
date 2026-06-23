/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang.Notation
public meta import Lean.Elab.Command
public meta import Lean.Linter.Util

public meta section
namespace Iris.HeapLang.Linter

open Lean Lean.Elab Lean.Elab.Command Lean.Linter

/--
The `linter.heapLang.freeVars` linter warns about unbound variables appearing
in a HeapLang expression written with the `hl(...)` / `hl_val(...)` notation.

Default value is `true`.
-/
register_option linter.heapLang.freeVars : Bool := {
  defValue := true
  descr := "warn about unbound variables in HeapLang `hl(...)` expressions"
}

/-- The result of inspecting a single `hl_binder`. -/
inductive BinderInfo where
  /-- A named binder `x`, which brings `name` into scope. -/
  | named (name : String)
  /-- The anonymous binder `_`; brings nothing into scope. -/
  | anon
  /-- An escaped binder `&t` whose name is a meta-level value we cannot inspect. We cannot
      tell whether a variable in the body it scopes refers to it, so that body is left
      unchecked entirely (see `extendScope`). -/
  | escaped
deriving Inhabited

/-- Classify a `hl_binder` syntax node. -/
def classifyBinder (stx : Syntax) : BinderInfo :=
  match stx with
  | `(hl_binder| & $_) => .escaped
  | `(hl_binder| $i:ident) => .named i.getId.toString
  | _ => .anon -- `_`

/-- Extend `scope` with the names bound by `bs`, returning the scope under which the body of
the binder should be analyzed. If `bs` binds an escaped binder, returns `none` to flag
the analysis as incomplete. -/
def extendScope (scope : List String) (bs : Array Syntax) : Option (List String) := Id.run do
  let mut scope := scope
  for b in bs do
    match classifyBinder b with
    | .named n => scope := n :: scope
    | .anon => pure ()
    | .escaped => return none
  return some scope

def matchArmBinder (stx : Syntax) : Option Syntax :=
  match stx with
  | `(hl_match_arm| injl($b)) => some b
  | `(hl_match_arm| injr($b)) => some b
  | `(hl_match_arm| some($b)) => some b
  | _ => none -- `none()`

partial def analyze (scope : List String) (stx : Syntax) :
    CommandElabM Unit := do
  let underBinders (bs : Array Syntax) (body : Syntax) : CommandElabM Unit := do
    if let some scope := extendScope scope bs then analyze scope body
  match stx with
  | `(hl_exp| $i:ident) =>
    let name := i.getId.toString
    unless scope.contains name do
      logLint linter.heapLang.freeVars i m!"\
        unbound HeapLang variable `{name}`.\n\n\
        • If you meant a meta-level (Lean) definition, escape it: `&{name}`.\n\
        • Otherwise `{name}` is a free variable, and likely a typo.\n\
        You can suppress this warning with `set_option linter.heapLang.freeVars false`"
  | `(hl_exp| & $_) => pure ()
  | `(hl_exp| # $_) => pure ()
  | `(hl_exp| v($_)) => pure ()
  | `(hl_val| & $_) => pure ()
  | `(hl_val| # $_) => pure ()
  | `(hl_exp| λ $bs*, $e) => underBinders (bs.map (·.raw)) e
  | `(hl_exp| rec $f $xs* := $e) => underBinders (#[f.raw] ++ xs.map (·.raw)) e
  | `(hl_exp| let $b := $e1; $e2) =>
    analyze scope e1
    underBinders #[b.raw] e2
  | `(hl_exp| match $e with | $a1 => $e1 | $a2 => $e2) =>
    analyze scope e
    underBinders (matchArmBinder a1.raw).toArray e1.raw
    underBinders (matchArmBinder a2.raw).toArray e2.raw
  | `(hl_val| λ $bs*, $e) => underBinders (bs.map (·.raw)) e
  | `(hl_val| rec $f $xs* := $e) => underBinders (#[f.raw] ++ xs.map (·.raw)) e
  | _ => for arg in stx.getArgs do analyze scope arg

/--
Collect every *outermost* `hl(...)` / `hl_val(...)` embedding in a command's syntax.
This does not descend into nested `&(hl(...))` forms.
-/
partial def collectEntries (stx : Syntax) (acc : Array Syntax) : Array Syntax := Id.run do
  match stx with
  | `(hl($e)) => return acc.push e
  | `(hl% $e) => return acc.push e
  | `(hl_val($v)) => return acc.push v
  | `(hl_val% $v) => return acc.push v
  | _ =>
    let mut acc := acc
    for arg in stx.getArgs do
      acc := collectEntries arg acc
    return acc

/-- The HeapLang free-variable linter. -/
def freeVarsLinter : Linter where
  run := fun stx => do
    unless getLinterValue linter.heapLang.freeVars (← getLinterOptions) do return
    for entry in collectEntries stx #[] do
      analyze [] entry
  name := `Iris.HeapLang.freeVars

initialize addLinter freeVarsLinter

end Iris.HeapLang.Linter
