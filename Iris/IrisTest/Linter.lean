/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

meta import Iris.Std.Linter.Style
meta import Iris.Std.Linter.DupNamespace
meta import Iris.Std.Linter.Whitespace

@[expose] public section

namespace IrisTest

/-! ## `linter.iris.style.cdot` -/

/- Tests that a focusing dot typed as a plain `.` is flagged. -/
/-- warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'. -/
#guard_msgs (whitespace := lax, substring := true) in
example : True := by
  . trivial

/- Tests that a cdot sitting alone on its line is flagged, even when typed correctly. -/
/-- warning: This central dot `·` is isolated; please merge it with the next line. -/
#guard_msgs (whitespace := lax, substring := true) in
example : True := by
  ·
    trivial

/-! ## `linter.iris.style.dollarSyntax` -/

/- Tests that `$` used as the pipe operator is flagged. -/
/-- warning: Please use '<|' instead of '$' for the pipe operator. -/
#guard_msgs (whitespace := lax, substring := true) in
example : Nat := id $ 0

/-! ## `linter.iris.style.lambdaSyntax` -/

/- Tests that `λ` is flagged. -/
/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
Following the Mathlib style guide, the 'λ' syntax is deprecated in Iris-Lean.
-/
#guard_msgs (whitespace := lax, substring := true) in
set_option linter.iris.style.lambdaSyntax true in
example : Nat → Nat := λ n => n

/-! ## `linter.iris.style.nameCheck` -/

/- Tests that a declaration name containing `__` is flagged. -/
/--
warning: The declaration 'foo__bar' contains '__', which does not follow the Iris-Lean naming
conventions. Consider using single underscores instead.
-/
#guard_msgs (whitespace := lax, substring := true) in
set_option linter.iris.style.nameCheck true in
theorem foo__bar : True := trivial

/-! ## `linter.iris.style.openClassical` -/

section OpenClassical

/- Tests that an unscoped `open Classical` is flagged. -/
/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.
-/
#guard_msgs (whitespace := lax, substring := true) in
open Classical

/- Tests that `open scoped Classical` is flagged too. -/
/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.
-/
#guard_msgs (whitespace := lax, substring := true) in
open scoped Classical

/- Tests that `open Classical in` is accepted. -/
#guard_msgs in
open Classical in
theorem openClassicalScoped : True := trivial

end OpenClassical

/-! ## `linter.iris.style.show` -/

/- Tests that a `show` which changes the goal is flagged. -/
/--
warning: The `show` tactic should only be used to indicate intermediate goal states for
readability.
However, this tactic invocation changed the goal. Please use `change` instead for these purposes.
-/
#guard_msgs (whitespace := lax, substring := true) in
example : id True := by
  show True
  trivial

/- Tests that a `show` which restates the goal verbatim is accepted. -/
#guard_msgs in
example : True := by
  show True
  trivial

/-! ## `linter.iris.dupNamespace` -/

namespace Dup

/- Tests the single-duplicate branch of the linter. -/
/--
warning: The namespace `Dup` is duplicated in the declaration `IrisTest.Dup.Dup.foo`.
-/
#guard_msgs (whitespace := lax, substring := true) in
theorem Dup.foo : True := trivial

end Dup

namespace Alpha
namespace Beta

/- Tests the duplicate sequences of namespaces. -/
/--
warning: The namespaces `Alpha` and `Beta` are duplicated in the declaration
`IrisTest.Alpha.Beta.Alpha.Beta.foo`.
-/
#guard_msgs (whitespace := lax, substring := true) in
theorem Alpha.Beta.foo : True := trivial

end Beta
end Alpha

/-! ## `linter.iris.style.whitespace` -/

/- Tests missing spaces. -/
/--
warning: missing space in the source

This part of the code
  '(a: Nat)'
should be written as
  '(a : Nat)'
-/
#guard_msgs (whitespace := lax, substring := true) in
example (a: Nat) : a = a := rfl

/- Tests extra spaces. -/
/--
warning: extra space in the source

This part of the code
  'Nat ) :'
should be written as
  'Nat) : a'
-/
#guard_msgs (whitespace := lax, substring := true) in
example (a : Nat ) : a = a := rfl

/- Tests incorrect indentation. -/
/--
warning: 'example : True := trivial' starts on column 2, but all commands should start at the
beginning of the line.
-/
#guard_msgs (whitespace := lax, substring := true) in
set_option linter.iris.style.whitespace true in
  example : True := trivial

end IrisTest
