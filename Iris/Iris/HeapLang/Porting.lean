/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init

/-!
# HeapLang porting bookkeeping

File-level `#rocq_ignore_file` entries for `iris_heap_lang/`. Per-definition
`@[rocq_alias]` and `#rocq_ignore` entries live next to the declarations they
describe; only whole-file decisions are recorded here.
-/

#rocq_ignore_file heap_lang "pretty.v"
  "Rocq-specific pretty printing; Lean prints HeapLang via the delaborators in Notation.lean"
