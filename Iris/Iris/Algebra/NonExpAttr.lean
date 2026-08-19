/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.Init

public section

namespace Iris.Std
open Lean Meta

meta initialize nonexpExt :
    SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := λ arr n => arr.push n
    initial := #[]
  }

meta initialize registerBuiltinAttribute {
  name := `non_exp
  descr := "Non-expansiveness lemmas to be used by the non-expansiveness and contractiveness solvers"
  add := λ decl _ kind => nonexpExt.add decl kind
}
