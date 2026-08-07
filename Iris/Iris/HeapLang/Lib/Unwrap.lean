/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Lib.Assert

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace Unwrap

/-- `unwrap o` unsafely asserts that `o` is `some v` and returns `v`. The
`none` case is unreachable (it aborts via `assert`). -/
@[rocq_alias heap_lang.unwrap]
def unwrap : Val := hl_val%
  λ o,
    match o with
    | none() => assert(#false)
    | some(v) => v

section Spec

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

@[rocq_alias heap_lang.unwrap_spec]
theorem unwrap_spec (Φ : Val → IProp GF) (v : Val) :
    ▷ Φ v ⊢ WP hl(&unwrap v(some(&v))) {{ Φ }} := by
  iintro HΦ
  wp_lam
  wp_pures
  iapply HΦ

end Spec

end Unwrap
end
