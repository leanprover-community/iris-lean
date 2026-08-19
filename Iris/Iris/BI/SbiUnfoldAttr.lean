/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Init
public meta import Lean.Elab.Tactic.Simp

/-!
# The `sbi_norm` and `sbi_model` simp sets

`sbi_norm` puts a plain SBI goal into its step-indexed normal form. `sbi_model`
holds the single rule that writes a down closure out as `∀ m ≤ n, _`. They are
separate sets because the second erases the pattern the first matches on; see
`Iris.BI.SbiUnfold`.
-/

namespace Iris

register_simp_attr sbi_norm
register_simp_attr sbi_model

end Iris
