/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.Algebra.OFE

public meta section

namespace Iris.NeCongr
open Lean Meta

/--
Environment extension holding the `@[ne_congr]` lemmas, keyed by their conclusion
(an `OFE.Dist` application).
-/
initialize neCongrExt : SimpleScopedEnvExtension (Array DiscrTree.Key × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (keys, n) => dt.insertKeyValue keys n
    initial := {}
  }

syntax (name := ne_congr) "ne_congr" : attr

/--
Congruence lemma for the `solve_ne` tactic.

A `@[ne_congr]` lemma must have a conclusion of the form `a ≡{n}≡ b`. The `solve_ne`
tactic applies such lemmas to distance goals, introduces any binders of the resulting
subgoals (e.g. the pointwise `∀ a, Φ a ≡{n}≡ Ψ a` hypotheses of `forall_ne`), and
recursively solves them. Use this attribute for congruence lemmas that cannot be
expressed as `NonExpansive`/`NonExpansive₂` instances, such as congruence for binders.
-/
initialize registerBuiltinAttribute {
  name := `ne_congr
  descr := "congruence lemma for the solve_ne tactic"
  add := fun declName _stx kind => MetaM.run' do
    let info ← getConstInfo declName
    let (_, _, concl) ← forallMetaTelescopeReducing info.type
    unless concl.isAppOfArity ``OFE.Dist 5 do
      throwError "@[ne_congr]: conclusion of {declName} must be of the form `a ≡\{n}≡ b`"
    let keys ← DiscrTree.mkPath concl
    neCongrExt.add (keys, declName) kind
}

/-- Return the `@[ne_congr]` lemmas whose conclusion may match the distance goal `e`. -/
def getNeCongrLemmas (e : Expr) : MetaM (Array Name) := do
  (neCongrExt.getState (← getEnv)).getMatch e

end Iris.NeCongr
