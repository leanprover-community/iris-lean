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
Environment extension holding the `@[ne_congr]` lemmas, keyed by their conclusion.
Each entry also carries the rule's priority, used by `solve_ne` to order the lemmas.
-/
initialize neCongrExt :
    SimpleScopedEnvExtension (Array DiscrTree.Key × Name × Nat) (DiscrTree (Name × Nat)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (keys, n, prio) => dt.insertKeyValue keys (n, prio)
    initial := {}
  }

syntax (name := ne_congr) "ne_congr" (prio)? : attr

/--
Congruence lemma for the `solve_ne` tactic.

A `@[ne_congr]` lemma must have a conclusion of the form `a ≡{n}≡ b`. The `solve_ne`
tactic applies such lemmas to distance goals, introduces any binders of the resulting
subgoals (e.g. the pointwise `∀ a, Φ a ≡{n}≡ Ψ a` hypotheses of `forall_ne`), and
recursively solves them. Use this attribute for congruence lemmas that cannot be
expressed as `NonExpansive`/`NonExpansive₂` instances, such as congruence for binders.

An optional priority may be given, e.g. `@[ne_congr 500]`; lemmas are tried from highest
to lowest priority (default `1000`), matching the convention of `@[ext]`/`@[simp]`.
-/
initialize registerBuiltinAttribute {
  name := `ne_congr
  descr := "congruence lemma for the solve_ne tactic"
  add := fun declName stx kind => MetaM.run' <| Lean.Elab.Term.TermElabM.run' do
    let `(attr| ne_congr $[$prio?:prio]?) := stx
      | throwError "invalid `[ne_congr]` attribute syntax"
    let info ← getConstInfo declName
    let (_, _, concl) ← withTransparency TransparencyMode.reducible <| forallMetaTelescopeReducing info.type
    let keys ← DiscrTree.mkPath concl
    let prio ← Lean.Elab.liftMacroM <| evalOptPrio prio?
    neCongrExt.add (keys, declName, prio) kind
}

/-- Return the `@[ne_congr]` lemmas whose conclusion may match the distance goal `e`,
ordered from highest to lowest priority. -/
def getNeCongrLemmas (e : Expr) : MetaM (Array Name) := do
  let arr ← (neCongrExt.getState (← getEnv)).getMatch e
  -- stable sort, so equal-priority lemmas keep their discr-tree order
  return arr.insertionSort (·.2 < ·.2) |>.reverse |>.map (·.1)

end Iris.NeCongr
