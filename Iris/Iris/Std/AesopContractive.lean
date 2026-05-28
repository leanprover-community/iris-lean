module
public meta import Aesop

declare_aesop_rule_sets [aesop_contractive]

macro (name := aesop_cat) "aesop_contractive" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (config := { introsTransparency? := some .reducible, warnOnNonterminal := false })
            (rule_sets := [$(Lean.mkIdent `aesop_contractive):ident]))

attribute [simp] Nat.repeat
