module
public meta import Aesop

declare_aesop_rule_sets [aesop_contractive]

macro (name := aesop_cat) "aesop_contractive" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (config := { introsTransparency? := some .reducible, warnOnNonterminal := false })
            (rule_sets := [$(Lean.mkIdent `aesop_contractive):ident]))

--For some reason, it looks like builting rules cannot be removed from specific rulesets, only from the general aesop ruleset...
erase_aesop_rules [Aesop.BuiltinRules.rfl, Exists]
