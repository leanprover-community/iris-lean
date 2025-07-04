# Tactics

| Syntax                                 | Description                                                  |
| -------------------------------------- | ------------------------------------------------------------ |
| `istart`                               | Start the proof mode.                                        |
| `istop`                                | Stop the proof mode.                                         |
| `irename` *nameFrom* `into` *nameTo*   | Rename the hypothesis *nameFrom* to *nameTo*.                |
| `iclear` *hyp*                         | Discard the hypothesis *hyp*.                                |
| `iexists` *x*                          | Resolve an existential quantifier in the goal by introducing the variable *x*. |
| `iexact` *hyp*                         | Solve the goal with the hypothesis *hyp*.                    |
| `iassumption_lean`                     | Solve the goal with a hypothesis of the type `⊢ Q` from the Lean context. |
| `iassumption`                          | Solve the goal with a hypothesis from any context (pure, intuitionistic or spatial). |
| `iex_falso`                            | Change the goal to `False`.                                  |
| `ipure` *hyp*                          | Move the hypothesis *hyp* to the pure context.               |
| `iintuitionistic` *hyp*                | Move the hypothesis *hyp* to the intuitionistic context.     |
| `ispatial` *hyp*                       | Move the hypothesis *hyp* to the spatial context.            |
| `iemp_intro`                           | Solve the goal if it is `emp` and discard all hypotheses.    |
| `ipure_intro`                          | Turn a goal of the form `⌜φ⌝` into a Lean goal `φ`.          |
| `ispecialize` *hyp* *args* `as` *name* | Specialize the wand or universal quantifier *hyp* with the hypotheses and variables *args* and assign the name *name* to the resulting hypothesis. |
| `isplit`                               | Split a conjunction (e.g. `∧`) into two goals, using the entire spatial context for both of them. |
| `isplit` {`l`\|`r`}                    | Split a separating conjunction (e.g. `∗`) into two goals, using the entire spatial context for the left (`l`) or right (`r`) side. |
| `isplit` {`l`\|`r`} `[`*hyps*`]`       | Split a separating conjunction (e.g. `∗`) into two goals, using the hypotheses *hyps* as the spatial context for the left (`l`) or right (`r`) side. The remaining hypotheses in the spatial context are used for the opposite side. |
| `ileft`<br>`iright`                    | Choose to prove the left (`ileft`) or right (`iright`) side of a disjunction in the goal. |
| `icases` *hyp* `with` *cases-pat*      | Destruct the hypothesis *hyp* using the cases pattern *cases-pat*. |
| `iintro` *cases-pats*                  | Introduce up to multiple hypotheses and destruct them using the cases patterns *cases-pats*. |
| `irevert` *hyp*                        | Revert the hypothesis *hyp*.                                 |

## Cases Patterns

| Pattern                         | Description                                                                                                                                                                         |
|---------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| *name*                          | Rename the hypothesis to *name*.                                                                                                                                                    |
| `_`                             | Drop the hypothesis.                                                                                                                                                                |
| `⟨`*pat_1* [`,` *pat_2*]...`⟩`  | Destruct a (separating) conjunction and recursively destruct its arguments using the patterns *pat_i*.                                                                              |
| `(`*pat_1* [`\|` *pat_2*]...`)` | Destruct a disjunction and recursively destruct its arguments in separate goals using the patterns *pat_i*. The parentheses can be omitted if this pattern is not on the top level. |
| `⌜`*name*`⌝`                    | Move the hypothesis to the pure context and rename it to *name*.                                                                                                                    |
| `□` *pat*                       | Move the hypothesis to the intuitionistic context and further destruct it using the pattern *pat*.                                                                                  |
| `-□` *pat*                      | Move the hypothesis to the spatial context and further destruct it using the pattern *pat*.                                                                                         |

Example:
```lean
-- the hypothesis:
P1 ∗ (□ P2 ∨ P2) ∗ (P3 ∧ P3')
-- can be destructed using the pattern:
⟨HP1, □HP2 | HP2, ⟨HP3, _⟩⟩
-- (there are of course other valid patterns for destructing the shown hypothesis)
```
