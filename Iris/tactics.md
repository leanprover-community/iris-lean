# Tactics

The proof mode maintains three contexts: the *pure* (Lean) context, the *intuitionistic* context (hypotheses prefixed with `□`, usable multiple times), and the *spatial* context (hypotheses that are owned and can be used only once).

## Proof Mode Management

- `istart` — Start the proof mode. (Most tactics start the proof mode automatically.)
- `istop` — Stop the proof mode, turning the goal back into a plain entailment.

## Context Management

- `irename` *H* `=>` *H'* — Rename the hypothesis *H* to *H'*.
- `irename :` *term* `=>` *H'* — Rename the hypothesis whose statement matches *term* to *H'*.
- `iclear` [*selPats*](#selection-patterns) — Discard the hypotheses selected by [*selPats*](#selection-patterns).
- `irevert` [*selPats*](#selection-patterns) — Revert the selected hypotheses (proof mode or pure Lean hypotheses) into the goal. An Iris hypothesis *H* in *selPats* is reverted as a wand premise. If a pure hypothesis *H* in *selPats* has a type `φ` such that `φ : Prop`, then *H* is reverted as a premise. If *x* in *selPats* has a type `α` such that `α` is non-`Prop`, then *x* is reverted as a universally quantified variable. For every hypothesis *H* being reverted, all hypotheses dependent on *H* must also be reverted.
- `irevert!` [*selPats*](#selection-patterns) — similar to `irevert` [*selPats*](#selection-patterns), except that for every hypothesis in *selPats*, hypotheses dependent on *H* are also implicitly reverted.
- `ipure` *H* — Move the pure hypothesis *H* into the Lean context.
- `iintuitionistic` *H* — Move *H* to the intuitionistic context. Equivalent to `icases H with #H`.
- `ispatial` *H* — Move *H* to the spatial context. Equivalent to `icases H with ∗H`.

## Introduction and Destruction

- `iintro` [*introPats*](#intro-patterns) — Introduce universal quantifiers, wands and implications using [*introPats*](#intro-patterns).
- `icases` [*pmTerm*](#proof-mode-terms) `with` [*casesPat*](#cases-patterns) — Destruct [*pmTerm*](#proof-mode-terms) using [*casesPat*](#cases-patterns), consuming the hypothesis.
- `icases +keep` [*pmTerm*](#proof-mode-terms) `with` [*casesPat*](#cases-patterns) — Like `icases`, but keep the original hypothesis (requires it to be intuitionistic or duplicable).
- `ihave` [*casesPat*](#cases-patterns) `:=` [*pmTerm*](#proof-mode-terms) — Bring [*pmTerm*](#proof-mode-terms) (e.g. a Lean lemma or specialized hypothesis) into the context and destruct it with [*casesPat*](#cases-patterns) without consuming the original. Equivalent to `icases +keep`.
- `ihave` [*casesPat*](#cases-patterns) `:` *term* `$$` [*specPat*](#specialization-patterns) — Assert the proposition *term*, prove it in a subgoal built from [*specPat*](#specialization-patterns), and destruct it with [*casesPat*](#cases-patterns).
- `iexists` *x₁*`,` ...`,` *xₙ* — Instantiate existential quantifiers in the goal with the terms *xᵢ*. Holes (`_`) and named metavariables (`?m`) are allowed.
- `ileft` / `iright` — Choose the left/right side of a disjunction in the goal.

## Splitting and Framing

- `isplit` — Turns the goal into a conjunction (`∧`) and splits it into two goals, both keeping the entire context.
- `isplitl [`*H₁* ... *Hₙ*`]` — Split a separating conjunction (`∗`); the hypotheses *Hᵢ* go to the left goal, all remaining spatial hypotheses to the right.
- `isplitr [`*H₁* ... *Hₙ*`]` — Like `isplitl`, but the listed hypotheses go to the right goal.
- `isplitl` / `isplitr` — Split a separating conjunction, giving *all* spatial hypotheses to the left (`isplitl`) or right (`isplitr`) goal.
- `iframe` [*selPats*](#selection-patterns) — Cancel the selected hypotheses against matching parts of the goal. Solves the goal completely if the leftover is `True` or `emp` (with affine context).
- `iframe` — Equivalent to `iframe ∗` (frame all spatial hypotheses).
- `icombine` [*selPats*](#selection-patterns) `as` [*casesPat*](#cases-patterns) — Combine the selected hypotheses into one using the `CombineSepAs` type class (defaults to `∗`) and destruct the result with [*casesPat*](#cases-patterns).
- `icombine` [*selPats*](#selection-patterns) `gives` [*casesPat*](#cases-patterns) — Derive persistent information (e.g. validity of combined ghost state) from the selected hypotheses via `CombineSepGives`, keeping the originals.
- `icombine` [*selPats*](#selection-patterns) `as` *pat₁* `gives` *pat₂* — Do both at once.

## Applying and Specializing

- `iapply` [*pmTerm*](#proof-mode-terms) — Apply the conclusion of [*pmTerm*](#proof-mode-terms) to the goal.
- `ispecialize` [*pmTerm*](#proof-mode-terms) — Specialize a hypothesis according to [*pmTerm*](#proof-mode-terms).
- `iexact` *H* — Solve the goal with the hypothesis *H*.
- `iassumption` — Solve the goal with a matching hypothesis from the intuitionistic or spatial context.

## Modalities

- `imodintro` — Introduce the modality at the top of the goal (e.g. `□`, `<pers>`, `▷`, `|==>`), adjusting the context as required by the modality.
- `imodintro` *sel* — Like `imodintro`, but only succeed if the modality matches the selector term *sel*, e.g. `imodintro (<pers> _)` or `imodintro (□ _)`.
- `inext` — Introduce one or more later modalities; equivalent to `imodintro (▷^[_] _)`.
- `imod` [*pmTerm*](#proof-mode-terms) `with` [*casesPat*](#cases-patterns) — Eliminate the modality at the top of [*pmTerm*](#proof-mode-terms) into the goal and destruct the result with [*casesPat*](#cases-patterns). Equivalent to `icases ... with >pat`.
- `imod` [*pmTerm*](#proof-mode-terms) — Like above; if [*pmTerm*](#proof-mode-terms) is a hypothesis, its name is kept.

## Rewriting and Induction

- `irewrite [`*rules*`]` (`at` *H* | `at ⊢`)? — Rewrite with internal equalities (`≡`). Each rule is a [*pmTerm*](#proof-mode-terms), optionally prefixed with `←` for right-to-left rewriting. Rewrites in the goal by default or in hypothesis *H*. Supports `(occs := ...)` config. Example: `irewrite [← Heq $$ %b] at H`.
- `iloeb as` *IH* (`generalizing` [*selPats*](#selection-patterns))? — Löb induction: adds the induction hypothesis *IH* (guarded by `▷`) to the intuitionistic context. All spatial hypotheses — plus anything selected by [*selPats*](#selection-patterns), including pure variables via `%x` — are generalized into the induction hypothesis. For every hypothesis *H* in *selPats*, all hypotheses dependent on *H* must also be included in *selPats*.
- `iloeb as` *IH* `generalizing!` [*selPats*](#selection-patterns) — same as `iloeb as` *IH* `generalizing` [*selPats*](#selection-patterns), except that for every hypothesis *H* in [*selPats*](#selection-patterns), all hypotheses dependent on *H* are implicitly also generalised.
- `iinduction` *e* (`using` *r*)? (`generalizing` [*selPats*](#selection-patterns))? (`with` (*tac*)? `|` *constr₁* `=>` *tac₁* `|` ... `|` *constrₙ* `=>` *tacₙ*)? — All spatial hypotheses, as well as hypotheses dependent on *e*, are generalised and included as premises in the induction hypotheses. Furthermore, generalise the hypotheses specified by [*selPats*](#selection-patterns). For every hypothesis *H* in [*selPats*](#selection-patterns), all hypotheses dependent on *H* must also be included in [*selPats*](#selection-patterns). The induction principle is determined by the recursor name *r*, if given, or otherwise the default induction principle is chosen. The `with` clause enables alternative names to be given to variables and induction hypotheses. Each of *constr₁*, ..., *constrₙ* is the constructor name followed by the alternative names. Each of *tac₁*, ..., *tacₙ* is either a tactic sequence for the induction subgoal or a hole (`_` or `?_`); the latter defers the induction subgoal. A tactic *tac* is optionally given in the `with` clause, which is the first tactic applied to all induction subgoals.
- `iinduction` *e* (`using` *r*)? `generalizing!` [*selPats*](#selection-patterns) (`with` (*tac*)? `|` *constr₁* `=>` *tac₁* `|` ... `|` *constrₙ* `=>` *tacₙ*)? — Same as above, except that for every hypothesis *H* in *selPats*, hypotheses dependent on *H* are implicitly generalised.

## Solving Simple Goals

- `ipureintro` — Turn a goal of the form `⌜φ⌝` into the Lean goal `φ`.
- `iempintro` — Solve an `emp` goal, requiring the spatial context to be affine.
- `iexfalso` — Change the goal to `False`.
- `itrivial` — Try to solve the goal with simple tactics (`iassumption`, `ipureintro` followed by `simp`/`assumption`, ...). Used by the `//` patterns. Extensible by adding `macro_rules` for `itrivial`.

## Cases Patterns

- *name* / `_` — Name the hypothesis *name* (or keep it anonymous).
- `-` — Drop the hypothesis.
- `$` — Frame the hypothesis: immediately cancel it against the goal (like `iframe`).
- `⟨`*pat₁*`,` ... `,` *patₙ*`⟩` — Destruct a (separating) conjunction or existential; an existential variable is bound with `%`*x*, e.g. `⟨%x, H⟩`.
- `(`*pat₁* `|` ... `|` *patₙ*`)` — Destruct a disjunction, one goal per disjunct. Parentheses can be omitted when nested inside `⟨⟩`.
- `%`*name* — Move the (pure) hypothesis into the Lean context as *name*.
- `#`*pat* — Move the hypothesis to the intuitionistic context, then destruct with *pat*.
- `∗`*pat* — Move the hypothesis to the spatial context, then destruct with *pat*.
- `>`*pat* — Eliminate the modality at the top of the hypothesis, then destruct with *pat*.

Example:
```lean
-- the hypothesis:
∃ x, P1 x ∗ (□ P2 ∨ P2) ∗ (P3 ∧ ⌜φ⌝)
-- can be destructed using the pattern:
⟨%x, HP1, #HP2 | HP2, ⟨HP3, -⟩⟩
```

## Intro Patterns

- [*casesPat*](#cases-patterns) — Introduce a hypothesis and destruct it with [*casesPat*](#cases-patterns). In particular, `%x` introduces a universally quantified variable or pure premise into the Lean context.
- `!>` — Introduce the modality at the top of the goal (like `imodintro`).
- `//` — Try to close the goal with `itrivial` (and continue with the remaining patterns if it fails).

Example: `iintro %x ⟨HP, #HQ⟩ !> //`.

## Selection Patterns

- *H* — The proof mode hypothesis *H*.
- `%`*h* — The Lean hypothesis *h* from the pure context.
- `%` — All pure (`Prop`) hypotheses in the Lean context.
- `#` — All hypotheses in the intuitionistic context.
- `∗` — All hypotheses in the spatial context.

## Specialization Patterns

Used in [proof mode terms](#proof-mode-terms) after `$$` to eliminate the premises of a wand or universal quantifier.

- *H* — Use the hypothesis *H*, which must match the premise exactly.
- `%`*t* — Instantiate a universal quantifier with the pure term *t*.
- `[`*H₁* ... *Hₙ*`]` — Generate a subgoal for the premise with exactly the spatial hypotheses *Hᵢ*. Hypotheses written as `$H` are framed instead of forming the context.
- `[-` *H₁* ... *Hₙ*`]` — Like above, but use all spatial hypotheses *except* the listed ones.
- `[`... `//]` — Additionally try to solve the subgoal with `itrivial` and fail if unsuccessful.
- `[`...`] as` *name* — Name the generated subgoal *name*.
- `[$]` — Solve the premise entirely by framing spatial and intuitionistic hypotheses.

If the conclusion of a specialization is persistent, the context can be shared between the subgoal and the main goal (e.g. `ihave #HQ : □ Q $$ [HP]` keeps `HP` usable in the main goal).

## Proof Mode Terms

Proof mode terms (*pmTerm*) are of the form
```
H $$ specPat₁ ... specPatₙ
```
where `H` is a hypothesis or a Lean term whose conclusion is an entailment, and the *specPatᵢ* are [specialization patterns](#specialization-patterns) applied to its premises. The `$$ ...` part is optional. Examples:

```lean
iapply (wand_trans HPQ)        -- Lean term as pmTerm
ispecialize HPQ $$ %x HP [HQ]  -- instantiate ∀ with x, use HP, prove premise from HQ
imod (own_update ... $$ Hown)  -- specialize and eliminate the update modality
```
