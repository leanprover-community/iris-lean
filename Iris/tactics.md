# Tactics

The proof mode maintains three contexts: the *pure* (Lean) context, the *intuitionistic* context (hypotheses prefixed with `□`, usable multiple times), and the *spatial* context (hypotheses that are owned and can be used only once).

## Proof Mode Management

| Syntax   | Description                                                                                  |
|----------|----------------------------------------------------------------------------------------------|
| `istart` | Start the proof mode. (Most tactics start the proof mode automatically.)                     |
| `istop`  | Stop the proof mode, turning the goal back into a plain entailment.                          |

## Context Management

| Syntax                                | Description                                                                                                                                  |
|---------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------|
| `irename` *H* `=>` *H'*               | Rename the hypothesis *H* to *H'*.                                                                                                           |
| `irename :` *term* `=>` *H'*          | Rename the hypothesis whose statement matches *term* to *H'*.                                                                                |
| `iclear` *selPats*                    | Discard the hypotheses selected by the [selection patterns](#selection-patterns) *selPats*.                                                  |
| `irevert` *selPats*                   | Revert the selected hypotheses (proof mode or pure Lean hypotheses) into the goal.                                                           |
| `ipure` *H*                           | Move the pure hypothesis *H* into the Lean context.                                                                                          |
| `iintuitionistic` *H*                 | Move *H* to the intuitionistic context. Equivalent to `icases H with #H`.                                                                    |
| `ispatial` *H*                        | Move *H* to the spatial context. Equivalent to `icases H with ∗H`.                                                                           |

## Introduction and Destruction

| Syntax                                     | Description                                                                                                                                         |
|--------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------|
| `iintro` *intro-pats*                      | Introduce universal quantifiers, wands and implications using the [intro patterns](#intro-patterns) *intro-pats*.                                   |
| `icases` *pmTerm* `with` *cases-pat*       | Destruct *pmTerm* using the [cases pattern](#cases-patterns) *cases-pat*, consuming the hypothesis.                                                 |
| `icases +keep` *pmTerm* `with` *cases-pat* | Like `icases`, but keep the original hypothesis (requires it to be intuitionistic or duplicable).                                                   |
| `ihave` *cases-pat* `:=` *pmTerm*          | Bring *pmTerm* (e.g. a Lean lemma or specialized hypothesis) into the context and destruct it with *cases-pat* without consuming the original. Equivalent to `icases +keep`. |
| `ihave` *cases-pat* `:` *term* `$$` *spec-pats* | Assert the proposition *term*, prove it in a subgoal built from *spec-pats*, and destruct it with *cases-pat*.                                  |
| `iexists` *x₁*`,` ...`,` *xₙ*              | Instantiate existential quantifiers in the goal with the terms *xᵢ*. Holes (`_`) and named metavariables (`?m`) are allowed.                        |
| `ileft` / `iright`                         | Choose the left/right side of a disjunction in the goal.                                                                                            |

## Splitting and Framing

| Syntax                            | Description                                                                                                                                            |
|-----------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------|
| `isplit`                          | Split a conjunction (`∧`) into two goals, both keeping the entire context.                                                                             |
| `isplitl [`*H₁* ... *Hₙ*`]`       | Split a separating conjunction (`∗`); the hypotheses *Hᵢ* go to the left goal, all remaining spatial hypotheses to the right.                          |
| `isplitr [`*H₁* ... *Hₙ*`]`       | Like `isplitl`, but the listed hypotheses go to the right goal.                                                                                        |
| `isplitl` / `isplitr`             | Split a separating conjunction, giving *all* spatial hypotheses to the left (`isplitl`) or right (`isplitr`) goal.                                     |
| `iframe` *selPats*                | Cancel the selected hypotheses against matching parts of the goal. Solves the goal completely if the leftover is `True` or `emp` (with affine context). |
| `iframe`                          | Equivalent to `iframe ∗` (frame all spatial hypotheses).                                       |
| `icombine` *selPats* `as` *cases-pat* | Combine the selected hypotheses into one using the `CombineSepAs` type class (defaults to `∗`) and destruct the result with *cases-pat*.           |
| `icombine` *selPats* `gives` *cases-pat* | Derive persistent information (e.g. validity of combined ghost state) from the selected hypotheses via `CombineSepGives`, keeping the originals. |
| `icombine` *selPats* `as` *pat₁* `gives` *pat₂* | Do both at once.                                                                                                                            |

## Applying and Specializing

| Syntax                  | Description                                                                                                                                                          |
|-------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `iapply` *pmTerm*       | Match the conclusion of *pmTerm* against the goal and generate goals for each premise, moving all unused spatial hypotheses into the last premise.                    |
| `ispecialize` *pmTerm*  | Specialize a hypothesis according to *pmTerm*.                                          |
| `iexact` *H*            | Solve the goal with the hypothesis *H*.                                                                                                                              |
| `iassumption`           | Solve the goal with a matching hypothesis from any context (pure, intuitionistic or spatial).                                                                        |

## Modalities

| Syntax                          | Description                                                                                                                                                    |
|---------------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `imodintro`                     | Introduce the modality at the top of the goal (e.g. `□`, `<pers>`, `▷`, `\|==>`), adjusting the context as required by the modality.                           |
| `imodintro` *sel*               | Like `imodintro`, but only succeed if the modality matches the selector term *sel*, e.g. `imodintro (<pers> _)` or `imodintro (□ _)`.                          |
| `inext`                         | Introduce one or more later modalities; equivalent to `imodintro (▷^[_] _)`.                                                                                   |
| `imod` *pmTerm* `with` *cases-pat* | Eliminate the modality at the top of *pmTerm* into the goal and destruct the result with *cases-pat*. Equivalent to `icases ... with >pat`. |
| `imod` *pmTerm*                 | Like above; if *pmTerm* is a hypothesis, its name is kept.                                                                                                     |

## Rewriting and Induction

| Syntax                                       | Description                                                                                                                                       |
|----------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------|
| `irewrite [`*rules*`]` (`at` *H* \| `at ⊢`)? | Rewrite with internal equalities (`≡`). Each rule is a proof mode term, optionally prefixed with `←` for right-to-left rewriting. Rewrites in the goal by default or in hypothesis *H*. Supports `(occs := ...)` config. Example: `irewrite [← Heq $$ %b] at H`. |
| `iloeb as` *IH* (`generalizing` *selPats*)?  | Löb induction: adds the induction hypothesis *IH* (guarded by `▷`) to the intuitionistic context. All spatial hypotheses — plus anything selected by *selPats*, including pure variables via `%x` — are generalized into the induction hypothesis. |

## Solving Simple Goals

| Syntax       | Description                                                                                                                                                       |
|--------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `ipureintro` | Turn a goal of the form `⌜φ⌝` into the Lean goal `φ`.                                                                                                             |
| `iempintro`  | Solve an `emp` goal, requiring the spatial context to be affine.                                                                                                  |
| `iexfalso`   | Change the goal to `False`.                                                                                                                                       |
| `itrivial`   | Try to solve the goal with simple tactics (`iassumption`, `ipureintro` followed by `simp`/`assumption`, ...). Used by the `//` patterns. Extensible by adding `macro_rules` for `itrivial`. |

## Cases Patterns

| Pattern                         | Description                                                                                                                                                         |
|---------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| *name* / `_`                    | Name the hypothesis *name* (or keep it anonymous).                                                                                                                  |
| `-`                             | Drop the hypothesis.                                                                                                                                                |
| `$`                             | Frame the hypothesis: immediately cancel it against the goal (like `iframe`).                                                                                       |
| `⟨`*pat₁*`,` ... `,` *patₙ*`⟩`  | Destruct a (separating) conjunction or existential; an existential variable is bound with `%`*x*, e.g. `⟨%x, H⟩`.                                                   |
| `(`*pat₁* `\|` ... `\|` *patₙ*`)` | Destruct a disjunction, one goal per disjunct. Parentheses can be omitted when nested inside `⟨⟩`.                                                                |
| `%`*name*                       | Move the (pure) hypothesis into the Lean context as *name*.                                                                                                         |
| `#`*pat*                        | Move the hypothesis to the intuitionistic context, then destruct with *pat*.                                                                                        |
| `∗`*pat*                        | Move the hypothesis to the spatial context, then destruct with *pat*.                                                                                               |
| `>`*pat*                        | Eliminate the modality at the top of the hypothesis, then destruct with *pat*.                                                                                      |

Example:
```lean
-- the hypothesis:
∃ x, P1 x ∗ (□ P2 ∨ P2) ∗ (P3 ∧ ⌜φ⌝)
-- can be destructed using the pattern:
⟨%x, HP1, #HP2 | HP2, ⟨HP3, -⟩⟩
```

## Intro Patterns

| Pattern     | Description                                                                                                       |
|-------------|---------------------------------------------------------------------------------------------------------------------|
| *cases-pat* | Introduce a hypothesis and destruct it with *cases-pat*. In particular, `%x` introduces a universally quantified variable or pure premise into the Lean context. |
| `!>`        | Introduce the modality at the top of the goal (like `imodintro`).                                                 |
| `//`        | Try to close the goal with `itrivial` (and continue with the remaining patterns if it fails).                     |

Example: `iintro %x ⟨HP, #HQ⟩ !> //`.

## Selection Patterns

| Pattern   | Description                                                  |
|-----------|------------------------------------------------------------------|
| *H*       | The proof mode hypothesis *H*.                               |
| `%`*h*    | The Lean hypothesis *h* from the pure context.               |
| `%`       | All pure (`Prop`) hypotheses in the Lean context.            |
| `#`       | All hypotheses in the intuitionistic context.                |
| `∗`       | All hypotheses in the spatial context.                       |

## Specialization Patterns

Used in proof mode terms after `$$` to eliminate the premises of a wand or universal quantifier.

| Pattern                       | Description                                                                                                                                |
|-------------------------------|------------------------------------------------------------------------------------------------------------------------------------------------|
| *H*                           | Use the hypothesis *H*, which must match the premise exactly.                                                                              |
| `%`*t*                        | Instantiate a universal quantifier with the pure term *t*.                                                                                 |
| `[`*H₁* ... *Hₙ*`]`           | Generate a subgoal for the premise with exactly the spatial hypotheses *Hᵢ*. Hypotheses written as `$H` are framed instead of forming the context. |
| `[-` *H₁* ... *Hₙ*`]`         | Like above, but use all spatial hypotheses *except* the listed ones.                                                                       |
| `[`... `//]`                  | Additionally try to solve the subgoal with `itrivial` and fail if unsuccessful.                                                            |
| `[`...`] as` *name*           | Name the generated subgoal *name*.                                                                                                         |
| `[$]`                         | Solve the premise entirely by framing spatial and intuitionistic hypotheses.                                                               |
If the conclusion of a specialization is persistent, the context can be shared between the subgoal and the main goal (e.g. `ihave #HQ : □ Q $$ [HP]` keeps `HP` usable in the main goal).

## Proof Mode Terms

Proof mode terms (*pmTerm*) are of the form
```
H $$ specPat₁ ... specPatₙ
```
where `H` is a hypothesis or a Lean term whose conclusion is an entailment, and the *specPatᵢ* are specialization patterns applied to its premises. The `$$ ...` part is optional. Examples:

```lean
iapply (wand_trans HPQ)        -- Lean term as pmTerm
ispecialize HPQ $$ %x HP [HQ]  -- instantiate ∀ with x, use HP, prove premise from HQ
imod (own_update ... $$ Hown)  -- specialize and eliminate the update modality
```
