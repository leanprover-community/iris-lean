Lean 4 port of *Iris*, a higher-order concurrent separation logic framework.

- [About Iris](#about-iris)
- [Project](#project)
  - [Usage](#usage)
  - [Structure](#structure)
  - [Tactics](#tactics)
  - [Type Classes](#type-classes)
  - [Proofs](#proofs)
- [Development](#development)
- [Miscellaneous](#miscellaneous)
  - [Unicode Input](#unicode-input)
  - [References](#references)

# About Iris

"Iris is a framework that can be used for reasoning about safety of concurrent programs, as the logic in logical relations, to reason about type-systems, data-abstraction etc."<br>
– https://iris-project.org/

Coq formalization of Iris: https://gitlab.mpi-sws.org/iris/iris/

# Project

In its current stage, the scope of this project is to provide a framework to support proofs in different separation logics. This is achieved by porting *MoSeL*, which is the proof interface of Iris. Although Iris provides a complex separation logic itself, MoSeL (in contrast to the older IPM) supports different separation logics as well. The logic of Iris could be ported in a later stage, but there are some open problems that need to be solved first.

## Usage

There are three steps to using the provided separation logic framework.

1. Instantiate the separation logic interface for a separation logic.
2. Define additional notation for the separation logic *(optional)*.
3. Instantiate existing typeclasses for custom constructs *(optional)*.
4. Write proofs using the provided separation logic tactics.

### 1. Instantiating the Separation Logic Interface

The separation logic interface consists of two typeclasses: `BIBase` and `BI`. The typeclass `BIBase` expects the definitions of all required separation logic operators (e.g. entailment, conjunction, separating conjunction). Instantiating the extending typeclass `BI` requires proofs of the listed separation logic axioms. In order to use the separation logic framework (including the tactics), instances of both typeclasses need to be provided. Since the typeclass `BI` extends the typeclass `BIBase`, it is also possible to instantiate only `BI` and provide the operators and axioms together.

Example: Instances of `BIBase` and `BI` for classical separation logic
```lean
instance : BIBase (HeapProp Val) where
  entails P Q := ∀ σ, P σ → Q σ
  emp         := fun σ => σ = ∅
  and P Q     := fun σ => P σ ∧ Q σ
  sep P Q     := fun σ => ∃ σ1 σ2 , σ = σ1 ∪ σ2 ∧ σ1 || σ2 ∧ P σ1 ∧ Q σ2
  ...

instance : BI (HeapProp Val) where
  entailsPreOrder := { ... }
  and_elim_l      := by ...
  and_elim_r      := by ...
  and_intro       := by ...
  ...
```

### 2. Adding Custom Notation

Depending on the separation logic, additional notation can be helpful to write separation logic statements. Custom notation can be added easily and used alongside the predefined syntax.

The syntax and the interpretation of the custom notation must be defined separately. The syntax of the notation is created as usual using the command `syntax`. Both, the arguments and the resulting syntax, should be placed in the syntax category `term`. The interpretation of the new syntax is then defined using the command `macro_rules`. Note that the interpretation of separation logic syntax is only defined inside `iprop` quotations to distinguish it from the syntax of Lean propositions. The left and right side of the `macro_rules` command must therefore include `iprop` quotations around every separation logic proposition.

Example:
```lean
syntax term " ~ " term : term
macro_rules
  | `(`[iprop| $P ~ $Q]) => `(foo `[iprop| $P] `[iprop| $Q])
```

The macro `delab_rule` can be used to provide delaborators for functions with a custom notation. The syntax `$_` in the example below is used in place of the function name, since the delaborator can be applied on function applications where the function names have different scopes. The call to `unpackIprop` is necessary since `P` and `Q` on the left side of `=>` might be wrapped in an `iprop` quotation, which is not required on the right side (since the entire separation logic proposition is wrapped in an `iprop` quotation) and should therefore not be printed.

Example:
```lean
delab_rule BIBase.and
  | `($_ $P $Q) => do ``(`[iprop| $(← unpackIprop P) ∧ $(← unpackIprop Q)])
```

### 3. Instantiating Existing Typeclasses

The separation logic framework contains a number of typeclasses used to require properties of separation logic propositions and connectives. For custom separation logic constructs, instances of these typeclasses can be provided to make their properties available inside the framework. Note that single separation logic propositions must be wrapped inside `iprop` quotations as shown below.

Example:
```lean
-- Every proposition with the modality `<foo>` is affine.
instance fooAffine [BI PROP] (P : PROP) :
  Affine `[iprop| <foo> P] →
where
  persistent := by ...
```

There are also typeclasses that can be instantiated for an entire separation logic. The proven properties of the logic are then automatically available in all proofs of statements in this separation logic.

Example:
```lean
instance (Val : Type) : BIAffine (AffineHeapProp Val) where
  affine P := { ... }
```

### 4. Writing Separation Logic Proofs

Writing a separation logic proofs starts with an ordinary `theorem`, except that the statement to prove is a separation logic proposition `P ⊢ Q` or `P ⊣⊢ Q` where `P` and `Q` are separation logic propositions. It is not necessary to use `iprop` quotations for the propositions here. Separation logic proofs are performed in the *Iris Proof Mode*, which is enabled by the tactic `istart`. When the proof mode is enabled, two additional contexts appear in the Lean tactic state display beneath the Lean context. It is often not necessary to explicitely write the call to `istart`, as it is automatically called by most separation logic tactics. Inside the proof mode, the other separation logic tactics (e.g. `iintro`) can be used to complete the proof. The tactic names follow the Lean conventions and start with an `i` to distinguish them from the exisiting Lean tactics.

Example: Proof of a separation logic statement for all separation logics `PROP`
```lean
theorem proof_example [BI PROP] (P Q R : PROP) (Φ : α → PROP) :
  P ∗ Q ∗ □ R ⊢ □ (R -∗ ∃ x, Φ x) -∗ ∃ x, Φ x ∗ P ∗ Q
:= by
  iintro ⟨HP, HQ, □HR⟩ □HRΦ
  ispecialize HRΦ HR as HΦ
  icases HΦ with ⟨x, HΦ⟩
  iexists x
  isplit r
  · iassumption
  isplit l [HP]
  · iexact HP
  · iexact HQ
```

Example: Tactic state display with the additional intuitionistic (`□`) and spatial (`∗`) contexts
```lean
PROP α : Type
P Q R : PROP
Φ : α → PROP
x : α
⊢ Iris Proof Mode
─────────────────────────────────────
HR : R
HRΦ : R -∗ ∃ x, Φ x
HΦ : Φ x
───────────────────────────────────── □
HP : P
HQ : Q
───────────────────────────────────── ∗
∃ x, Φ x ∗ P ∗ Q
```

## Structure

The structure of the project mostly follows the implementation of MoSeL. The main part of the implementation resides in `src/Iris/`. The subdirectories are described in the following table.

| Directory              | Description |
|------------------------|-------------|
| `BI/`                  | Logic interface: `Interface.lean`, `Extensions.lean`, `Classes.lean`<br>Notation: `Interface.lean`, `DerivedConnectives.lean`, `BigOp.lean`<br>Derived laws: `DerivedLaws.lean`, `Instances.lean` |
| `Examples/`            | Examples of proofs and partial instances of the logic interface. |
| `Instances/`           | Instances of the logic interface for different separation logics. |
| `Instances/Classical/` | Instance for classical (non-affine) separation logic. |
| `Instances/Data/`      | Data structures shared by different logic instances. |
| `Proofmode/`           | *Proof interface*<br>Tactics: `Tactics.lean`, `Theorems.lean`<br>Type classes: `Classes.lean`, `Instances.lean`<br>Separation logic context definition: `Environments.lean`, `Display.lean` |
| `Proofmode/Patterns/`  | Syntax of patterns used in tactic arguments. |
| `Proofmode/Tactics/`   | Implementation of more complex tactics. |
| `Std/`                 | Standard functionality currently missing from Lean. |
| `Tests/`               | Tests for various parts of the proof framework. |

## Tactics

The tactics are implemented in `Tactics.lean` as functions in the `TacticM` monad using the `elab` macro as usual. The monadic functions take care of processing the argument syntax and manipulating the Lean goals. The separation logic goal and contexts, however, are accessed using the tactic theorems in `Theorems.lean`. Besides having proof that the changes are valid, this allows verifying the resulting separation logic proofs within Lean's kernel.

Since the separation logic context types `Envs` and `Env` (defined in `Environments.lean`) reference hypothesis in the context using `Fin` indices (as `EnvsIndex`), the monadic tactic functions have to translate the user names of the hypotheses to indices. This is usually done using the function `findHypothesis?` and requires parsing `Expr`s manually. Helpful functions for this are located in `Proofmode/Expr.lean` and `Std/Expr.lean`.

The monadic tactic functions use the tactic theorems to modify the separation logic goal and contexts. The theorems are applied using the tactic `refine` inside `evalTactic`. The pattern `first | ... | fail` is used to catch typeclass exceptions.

Example:
```lean
elab "iclear" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId

  -- find hypothesis index
  let some hypIndex ← findHypothesis? name
    | throwError "unknown hypothesis"

  -- clear hypothesis
  try evalTactic (← `(tactic|
    first
    | refine tac_clear $(← hypIndex.quoteAsEnvsIndex) _ ?_
    | fail
  ))
  catch _ => throwError "failed to clear the hypothesis"
```

The tactic theorems justify the modification to the separation logic goal and contexts. They are formulated as implications between the embeddings of a separation logic context and a goal. The embedding of a separation logic context and a goal is defined in the function `envs_entails`. The theorems use typeclasses to require specific properties of separation logic propositions. Most of the used typeclasses also support destructing the given separation logic proposition using `outParam`s (e.g. returning the premise and conclusion of an implication).

Example:
```lean
theorem tac_wand_intro [BI PROP] {Δ : Envs PROP} {P Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  envs_entails (Δ.append false P) Q →
  envs_entails Δ R
```

## Type Classes

The separation logic framework uses a complex system of typeclasses to require that a separation logic, proposition or connective possesses certain properties. The relevant typeclasses usually contain a single field of the type `Prop`, which requires a proof of the specified property when the typeclass is instantiated. The typeclasses in `Proofmode/Classes.lean` in addition support destructing separation logic propositions, e.g., returning the premise and conclusion of an implication when a typeclass instance is required. This is done using `outParam`s, which are parameters that are not required to start the typeclass instance search, but determined by the found instance.

This separation logic framework comes with default instances for many separation logic propositions and users can easily extend them with instances for custom separation logic constructs. Some typeclasses come in different versions indicating the directory of the required entailment, e.g. `FromImpl` requires that a separation logic propositions `P` must be deductable *from* an implication `Q1 → Q2`. Other typeclasses require instance priorities in order to fulfill the intended purpose (e.g. `FromAssumption`). This is a common source of failure and must be tuned carefully.

Example:
```
class FromImpl [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_impl : (Q1 → Q2) ⊢ P

instance fromImplImpl [BI PROP] (P1 P2 : PROP) :
  FromImpl `[iprop| P1 → P2] P1 P2
where
  from_impl := by ...
```

## Proofs

The project contains proofs wherever necessary. This includes proofs for the derived laws, the propositions in typeclass instances, the tactic theorems and the soundness of context/environment operations. These proofs are not performed using the provided separation logic interface, but using standard Lean tactics.

One difficulty in these proofs is rewriting. There are two main relations with which rewriting is necessary: entailments `⊢` and bidirectional entailments `⊣⊢`. The bidirectional entailment should represent an equivalence `≡` on separation logic propositions, but since Lean does not support rewriting with equivalences, it is defined as equality `=` instead. This allows using the standard `rw` tactic in the proofs, but forces the user to prove that entailments in both directions are equal to the equality `=` on their separation logic propositions (`equiv_entails` in `BI`), which is not true in general. It can therefore be necessary to use a quotient type with a setoid instance when instantiating the separation logic interface. This is not only more complicated, but limits the interface to logics with a non-parameterized equivalence. This excludes separation logics like Iris, which has an equivalence `={n}=` from an ordered family of equivalences (OFE). The current approach should therefore be changed to use an actual equivalence in the definition of `⊣⊢` as soon as Lean supports *generalized rewriting*.

Example:
```lean
instance myPropSetoid : Setoid MyProp where
  r P Q := ...
  iseqv := { ... }

instance : BI (Quotient myPropSetoid) where
  ...
```

A generalized rewriting approach is also necessary for the entailment relation (similar to rewriting with an implication). Since there was no workaround for rewriting with entailments, this project includes the tactic `rw'` for rewriting with a preorder and monotone rewrite rules. For an entailment with instances of `Reflexive` and `Transitive`, theorems can be annotated with `@[rwMonoRule]` to indicate that the annotated implication can be used to apply a rewrite term (such as a hypothesis in a proof) to one of the arguments of an operator in a proposition. The tactic `rw'` simplifies the problem by assuming that at most one rewrite rule is applicable for each operator, so backtracking is not required.

Example:
```lean
@[rwMonoRule]
theorem and_mono [BI PROP] {P P' Q Q' : PROP} : (P ⊢ Q) → (P' ⊢ Q') → P ∧ P' ⊢ Q ∧ Q' := by
  ...

theorem rw_example [BI PROP] (P R : PROP) (h : P ⊢ R) :
  P ∧ Q ⊢ R ∧ Q
:= by
  rw' [h]
  done
```

# Development

This project started as part of my master's thesis at Karlsruhe Institute of Technology (KIT). Since I finished my studies in October 2022, I will now gladly accept pull requests that will improve and continue the project. If you want to contribute, please match the available code style and add documentation to the code, commits and PRs.

# Miscellaneous

## Unicode Input

Most of the unicode characters used in Iris can be written with the Lean extension replacement, e.g. `\ast` will automatically be replaced with `∗`. To add additional replacements, edit the Lean extension setting `lean4.input.customTranslations`. Suggested additional replacements are listed below.

```json
"sep": "∗",
"wand": "-∗",
"pure": "⌜⌝",
"bientails": "⊣⊢"
```

## References

- [koenig22](https://pp.ipd.kit.edu/uploads/publikationen/koenig22masterarbeit.pdf), Master Thesis, *An Improved Interface for Interactive Proofs in Separation Logic*, 2022-10, Lars König, KIT.
