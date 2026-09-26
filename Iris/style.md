# Iris-Lean Style Guide

Iris-Lean follows the [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html) and the [Mathlib naming convention](https://leanprover-community.github.io/contribute/naming.html) wherever they apply.

The following are some additional guidelines specific to Iris-Lean, as well as the conventions that are mechanically enforced by the project's linters and scripts.

## File Layout

Every module starts with the following headers:

```lean
/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <comma-separated list of authors>
-/
```

## Naming

### General

Mathlib's conventions mostly apply:

| Kind                       | Convention       | Example                                |
|----------------------------|------------------|----------------------------------------|
| Types, structures, classes | `UpperCamelCase` | `BIAffine`, `CombineSepGives`          |
| Definitions, abbreviations | `lowerCamelCase` | `laterIf`                              |
| Theorems, lemmas           | `snake_case`     | `persistently_sep_mpr`, `wand_entails` |
| Universe variables         | `u`, `v`, ...    |                                        |

* Type class instances are the exception: `lowerCamelCase` with a suffix separated by underscores (e.g. `elimInv_acc_with_close`).
* **No double underscores**: names such as `foo__bar` are rejected by the linter.
* **No repeated namespace components**: fully qualified names such as `Iris.BI.BI.foo` and `Iris.Foo.Bar.Foo.baz` are flagged by the linter.

### Hypothesis Naming

A proof-mode goal carries two contexts at once: the ambient Lean local context, and the Iris hypothesis context managed by IPM.

* **Pure Lean hypotheses are lower-case**: `h`, `h1`, `h2`, `hφ`, `hP`, `hpq`, `hAcc`.
* **Iris hypotheses are capitalised**: `H`, `H1`, `H2`, `HP`, `Hinv`, `Hclose`, `Hα`.

## Correspondence with Iris-Rocq

Every declaration that corresponds to something in Iris-Rocq development should be annotated with `rocq_alias`, and every Rocq declaration that is deliberately *not* ported should be annotated with `rocq_ignore`.

### `@[rocq_alias ...]`

Annotate a new Lean declaration with the name of the Rocq declaration it ports:

```lean
@[rocq_alias BiAffine]
class BIAffine (PROP : Type _) [BI PROP] where
  affine (P : PROP) : Affine P

@[rocq_alias bi.entails_anti_sym]
instance entails_antisymm [BI PROP] : Antisymmetric (α := PROP) BiEntails Entails where
  antisymm h1 h2 := ⟨h1, h2⟩
```

One Lean declaration may subsume several Rocq ones — list each alias separately:

```lean
@[rocq_alias bi, rocq_alias BiMixin,
  rocq_alias BiPersistentlyMixin, rocq_alias BiLaterMixin]
class BI (PROP : Type _) extends COFE PROP, BI.BIBase PROP where
  ...
```

### `#rocq_ignore`

When a Rocq declaration is intentionally not ported, record it with a reason:

```lean
#rocq_ignore bi.entails_proper "Derivable from _ne with NonExpansive.eqv."

#rocq_ignore BiPureForall
  "BIPureForall is provable for all BIs using classical logic, see pure_forall_2"
```

Typical reasons why Rocq declarations are ignored:

* the Rocq mixin records (`BiMixin`, `BiPersistentlyMixin`, `BiLaterMixin`) are collapsed into Lean's type classes;
* the statement is derivable in Lean from a more general result;
* the machinery is superseded by Lean's meta-level elaboration.

### `#rocq_ignore_file`

Files in Iris-Rocq that are deliberately not ported (e.g. Rocq-specific machinery) are ignored using the `#rocq_ignore_file` annotation.

## Module Organisation and Imports

The project is organised so that **every directory `Foo/` is accompanied by a module `Foo.lean` acting as its entry point**: [`Iris/BI/`](./Iris/BI/) by [`Iris/BI.lean`](./Iris/BI.lean), [`Iris/BI/BigOp/`](./Iris/BI/BigOp) by [`Iris/BI/BigOp.lean`](./Iris/BI/BigOp.lean), and so on.

These requirements are enforced by the CI.

### Entry Points

For every directory, the entry-point module must **transitively** import every module in that directory. So a new file [`Iris/ProofMode/Tactics/Frame.lean`](./Iris/ProofMode/Tactics/Frame.lean) must be reachable from [`Iris/ProofMode/Tactics.lean`](./Iris/ProofMode/Tactics.lean), which must in turn be reachable from [`Iris/ProofMode.lean`](./Iris/ProofMode.lean) and from [`Iris.lean`](./Iris.lean).

The exceptions are the `Iris/*/Lib` directories, whose entry points are deliberately not imported by their parent:

* `Iris.Algebra.Lib`
* `Iris.BI.Lib`
* `Iris.HeapLang.Lib`
* `Iris.Instances.Lib`

### `Iris.Init` as the Initial Module

`Iris/Init.lean` collects the imports that set up the library's environment — options, attributes, notation, linters. Every module must import it directly or transitively, so that the environment is the same everywhere. The only exempt modules are those `Init` itself depends on, which cannot import it back without creating a cycle.

Usually nothing needs doing: importing any existing Iris module pulls `Iris.Init` in. A new *leaf* module that imports nothing from the project (only Lean core, Batteries or Qq) must add `import Iris.Init` explicitly.

### Running the check

```bash
lake exe check-imports Iris                      # both checks
lake exe check-imports --entry-points-only Iris  # check entry points only
lake exe check-imports --init-only Iris          # check Iris.Init only
lake exe check-imports --minimal-init Iris       # list the modules where adding the import suffices
```

Exit code `0` means all checks passed, `1` that a check failed, and `2` that the script could not run (for example, a directory with no entry-point file). When the `Iris.Init` check fails, it also prints the minimal set of modules to add `import Iris.Init` to, so start from that list rather than adding the import everywhere.
