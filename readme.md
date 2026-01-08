# Verified-zkEVM Fork of Iris

This is a fork of [iris-lean](https://github.com/iris-project/iris-lean), a higher-order concurrent separation logic framework. We plan to develop the [Bluebell](https://arxiv.org/pdf/2402.18708) program logic on top of Iris. This repo adds mathlib as a dependency for probability theory and other math prerequisites. **Please note that this is under active development and the contents of src/Bluebell should not be considered stable for now**.

- [Verified-zkEVM Fork of Iris](#verified-zkevm-fork-of-iris)
- [About Iris](#about-iris)
- [Project](#project)
  - [Usage](#usage)
    - [1. Instantiating the Separation Logic Interface](#1-instantiating-the-separation-logic-interface)
    - [2. Adding Custom Notation](#2-adding-custom-notation)
    - [3. Instantiating Existing Typeclasses](#3-instantiating-existing-typeclasses)
    - [4. Writing Separation Logic Proofs](#4-writing-separation-logic-proofs)
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

Rocq formalization of Iris: https://gitlab.mpi-sws.org/iris/iris/

# Project

Currently, Iris-Lean has support for 
- *MoSeL*, the proof interface of Iris
- `UPred`, the Iris base logic
- A selection of the Iris resources

MoSeL (in contrast to the older IPM) supports different separation logics as well. For more details on the proofmode, see [proofmode.md](proofmode.md).

# Using Iris-Lean as a Dependency

- Iris-Lean is updated in sync with Lean. The [releases](https://github.com/leanprover-community/iris-lean/releases) page includes tags for recent versions.
- The `master` branch may contain features added since the last release:
```
[[require]]
name = "iris"
git = "https://github.com/leanprover-community/iris-lean.git"
rev = "master"
```
- The `unstable` tag will be periodically updated with features that are still in development:
```
[[require]]
name = "iris"
git = "https://github.com/leanprover-community/iris-lean.git"
rev = "unstable"
```

# Development

This project started as part of Lars König's master's thesis at Karlsruhe Institute of Technology (KIT). It is currently being maintained by Mario Carneiro and Markus de Medeiros. 

For questions, contribution guidance, and development information, see the [iris-lean channel](https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean) on the Lean Zulip. We always welcome new contributors, and would be happy to help you find something to work on!


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
