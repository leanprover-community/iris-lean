Lean 4 port of *Iris*, a higher-order concurrent separation logic framework.

# About Iris

"Iris is a framework that can be used for reasoning about safety of concurrent programs, as the logic in logical relations, to reason about type-systems, data-abstraction etc."<br>
– https://iris-project.org/

Rocq formalization of Iris: https://gitlab.mpi-sws.org/iris/iris/

# Project

Currently, Iris-Lean has support for 
- *MoSeL*, the proof interface of Iris
- `IProp`, the standard model of Iris
- `HeapLang`, the Iris example language and logic
- A selection of the Iris resources, including invariants, later credits, and many more.

Users of Iris-Lean should be aware of the documentation:
- [tactics.md](docs/tactics.md): Instructions for using Iris tactics.
- [tracking site](https://leanprover-community.github.io/iris-lean/): Iris-Lean correspondence for definitions in Iris-Rocq.
- [compatibility.md](docs/tactics.md): Important differences between Iris-Rocq and Iris-Lean.
- [proofmode.md](docs/proofmode.md): Details of *MoSeL*; support for separation logics other than Iris.

# Using Iris-Lean as a Dependency

- Iris-Lean is updated in sync with Lean. The [releases](https://github.com/leanprover-community/iris-lean/releases) page includes tags for recent versions.
- The `master` branch may contain features added since the last release:
```
[[require]]
name = "iris"
git.url = "https://github.com/leanprover-community/iris-lean.git" 
git.subDir = "Iris" 
rev = "master"
```
- To use Iris constructions based on mathlib, you can also import the math library
```
[[require]]
name = "iris"
git.url = "https://github.com/leanprover-community/iris-lean.git" 
git.subDir = "IrisMath" 
rev = "master"
```

# Development

Development for Iris-Lean coordinates in:
- The [iris-lean channel](https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean) on the Lean Zulip. 
- The [Iris Mattermost channel](https://mattermost.mpi-sws.org/iris/channels/iris-lean)

We always welcome new contributors! For questions, contribution guidance, and development information, feel free to introduce yourself on the Zulip. 

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
