Lean 4 port of Iris, a higher-order concurrent separation logic framework.

# About Iris

"Iris is a framework that can be used for reasoning about safety of concurrent programs, as the logic in logical relations, to reason about type-systems, data-abstraction etc." - https://iris-project.org/

Coq formalization of Iris: https://gitlab.mpi-sws.org/iris/iris/

# Unicode Input

Most of the unicode characters used in Iris can be written with the Lean extension replacement, e.g. `\ast` will automatically be replaced with `∗`. To add additional replacements, edit the Lean extension setting `lean4.input.customTranslations`. Suggested additional replacements are listed below.

```json
"sep": "∗",
"wand": "-∗"
```

# Development

This project is part of my master's thesis at Karlsruhe Institute of Technology (KIT). I can therefore not accept any substantial pull requests before my master's thesis is finished.
