## Description
Briefly describe your changes, and link any issues if appropriate.

Fixes # (issue number)

## Checklist
* [ ] My code follows the mathlib [naming](https://leanprover-community.github.io/contribute/naming.html) and [code style](https://leanprover-community.github.io/contribute/style.html) conventions
* [ ] I have updated `PORTING.md` as appropriate
* [ ] I have added my name to the `authors` section of any appropriate files

## Generative AI Guidelines
AI assistance is permitted when making contributions to Iris-Lean, however, generative AI systems tend to produce code which takes a long time to review. 
Please carefully review your code to ensure it meets the following standards.

- Your PR should avoid duplicating constructions found in Iris-Lean or in the Lean standard library.
- Short, single-use `have` statements should be inlined.
- Your proofs should be shortened such that their overall structure is explicable to a human reader. As a goal, aim to express one idea per line.
- In general, proofs should not perform substantially more case splitting than their Rocq counterparts.

In our experience, a good place to begin refactoring is by re-arranging and combining independent tactic invocations. 
We also find that pointing generative AI systems to the Mathlib code style guidelines can help them perform some of this refactoring work. 
