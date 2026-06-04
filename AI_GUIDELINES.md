# Generative AI Guidelines
AI assistance is permitted when making contributions to Iris-Lean, however, generative AI systems tend to produce code which takes a long time to review. 
Please carefully review your code to ensure it meets the following standards.

- Your PR should avoid duplicating constructions found in Iris-Lean or in the Lean standard library.
- `have` statements that do not aid readability or code reuse should be inlined. 
- Your proofs should be shortened such that their overall structure is explicable to a human reader. As a goal, aim to express one idea per line.
- In general, proofs should not perform substantially more case splitting than their Rocq counterparts.

In our experience, a good place to begin refactoring is by re-arranging and combining independent tactic invocations. 
We also find that pointing generative AI systems to the Mathlib code style guidelines can help them perform some of this refactoring work. 


