# Contributing to Iris-Lean

We enthusiastically welcome contributions to this fork of Iris-Lean!

This project aims to develop the [Bluebell](https://arxiv.org/abs/2402.18708) program logic on top of Iris. Whether you are fixing bugs, improving documentation, or adding new formalizations, your input is valuable. We particularly encourage contributions that address:

* **Active formalizations:** Please see the [Bluebell paper](https://arxiv.org/abs/2402.18708) for the theoretical foundations and goals of this project.
* **Open Issues:** Please see the list of open issues for bugs, requested features, and specific formalization tasks. Issues tagged as `good first issue` or `help wanted` are great places to start.
* **Documentation:** Documentation is actively being worked on.

If you are interested in contributing but unsure where to begin, please get in touch via the [Iris-Lean Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean).

### Large Contributions

For substantial contributions, such as formalizing a new section of the Bluebell logic, we strongly encourage aligning with the paper first.

* **Bluebell Paper:** The [Bluebell paper](https://arxiv.org/abs/2402.18708) acts as the primary specification (or "blueprint") for this project.
    * It outlines the definitions, theorems, and logical rules we aim to formalize.
    * Please verify that your contributions match the definitions and theorems presented in the paper.
* **Process:** Please open a new discussion or issue to propose your planned contribution and discuss how it fits into the existing formalization before starting implementation.

### Style Guide

Iris-Lean aims to align closely with the established conventions of the Lean community, particularly those used in `mathlib`.
Please follow the [mathlib Style Guide](https://github.com/leanprover-community/mathlib4/blob/master/CONTRIBUTING.md#style-guide-and-conventions).
This covers naming conventions, proof style, formatting, and more.

Adhering to this style guide ensures consistency across the library, making it easier for everyone to read, understand, and maintain the code. Please ensure your code compiles and follows these standards.

#### Citation Standards

When referencing papers in Lean docstrings:

* **Use citation keys in text**: Reference papers with citation keys (e.g., `[Bluebell24]`) rather than full titles or URLs.

* **Include a References section**: Each file that cites papers should have a `## References` section in its docstring header.

## Code of Conduct

To ensure a welcoming and collaborative environment, this project follows the principles outlined in the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md).

By participating in this project (e.g., contributing code, opening issues, commenting in discussions), you agree to abide by its terms. Please treat fellow contributors with respect. Unacceptable behavior can be reported to the project maintainers.

## Licensing

This project is licensed under the terms of the Apache License 2.0 license. The full license text can be found in the [LICENSE](LICENSE) file.

By contributing to Iris-Lean, you agree that your contributions will be licensed under this same license. Ensure you are comfortable with these terms before submitting contributions.
