# Porting Transfinite Iris to Iris-Lean

This document tracks the port of [Transfinite Iris](https://iris-project.org/transfinite-iris/)
(Spies, Gäher, et al., PLDI 2021; Rocq sources at <https://gitlab.mpi-sws.org/iris/transfinite>)
to Iris-Lean. It is organized by the Rocq files of the transfinite development. Status markers:

- ✅ ported (builds)
- 🟡 partially ported / ported with a restriction (see notes)
- ⬜ not yet ported
- ➖ not needed (already present in Iris-Lean, superseded by upstream Iris, or replaced by Mathlib)

## Sources and design

Transfinite Iris is a 2020 fork of Iris 3.3 that abstracts over the type of step-indices. Upstream
Rocq Iris has since absorbed the generic part (Iris 4.4: `algebra` is parametric in `{SI : sidx}`;
Iris master: `bi`, `proofmode`, `si_logic` are parametric too, but the BI laws are unchanged). We
therefore follow **upstream Iris's `sidx` interface** (`Iris/Iris/Algebra/StepIndex.lean`, ported in
#515) and use the transfinite fork only for what upstream does not have: the transfinite `uPred`
model and BI laws, the transfinite COFE solver, satisfiability, logical steps, and the
refinement/termination program logics and examples.

The step-index type is threaded through Iris-Lean using the mechanism of PR #576 (`local
stepindex T`, `stepindex%`, default instances via `DefaultSI`), combined with the `outParam` on
`OFE`/`CMRA`/`UCMRA`/`IsTotal` from PR #683. See [Mechanism notes](#mechanism-notes).

Ordinals come from Mathlib (`IrisMath/IrisMath/StepIndex.lean`: `SIdx Ordinal`), replacing the
fork's Aczel-tree set model (`algebra/ordinals/set_*.v`, ~2.8k lines) and its ordinal arithmetic
(Mathlib's `NatOrdinal` provides the Hessenberg sum).

## Roadmap

| Phase | Content | Status |
|---|---|---|
| 0 | Merge master into #576 | ✅ |
| 1 | Generalize `Algebra/` over `SI` (from #683, without the pending issues listed below) | ✅ |
| 1b | Bounded completions (`lbcompl`) for `Excl`, `Csum`, `List`, `Heap`, `UPred` | ✅ |
| 2 | Generalize `BI/`, `ProofMode/`, `Instances/UPred` over `SI`; gate finite-only later laws | ✅ |
| 3 | Step-index property classes (`TransfiniteIndex`, `LargeIndex`, ...), big later `⧍`, satisfiability, ordinal instances, counterexamples | ✅ |
| 4 | Transfinite COFE solver and `IProp`/`iOwn`/`wsat` over arbitrary `SI` | ✅ |
| 5 | Logical steps, credit-free fupd + invariants, `wp`/`swp`, lifting, adequacy (✅); HeapLang `swp` rules (⬜) | 🟡 |
| 6 | Refinement WP, time credits, SEQ; examples (termination, refinements, key ideas) | ⬜ |

## File-by-file status

See [`transfinite-correspondence.md`](transfinite-correspondence.md), which maps every Rocq file
(and every transfinite-specific declaration) to its Lean counterpart.

## Mechanism notes

Findings from threading the step-index type through Iris-Lean (relevant to PRs #576/#627/#683):

1. **`outParam` on `CMRA` is load-bearing.** `CMRA.pcore`, `CMRA.op` and `CMRA.Valid` do not
   mention the step-index type, so without an `outParam` every unannotated use of them is a stuck
   typeclass problem. #683 therefore makes `SI` an `outParam` of `CMRA`/`UCMRA`/`IsTotal`.
2. **`outParam` on `OFE` follows.** A leaf instance such as `[OFE α] → CMRA (Excl α)` can only
   determine the `outParam` of `CMRA` if the `SI` of `OFE α` is itself an `outParam`.
3. **Quantified instance binders.** With the `outParam`, a lemma binder `[∀ x, CMRA (β x)]` gets
   an auto-bound step-index type depending on `x`. We write `[∀ x, CMRA (SI := stepindex%) (β x)]`
   in lemma statements.
4. **Laws that do not mention `SI`.** Classes whose fields do not mention `SI` (e.g. `MonoidOps`'s
   associativity) produce projections from which `SI` cannot be inferred. We make such fields
   `protected` and restate them as theorems stated in a `local stepindex SI` section.
5. **SI-polymorphic leaf instances** (`CMRA Unit`, `OFE Empty`, ...) need
   `set_option synthInstance.checkSynthOrder false`; they pick `SI` by instance search.
6. **Pretty printing.** Notations that pass `(SI := stepindex%)` lose their automatic
   delaborators; `app_unexpander`s restore them.
7. **Grind lemmas** whose statements do not mention `SI` cannot be generalized (their patterns
   cannot instantiate `SI`); `MaxPrefixList` and `MonoList` stay at `SI = Nat` for now.
