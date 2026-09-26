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
| 2 | Generalize `BI/`, `ProofMode/`, `Instances/UPred` over `SI`; gate finite-only later laws | ⬜ |
| 3 | Step-index property classes (`TransfiniteIndex`, `LargeIndex`, ...), big later `⧍`, satisfiability, ordinal instances | ⬜ |
| 4 | Transfinite COFE solver and `IProp` over arbitrary `SI` | ⬜ |
| 5 | Logical steps, strong WP (`swp`), transfinite adequacy, HeapLang lifting | ⬜ |
| 6 | Refinement WP, time credits, SEQ; examples (termination, refinements, key ideas) | ⬜ |

## File-by-file status

### `algebra/`

| Rocq file | Lean | Status | Notes |
|---|---|---|---|
| `stepindex.v` (`indexT`, `index_rec`, limits) | `Algebra/StepIndex.lean` | ✅ | upstream `SIdx` interface; `SIdx.rec'` is `index_rec` |
| `stepindex.v` (`natI`, `FiniteIndex`) | `Algebra/StepIndexFinite.lean` | ✅ | `natSIdx`, `SIdxFinite` |
| `stepindex.v` (`pairI` = ω²) | | ⬜ | lexicographic pairs |
| `stepindex.v` (`TransfiniteIndex`, `LargeIndex`, `FiniteExistential`, `FiniteBoundedExistential`, `Classical`) | | ⬜ | phase 3 |
| `ordinals/set_*.v`, `ordinals/ord_stepindex.v` | `IrisMath/StepIndex.lean` | 🟡 | `SIdx Ordinal` via Mathlib; `TransfiniteIndex`/`LargeIndex` instances pending |
| `ordinals/arithmetic.v` | | ⬜ | natural sum/difference via Mathlib `NatOrdinal` |
| `ofe.v`: OFEs, `dist_later`, contractive maps | `Algebra/OFE.lean` | ✅ | from #576 |
| `ofe.v`: `bchain`, `bcompl`, `Cofe` | `Algebra/OFE.lean` | ✅ | upstream interface: `lbcompl` only at limits; `bcompl` for any `n` derived (`Iris.bcompl`) |
| `ofe.v`: transfinite fixpoint (`bfpc`, `fixpoint_chain`) | `Algebra/OFE.lean` | ✅ | `BFChain`, `fixpointBFChain` (from #550/#576) |
| `ofe.v`: `LimitPreserving` + `BoundedLimitPreserving` | `Algebra/OFE.lean` | ✅ | merged into one class as upstream |
| `ofe.v`: later OFE with transfinite `bcompl` | `Algebra/OFE.lean` | ✅ | |
| `ofe.v`: `BcomplUnique*`, truncation (`Truncatable`, `ProtoTruncatable`) | | ⬜ | needed by the solver (phase 4) |
| `cmra.v` | `Algebra/CMRA.lean` | ✅ | `validN_le` |
| `cmra.v`: ordinal CMRA `OrdR`/`OrdUR` (natural sum) | | ⬜ | phase 6 (time credits) |
| `excl.v`, `csum.v`, `list.v`, `gmap.v` COFEs | `Excl`, `Csum`, `List`, `Heap` | ✅ | upstream `lbcompl`s |
| `agree.v`, `auth.v`, `frac.v`, `functions.v`, `local_updates.v`, `updates.v`, `big_op.v`, `vector.v`, `gmap` CMRA, ... | resp. files | ✅ | generic in `SI` |
| `wf_IR.v` (well-founded induction-recursion) | | ⬜ | solver |
| `cofe_solver.v` (transfinite solver, 3k lines) | `Algebra/COFESolver.lean` | ⬜ | currently the finite (ω) solver |
| `mlist.v`, `dfrac.v`, `auth_map.v`, `auth_frac.v` | | ➖ | not transfinite-specific; `DFrac`/`MonoList`/`HeapView` exist |

### `base_logic/`

| Rocq file | Lean | Status | Notes |
|---|---|---|---|
| `upred.v`: `uPred` over `SI` | `Algebra/UPred.lean` | ✅ | |
| `upred.v`: `uPred_bcompl'` | `Algebra/UPred.lean` | ✅ | `UPred.bcompl` |
| `upred.v`: connectives, later = `∀ n' < n` | `Instances/UPred/Instance.lean` | ⬜ | phase 2 |
| `upred.v`: `later_exist_false`, `later_sep_1`, `later_ownM` (finite only) | | ⬜ | phase 2 |
| `upred.v`: `later_finite_exist_false` (`FiniteBoundedExistential`) | | ⬜ | phase 2 |
| `upred.v`: `big_later_soundness`, `⧍` | | ⬜ | phase 3 |
| `upred.v`: timelessness in the model (`later_or_timeless`, `later_exist_timeless`, ...) | | ⬜ | phase 2 |
| `upred.v`: `later_or_is_classical`, `later_or_commute_classically` | | ⬜ | phase 3 |
| `satisfiable.v` | | ⬜ | phase 3 |
| `derived.v` (`transfinite_soundness`, timeless instances) | | ⬜ | |
| `lib/logical_step.v` | | ⬜ | phase 5 |
| `lib/fancy_updates.v` (`satisfiable_at`) | | ⬜ | phase 5 |
| `lib/own.v` (`initial_satisfiable`) | | ⬜ | |
| `lib/{invariants,wsat,na_invariants,cancelable_invariants,gen_heap,proph_map,saved_prop,viewshifts}.v` | `Instances/Lib/*` | 🟡 | exist for `SI = Nat`; need generalization after phase 4 |

### `bi/`

| Rocq file | Lean | Status | Notes |
|---|---|---|---|
| `interface.v`: `SbiMixin` with finite-gated laws | `BI/BI.lean` | ⬜ | phase 2 |
| `derived_laws_sbi.v` (finite-gated `later_exist`, `later_or`, ...) | `BI/DerivedLawsLater.lean` | ⬜ | phase 2 |
| `big_op.v` (finite-gated `big_sep*_later`) | `BI/BigOp/*` | ⬜ | phase 2 |
| `satisfiable.v` | | ⬜ | phase 3 |
| `weakestpre.v` (`Swp`, `Rswp`) | | ⬜ | phase 5 |
| other `bi/*.v` | `BI/*` | 🟡 | exist, `SI = Nat` |

### `proofmode/`

| Rocq file | Lean | Status | Notes |
|---|---|---|---|
| `class_instances_sbi.v` (finite-gated later instances) | `ProofMode/InstancesLater.lean` | ⬜ | phase 2 |
| rest | `ProofMode/*` | 🟡 | exist, `SI = Nat` |

### `program_logic/`

| Rocq file | Lean | Status |
|---|---|---|
| `weakestpre.v` (logical-step WP, `swp`) | | ⬜ |
| `lifting.v`, `ectx_lifting.v` | | ⬜ |
| `adequacy.v` (`TransfiniteIndex`) | | ⬜ |
| `refinement/ref_source.v` | | ⬜ |
| `refinement/ref_weakestpre.v` | | ⬜ |
| `refinement/ref_lifting.v`, `ref_ectx_lifting.v` | | ⬜ |
| `refinement/ref_adequacy.v` | | ⬜ |
| `refinement/tc_weakestpre.v` | | ⬜ |
| `refinement/seq_weakestpre.v` | | ⬜ |

### `heap_lang/`

| Rocq file | Lean | Status |
|---|---|---|
| `lifting.v` (`swp`/`rwp` rules) | | ⬜ |
| `proofmode.v` (`wp_swp`, `swp_step`) | | ⬜ |
| `adequacy.v` | | ⬜ |

### `examples/`

| Rocq file | Status |
|---|---|
| `transfinite.v` | ⬜ |
| `counterexamples.v` | ⬜ |
| `keyideas/simulations.v`, `keyideas/generalized_simulations.v` | ⬜ |
| `termination/{adequacy,derived,thunk,eventloop,logrel}.v` | ⬜ |
| `refinements/{refinement,derived,examples,memoization}.v` | ⬜ |
| `safety/*` | ➖ (upstream HeapLang library examples; most exist in `HeapLang/Lib`) |

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
