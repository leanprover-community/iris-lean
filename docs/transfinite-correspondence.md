# Transfinite Iris ↔ Iris-Lean correspondence

This file maps the Rocq development of [Transfinite Iris](https://iris-project.org/transfinite-iris/)
(`~/Downloads/transfinite/theories`, a 2020 fork of Iris 3.3, 53.8k lines in 150 files) to Iris-Lean
(branch `transfinite`, based on PR #576). The roadmap and design notes are in
[`transfinite-porting.md`](transfinite-porting.md).

Paths on the Lean side are relative to `Iris/Iris/` unless they start with `IrisMath/`.

Status markers:

- ✅ ported (builds)
- 🟡 partially ported, or ported with a restriction (see the notes)
- ⬜ not yet ported
- ➖ no port needed: generic Iris that Iris-Lean already has (ported from upstream Iris), a Rocq
  artifact (setoid `Proper` instances, `seal`s, `Canonical Structure`s, ...), or replaced by
  Mathlib/Lean's classical logic

Most of the fork is ordinary Iris 3.3 with an extra `{SI : indexT}` parameter. Upstream Iris (and hence
Iris-Lean) has since caught up with that generalization, so for those files the right counterpart
is the generic Iris-Lean file. That file is marked ✅ once it is generic in the step-index type, and 🟡
if it still fixes `SI = Nat`. The **transfinite-specific** content, where the fork is the only source,
is listed declaration by declaration in [Part II](#part-ii-transfinite-specific-declarations).

---

## Part I: file-level map

### `algebra/`

| Rocq file | Lines | Lean | Status | Notes |
|---|---:|---|---|---|
| `base.v` | 6 | `Std/` | ➖ | stdpp re-exports |
| `stepindex.v` | 832 | `Algebra/StepIndex.lean`, `Algebra/StepIndexFinite.lean`, `Algebra/StepIndexTransfinite.lean` | 🟡 | `pairI` (ω²) missing; see [Part II](#algebrastepindexv) |
| `ofe.v` | 2443 | `Algebra/OFE.lean` | 🟡 | generic; `BcomplUnique`, `Truncatable`, `ProtoTruncatable` (needed by the solver) missing |
| `cmra.v` | 1695 | `Algebra/CMRA.lean` | 🟡 | generic; ordinal CMRA (`ordA`, natural sum) missing (time credits) |
| `cofe_solver.v` | 3090 | `Algebra/COFESolver.lean` | ⬜ | Lean has the finite (ω) America–Rutten solver only |
| `wf_IR.v` | 231 | — | ⬜ | well-founded induction-recursion, used only by the transfinite solver |
| `agree.v` | 329 | `Algebra/Agree.lean` | ✅ | |
| `auth.v` | 507 | `Algebra/Auth.lean`, `Algebra/View.lean` | ✅ | upstream defines `auth` through `view` |
| `auth_frac.v` | 63 | `Algebra/Auth.lean` (fractional `●{dq}`) | ➖ | upstream `auth` has fractional authorities |
| `auth_map.v` | 673 | `Algebra/HeapView.lean`, `Instances/Lib/GhostMap.lean` | ➖ | Perennial backport; superseded by upstream `ghost_map` |
| `big_op.v` | 536 | `Algebra/BigOp.lean`, `Algebra/CMRABigOp.lean` | ✅ | |
| `coPset.v` | 135 | `Std/CoPset.lean`, `Algebra/LeibnizSet.lean` | ✅ | |
| `csum.v` | 434 | `Algebra/Csum.lean` | ✅ | transfinite `lbcompl` |
| `dfrac.v` | 217 | `Algebra/DFrac.lean` | ✅ | |
| `excl.v` | 172 | `Algebra/Excl.lean` | ✅ | transfinite `lbcompl` |
| `frac.v` | 66 | `Algebra/Frac.lean` | ✅ | |
| `frac_auth.v` | 120 | `Algebra/Lib/FracAuth.lean` | ✅ | |
| `functions.v` | 161 | `Algebra/Functions.lean` | ✅ | |
| `gmap.v` | 621 | `Algebra/Heap.lean`, `Algebra/GenMap.lean` | ✅ | transfinite `lbcompl` |
| `gmultiset.v` | 92 | `Algebra/LeibnizMultiSet.lean` | ✅ | |
| `gset.v` | 235 | `Algebra/LeibnizSet.lean` | ✅ | |
| `list.v` | 513 | `Algebra/List.lean` | ✅ | transfinite `lbcompl` |
| `local_updates.v` | 210 | `Algebra/LocalUpdates.lean` | ✅ | |
| `mlist.v` | 346 | `Algebra/Lib/MonoList.lean` | 🟡 | upstream `mono_list`; stays at `SI = Nat` (grind lemmas, see porting notes) |
| `monoid.v` | 55 | `Algebra/Monoid.lean` | ✅ | |
| `namespace_map.v` | 299 | `Algebra/ReservationMap.lean` | ✅ | renamed upstream |
| `proofmode_classes.v` | 54 | `Algebra/IsOp.lean`, `ProofMode/Classes.lean` | ✅ | |
| `ufrac.v` | 51 | `Algebra/UFrac.lean` | ✅ | |
| `ufrac_auth.v` | 143 | `Algebra/Lib/UFracAuth.lean` | ✅ | |
| `updates.v` | 181 | `Algebra/Updates.lean` | ✅ | |
| `vector.v` | 115 | `Algebra/Vector.lean` | ✅ | |
| `ordinals/set_sets.v` | 516 | Mathlib | ➖ | Aczel-tree set model, replaced by Mathlib's `Ordinal` |
| `ordinals/set_model.v` | 717 | Mathlib | ➖ | idem |
| `ordinals/set_ordinals.v` | 508 | Mathlib | ➖ | idem |
| `ordinals/set_functions.v` | 1021 | Mathlib | ➖ | idem |
| `ordinals/ord_stepindex.v` | 322 | `IrisMath/StepIndex.lean`, `IrisMath/Transfinite.lean` | ✅ | see [Part II](#algebraordinalsord_stepindexv) |
| `ordinals/arithmetic.v` | 837 | Mathlib (`NatOrdinal`) | ⬜ | natural (Hessenberg) sum/difference; needed for the ordinal CMRA of time credits |

### `base_logic/`

| Rocq file | Lines | Lean | Status | Notes |
|---|---:|---|---|---|
| `base_logic.v`, `proofmode.v` | 55 | `Instances/UPred.lean`, `Instances/UPred/ProofMode.lean` | ✅ | re-exports |
| `upred.v` | 1074 | `Algebra/UPred.lean`, `Instances/UPred/Instance.lean`, `Instances/UPred/Transfinite.lean` | ✅ | generic model + transfinite laws; see [Part II](#base_logicupredv) |
| `bi.v` | 236 | `Instances/UPred/Instance.lean` | ✅ | `uPredI`/`uPredSI` instances |
| `derived.v` | 225 | `Instances/UPred/Instance.lean`, `Instances/UPred/Transfinite.lean` | ✅ | see [Part II](#base_logicderivedv) |
| `satisfiable.v` | 100 | `Instances/UPred/Transfinite.lean` | ✅ | see [Part II](#base_logicsatisfiablev-and-bisatisfiablev) |
| `lib/iprop.v` | 162 | `Algebra/IProp.lean`, `Instances/IProp/` | 🟡 | `IProp` needs the (finite) solver, so `SI = Nat` |
| `lib/own.v` | 363 | `Instances/IProp/Instance.lean` | 🟡 | `SI = Nat`; `initial_satisfiable` ⬜ |
| `lib/wsat.v` | 254 | `Instances/Lib/WSat.lean` | 🟡 | `SI = Nat` |
| `lib/fancy_updates.v` | 227 | `Instances/Lib/FUpd.lean` | 🟡 | `SI = Nat`; `satisfiable_at` ⬜ |
| `lib/invariants.v` | 211 | `Instances/Lib/Invariants.lean` | 🟡 | `SI = Nat` |
| `lib/na_invariants.v` | 195 | `Instances/Lib/NaInvariants.lean` | 🟡 | `SI = Nat` |
| `lib/cancelable_invariants.v` | 132 | `Instances/Lib/CInvariants.lean` | 🟡 | `SI = Nat` |
| `lib/saved_prop.v` | 136 | `Instances/Lib/SavedProp.lean` | 🟡 | `SI = Nat` |
| `lib/gen_heap.v` | 439 | `BI/Lib/GenHeap.lean` | 🟡 | `SI = Nat` |
| `lib/proph_map.v` | 193 | `BI/Lib/ProphMap.lean` | 🟡 | `SI = Nat` |
| `lib/viewshifts.v` | 88 | `Instances/Lib/FUpdFromViewShift.lean` | 🟡 | `SI = Nat` |
| `lib/logical_step.v` | 402 | `BI/Lib/LogicalStep.lean` | ✅ | generic in `SI`, see [Part II](#base_logicliblogical_stepv) |

### `bi/`

| Rocq file | Lines | Lean | Status | Notes |
|---|---:|---|---|---|
| `interface.v` | 480 | `BI/BIBase.lean`, `BI/BI.lean`, `BI/Sbi.lean` | ✅ | finite-only later laws gated by `[SIdxFinite SI]` |
| `derived_laws_bi.v` | 1544 | `BI/DerivedLaws.lean` | ✅ | |
| `derived_laws_sbi.v` | 568 | `BI/DerivedLawsLater.lean` | ✅ | gated as in the fork (`later_exist_false`, `later_sep`, `later_absorbingly`, ...) |
| `derived_connectives.v`, `notation.v`, `bi.v` | 282 | `BI/Classes.lean`, `BI/Notation.lean`, `BI.lean` | ✅ | |
| `big_op.v` | 1734 | `BI/BigOp/` | ✅ | `big_sep*_later` gated by `[SIdxFinite SI]` |
| `embedding.v` | 327 | `BI/Embedding.lean` | ✅ | |
| `plainly.v` | 547 | `BI/Plainly.lean` | ✅ | |
| `updates.v` | 499 | `BI/Updates.lean` | ✅ | |
| `telescopes.v` | 82 | `BI/Telescopes.lean` | ✅ | |
| `tactics.v` | 214 | `ProofMode/` | ➖ | Rocq reflection tactics |
| `lib/fixpoint.v` | 124 | `BI/Lib/Fixpoint.lean` | ✅ | |
| `lib/fractional.v` | 180 | `BI/Lib/Fractional.lean` | ✅ | |
| `satisfiable.v` | 99 | `BI/Transfinite.lean` | ✅ | see [Part II](#base_logicsatisfiablev-and-bisatisfiablev) |
| `weakestpre.v` | 574 | `BI/WeakestPre.lean` | 🟡 | ordinary WP classes exist; `Swp`/`Rswp` (strong/refinement WP) classes ⬜ |

### `proofmode/`

All files map to `ProofMode/` (✅: generic in `SI` since commit `1461d72`). Transfinite-specific
content: `class_instances_sbi.v` gates the instances that commute `▷` with `∗`/`∃`
(`into_later_sep`, `into_later_exist`, ...), mirrored by `ProofMode/InstancesLater.lean` using
`[SIdxFinite SI]`. `ltac_tactics.v`, `environments.v`, `coq_tactics.v`, `intro_patterns.v`,
`spec_patterns.v`, `sel_patterns.v`, `tokens.v`, `notation.v`, `reduction.v` are the Rocq tactic
implementation (➖, replaced by the Lean IPM).

### `program_logic/`

| Rocq file | Lines | Lean | Status | Notes |
|---|---:|---|---|---|
| `language.v`, `ectx_language.v`, `ectxi_language.v` | 655 | `ProgramLogic/Language.lean`, `EctxLanguage.lean`, `EctxiLanguage.lean` | ✅ | language-level, no `SI` |
| `weakestpre.v` | 724 | `ProgramLogic/WeakestPre.lean` | ⬜ | fork's WP is built from *logical steps* and a strong WP `swp`; Lean has upstream's WP at `SI = Nat` |
| `lifting.v` | 281 | `ProgramLogic/Lifting.lean` | ⬜ | `swp` lifting lemmas |
| `ectx_lifting.v` | 178 | `ProgramLogic/EctxLifting.lean` | ⬜ | idem |
| `adequacy.v` | 284 | `ProgramLogic/Adequacy.lean` | ⬜ | uses `TransfiniteIndex`, big-later soundness, satisfiability |
| `hoare.v` | 162 | — | ➖ | Hoare-triple notation on top of WP |
| `refinement/ref_source.v` | 382 | — | ⬜ | source-program resource (auth of source state), `SI`-generic |
| `refinement/ref_weakestpre.v` | 691 | — | ⬜ | refinement WP (`RSWP`/`RWP`) |
| `refinement/ref_lifting.v` | 244 | — | ⬜ | |
| `refinement/ref_ectx_lifting.v` | 201 | — | ⬜ | |
| `refinement/ref_adequacy.v` | 354 | — | ⬜ | termination-preserving refinement, needs `LargeIndex` |
| `refinement/tc_weakestpre.v` | 103 | — | ⬜ | time credits `$α` with ordinals |
| `refinement/seq_weakestpre.v` | 32 | — | ⬜ | sequential WP |

### `heap_lang/`

| Rocq file | Lines | Lean | Status | Notes |
|---|---:|---|---|---|
| `lang.v`, `locations.v`, `notation.v`, `metatheory.v`, `tactics.v` | 1253 | `HeapLang/Syntax.lean`, `Semantics.lean`, `Notation.lean`, `Metatheory.lean`, `Tactic.lean` | ✅ | language-level |
| `lifting.v` | 1349 | `HeapLang/PrimitiveLaws.lean`, `DerivedLaws.lean` | 🟡 | ordinary WP rules exist at `SI = Nat`; `swp`/`rwp` rules ⬜ |
| `proofmode.v` | 1007 | `HeapLang/ProofMode.lean` | 🟡 | `wp_*` tactics exist; `swp_*`/`rwp_*` ⬜ |
| `adequacy.v` | 38 | `ProgramLogic/Adequacy.lean` | ⬜ | transfinite adequacy |

### `examples/`

| Rocq file | Lines | Lean | Status | Notes |
|---|---:|---|---|---|
| `counterexamples.v` | 227 | `Examples/TransfiniteCounterexamples.lean` | ✅ | see [Part II](#examplescounterexamplesv) |
| `transfinite.v` | 150 | — | ⬜ | invariants + `swp` with transfinite indices (needs `IProp` over ordinals, `swp`) |
| `keyideas/simulations.v` | 252 | `Examples/TransfiniteSimulations.lean` | ✅ | in `UPred M` instead of `iProp Σ`; see [Part II](#examplekeyideas) |
| `keyideas/generalized_simulations.v` | 147 | `Examples/TransfiniteSimulations.lean` | ✅ | idem |
| `termination/{adequacy,derived,thunk,eventloop,logrel}.v` | 1534 | — | ⬜ | termination logic (needs `tc_weakestpre`) |
| `refinements/{refinement,derived,examples,memoization}.v` | 3496 | — | ⬜ | refinement logic (needs `ref_weakestpre`) |
| `safety/*` | 1025 | `HeapLang/Lib/*` | ➖ | upstream HeapLang library examples (`lock`, `spin_lock`, `ticket_lock`, `par`, `spawn`, `counter`, coins, `nondet_bool`, `assert`) exist in Iris-Lean; `barrier/` does not |

---

## Part II: transfinite-specific declarations

### `algebra/stepindex.v`

| Rocq | Lean | Status |
|---|---|---|
| `indexT`, `IndexMixin`, `index_lt`, `index_le`, `index_zero`, `index_succ` | `SIdx` (`Algebra/StepIndex.lean`) | ✅ |
| `index_*` order lemmas (`index_lt_le_trans`, `index_succ_iff`, `index_le_total`, ...) | `SIdx.*` (`lt_le_trans`, `lt_succ_r`, `le_total`, ...) | ✅ |
| `index_is_limit`, `limit_idx` | `SIdx.Limit` | ✅ |
| `index_min` and lemmas | — | ➖ (unused outside the solver; use `min`) |
| `ord_match`, `index_rec`, `index_rec_unfold`, `index_rec_zero/succ/lim`, `index_rec_lim_ext` | `SIdx.case`, `SIdx.rec'`, `SIdx.rec_unfold`, `SIdx.rec_zero/succ/lim` | ✅ |
| `index_cumulative_rec*` | — | ⬜ (solver) |
| `FiniteIndex`, `natI`, `nat_index_mixin` | `SIdxFinite`, `natSIdx` (`Algebra/StepIndexFinite.lean`) | ✅ |
| `TransfiniteIndex` (`upper_limit`, `upper_limit_bound`) | `SIdxTransfinite` (`upperLimit`, `iter_succ_lt_upperLimit`) | ✅ |
| `LargeIndex` (`commute_exists`) | `SIdxLarge` | ✅ |
| `FiniteExistential`, `can_split_or` | `SIdx.forall_or` (theorem: holds classically) | ✅ |
| `FiniteBoundedExistential`, `can_split_bounded_or` | `SIdx.forall_lt_or` | ✅ |
| `Classical`, `classical_can_commute_or`, `classical_finite_existential`, ... | — | ➖ (Lean is classical) |
| `can_commute_finite_exists` | `SIdx.commute_finite_exists` | ✅ |
| `can_commute_finite_bounded_exists` | `SIdx.commute_finite_bounded_exists` | ✅ |
| `large_index_finite_existential`, `finite_bounded_from_finite` | — | ➖ (the targets are theorems) |
| `pair_zero`, `pair_succ`, `pair_lt`, `pair_lt_wf`, `pair_index_mixin`, `pairI` (ω²), `TransfiniteIndex pairI` | — | ⬜ |
| `classical_dn`, `classical_forall_exists*`, `classical_impl`, `find_least` | Lean core / Mathlib | ➖ |

### `algebra/ordinals/ord_stepindex.v`

| Rocq | Lean | Status |
|---|---|---|
| `Ord`, `zero`, `succ`, `limit`, `ord_lt`, `ord_index_mixin`, `ordI` | `SIdx Ordinal` (`IrisMath/StepIndex.lean`) | ✅ |
| `jump_limit`, `TransfiniteIndex ordI` | `ordinalSIdxTransfinite` (`upperLimit m := m + ω`) | ✅ |
| `limit_upper_bound*`, `limit_mono*`, `limitO*`, `ordinals_lt`, ... | Mathlib (`Ordinal.iSup`, `Ordinal.lt_iSup_add_one`, ...) | ➖ |
| `upper_bound_ordinal`, `constructive_upper_bound_ordinal`, `commute_exists` | proof of `ordinalSIdxLarge` | ✅ |
| `set_model_large_index : LargeIndex ordI` | `ordinalSIdxLarge : SIdxLarge.{u} Ordinal.{u}` | ✅ |
| `or_to_sum`, `classic_*` | — | ➖ |

### `base_logic/upred.v`

| Rocq | Lean | Status |
|---|---|---|
| `uPred` over `SI`, `uPred_ne`, `uPred_mono` | `UPred` (`Algebra/UPred.lean`) | ✅ |
| `uPred_bcompl'`, `uPred_bcompl'_ne`, `bcompl_unfold` | `UPred.bcompl`, `UPred.bcompl_ne`, `UPred.bcompl_holds` | ✅ |
| `bcompl_unique : BcomplUnique uPredO` | — | ⬜ (needs `BcomplUnique`, solver) |
| `uPred_later` (`∀ β ≺ α`) | `UPred.later` (`Instances/UPred/Instance.lean`) | ✅ |
| `later_exist_false` (`FiniteIndex`) | `later_sExists_false` field, `[SIdxFinite SI]` | ✅ |
| `later_finite_exist_false` (`FiniteBoundedExistential`) | `later_or_1` (the finite case needed by the BI), `Instances/UPred/Instance.lean` | ✅ |
| `later_sep_1` (`FiniteIndex`), `later_sep_2` | `later_sep_1` field (`[SIdxFinite SI]`), `later_sep_2` field | ✅ |
| `later_ownM` (`FiniteIndex`) | `UPred.later_ownM [SIdxFinite SI]` | ✅ |
| `later_false_em`, `later_persistently_*`, `later_plainly_*`, `later_eq_*` | generic BI fields | ✅ |
| `pure_soundness`, `later_soundness` | `UPred.pure_soundness`, `UPred.later_soundness` | ✅ |
| `big_later_soundness` (`TransfiniteIndex`) | `UPred.big_later_soundness` | ✅ |
| `big_laterN_soundness` | `UPred.big_laterN_soundness` | ✅ |
| `⧍ P`, `⧍^n P` notations | `bigLater`, `bigLaterN`, notation `⧍ P` (`BI/Transfinite.lean`) | ✅ |
| `timeless` (model-level), `pure_timeless` | BI `Timeless` | ✅ |
| `timeless_zero` | `UPred.timeless_zero` | ✅ |
| `later_or_timeless` | `later_or` (holds for every `SI`, `BI/DerivedLawsLater.lean`) | ✅ |
| `later_sep_timeless` | `UPred.later_sep_timeless` | ✅ |
| `later_exist_timeless` | `UPred.later_exist_timeless` | ✅ |
| `later_or_commute_classically`, `dec_halting` | `UPred.later_or_is_classical` | ✅ |

### `base_logic/derived.v`

| Rocq | Lean | Status |
|---|---|---|
| `pure_timeless`, `emp_timeless`, `or_timeless`, `wand_timeless`, `persistently_timeless`, `absorbingly_timeless`, `intuitionistically_timeless`, `eq_timeless`, `big_sep*_timeless` | generic BI instances | ✅ |
| `sep_timeless` (all `SI`) | `UPred.sep_timeless'` | ✅ |
| `exist_timeless` (all `SI`) | `UPred.exists_timeless'` | ✅ |
| `valid_timeless`, `ownM_timeless`, `cmra_valid_*`, `ownM_*`, `bupd_ownM_update`, `bupd_plain_soundness` | `Instances/UPred/Instance.lean` | ✅ |
| `soundness`, `consistency_modal`, `consistency` | `BI.laterN_soundness`, `UPred.modal_soundness`, `UPred.consistency` | ✅ |
| `transfinite_soundness` (`TransfiniteIndex`) | `UPred.transfinite_soundness` | ✅ |
| `uPred_valid_proper`, `uPred_valid_mono`, `ownM_proper`, `cmra_valid_proper` | — | ➖ (setoid instances) |

### `base_logic/satisfiable.v` and `bi/satisfiable.v`

| Rocq | Lean | Status |
|---|---|---|
| `satisfiable_mixin`, `Satisfiable` | `Satisfiable` class (`BI/Transfinite.lean`) | ✅ |
| `satisfiable_intro/mono/elim/later/bupd` | `Satisfiable.intro/mono/elim/later/bupd` | ✅ |
| `satisfiable_finite_exists` (`FiniteExistential`) | `Satisfiable.finite_exists` (all `SI`) | ✅ |
| `satisfiable_exists` (`LargeIndex`) | `Satisfiable.exists_` (`[SIdxLarge SI]`) | ✅ |
| `satisfiable_forall/impl/wand/pers/intuitionistically/or` | `Satisfiable.forall_elim/imp/wand/pers/intuitionistically/or` | ✅ |
| `satisfiable_equiv` | — | ➖ (`Proper` instance) |
| `uPred_satisfiable` and its lemmas | `UPred.satisfiable`, `UPred.satisfiable_*` (`Instances/UPred/Transfinite.lean`) | ✅ |
| `uPred_satisfiable_mixin`, `uPred_Satisfiable` | `UPred.instSatisfiable` | ✅ |
| (existential property for ordinals) | example in `IrisMath/Transfinite.lean` | ✅ |

### `base_logic/lib/logical_step.v`

All in `BI/Lib/LogicalStep.lean`, generic over `BIFUpdate` and the step-index type. Rocq
notations: `<E>_n P` = `eventuallyN n E P`, `<E> P` = `eventually E P`,
`>={E1}={Ei}={E2}=>_n P` = `gstepN n Ei E1 E2 P`, `>={E1}={Ei}={E2}=> P` = `gstep Ei E1 E2 P`,
`>={E1}=={E2}=> P` = `gstep ∅ E1 E2 P`. The Lean port has no dedicated notation yet.

| Rocq | Lean | Status |
|---|---|---|
| `elim_fupd_step` | `elimModal_step_fupd` | ✅ |
| `eventuallyN`, `eventually` | `eventuallyN`, `eventually` | ✅ |
| `eventuallyN_ne`, `eventually_ne` | same names (instances) | ✅ |
| `eventuallyN_intro`, `eventuallyN_eventually`, `eventuallyN_fupd_left/right`, `eventuallyN_step_left/right`, `eventuallyN_intro_n` | same names | ✅ |
| `eventuallyN_mono` (index monotonicity) | `eventuallyN_mono_le` (`eventuallyN_mono` is monotonicity in `P`) | ✅ |
| `eventually_fupd_left/right`, `eventually_step_right`, `eventuallyN_mask_mono`, `eventually_mask_mono` | same names | ✅ |
| `eventuallyN_compose`, `eventuallyN_compose'`, `eventually_compose`, `eventually_intro` | same names | ✅ |
| `elim_eventuallyN` | `elimModal_eventuallyN` | ✅ |
| `elim_eventually` (local instance) | — | ➖ (use `eventually_compose`) |
| `eventuallyN_equiv`, `eventually_equiv`, `gstep_equiv`, `gstepN_equiv` | — | ➖ (follow from `_ne`) |
| `gstepN`, `gstep`, `gstep_ne`, `gstepN_ne` | same names | ✅ |
| `gstepN_fupd_left/right`, `gstep_fupd_left/right`, `gstepN_gstep`, `gstepN_later`, `gstepN_intro`, `gstepN_intro'`, `gstep_squash` | same names | ✅ |
| `gstepN_change_iter`, `gstep_change_iter`, `gstep_compose`, `gstepN_mono` | same names | ✅ |
| `elim_gstep`, `elim_gstepN`, `elim_gstep_N` | `elimModal_gstep`, `elimModal_gstepN`, `elimModal_gstep_iter` | ✅ |
| `lstep_fupd_left/right`, `lstepN_fupd_left/right`, `lstepN_lstep`, `lstepN_later`, `lstepN_intro'`, `lstepN_intro`, `lstep_squash`, `lstep_intro` | same names | ✅ |

### `examples/counterexamples.v`

All in `Examples/TransfiniteCounterexamples.lean`. The section hypotheses on `ω` are bundled as
`IsOmega ω`.

| Rocq | Lean | Status |
|---|---|---|
| `sProp`, `sProp_later`, `sProp_false`, `sProp_ex` | `SProp`, `SProp.later`, `SProp.false`, `SProp.ex` | ✅ |
| `bounded_existential`, `existential` | `BoundedExistential`, `Existential` | ✅ |
| `transfinite_no_bounded_existential` | same name | ✅ |
| `no_later_existential_commuting` | same name | ✅ |
| `F`, `G`, `c`, `zero_omega`, `bounded_limit_preserving_entails_counterexample` | `not_limitPreserving_entails` | ✅ |
| `f`, `c0`, `zero_omega'`, `test` | `andBigLaterFalse`, `ne_not_preserve_lbcompl` | ✅ |

### `examples/keyideas/*.v` <a name="examplekeyideas"></a>

All in `Examples/TransfiniteSimulations.lean`. The Rocq development works in `iProp Σ`; the Lean
port works in `UPred M` for an arbitrary unital camera `M` and arbitrary step-indices (the
constructions only need satisfiability and guarded/least fixpoints). Rocq's coinductive `ex_loop`
is replaced by the existence of an infinite execution (`ExLoop`), and `nsteps` by
`Relation.Iterate`.

| Rocq | Lean | Status |
|---|---|---|
| `rpr`, `tpr` | `Rpr`, `Tpr` | ✅ |
| `sim_pre`, `sim_pre_contr`, `sim`, `sim_unfold'`, `sim_unfold` | `simPre`, `simPre_contractive`, `sim`, `sim_unfold` | ✅ |
| `sim_plain` | `sim_plain` (via `sim_plain_aux`, by Löb induction) | ✅ |
| `sim_valid_satisfiable`, `satisfiable_pure` | same names | ✅ |
| `sim_execute_tgt_step`, `sim_execute_tgt` | same names (`[SIdxLarge SI]`) | ✅ |
| `sim_is_rpr` (Lemma 2.1), `sim_is_tpr` (Lemma 2.2) | same names | ✅ |
| `ex_loop_sn`, `sn_finite_nondet_bounded`, `finite_nondet_ex_loop_diverge`, `ex_loop_extract_finite_execution` | `exLoop_iff_not_sn`, `sn_finite_nondet_bounded`, `finite_nondet_exLoop_diverge`, `exLoop_extract_finite_execution` | ✅ |
| `sim_finite_ref`, `satisfiable_laterN` | `SimFiniteRef`, `satisfiable_laterN` | ✅ |
| `sim_to_sim_finite_ref`, `sim_finite_ref_tpr` | `sim_to_simFiniteRef` (for every `SI`; the Rocq section assumes `FiniteIndex` but does not use it), `simFiniteRef_tpr` | ✅ |
| `gtpr`, `gsim_pre`, `gsim_pre_mono`, `gsim`, `sim_unfold` (generalized) | `Gtpr`, `gsimPre`, `gsimPre_mono`, `gsim`, `gsim_unfold` | ✅ |
| `gsim_execute_tgt_step`, `sim_execute_tgt` (generalized) | `gsim_execute_tgt_step`, `gsim_execute_tgt` | ✅ |
| `sim_execute_tgt_step` (termination, generalized) | `gsim_execute_loop_step` | ✅ |
| `sim_divergence`, `sim_is_tpr` (generalized) | `gsim_divergence`, `gsim_is_gtpr` | ✅ |

### `base_logic/lib/fancy_updates.v`, `lib/own.v` (transfinite parts)

| Rocq | Lean | Status |
|---|---|---|
| `satisfiable_at`, `satisfiable_at_intro/mono/fupd/later/exists/...` | — | ⬜ (needs `IProp` over arbitrary `SI`) |
| `initial_satisfiable`, `own_satisfiable` | — | ⬜ |

### Not yet started

`algebra/cofe_solver.v`, `algebra/wf_IR.v`, `ofe.v` (`BcomplUnique`, `Truncatable`), `algebra/ordinals/arithmetic.v`,
`cmra.v` (`ordA`), `bi/weakestpre.v` (`Swp`, `Rswp`), all of `program_logic/` apart from the
language definitions, the `swp`/`rwp` parts of `heap_lang/`, and the examples other than the
counterexamples and the key ideas. See [`transfinite-porting.md`](transfinite-porting.md#roadmap) for the plan.
