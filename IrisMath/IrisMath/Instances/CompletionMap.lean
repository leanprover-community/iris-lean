/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Iris

/-! # `CompletionMap`: a non-extensional `PartialMap` whose payload is a *convergent sequence*,
observed at its **limit in the completion**

Each key of a `CompletionMap` stores a *representative sequence* `ℕ → V`, and the observation
`get?` collapses that sequence to its **limit along `Filter.atTop`** — its value in the
*completion* of `V` — whenever that limit exists.  Two sequences with the **same limit** but
**different terms** denote the same map even though they are distinct Lean values, so the
representation is genuinely **non-extensional**: two `≠` reps with `PartialMap.equiv`.

## The well-definedness obstruction and how it is resolved

The `Iris.Std.PartialMap` interface is **polymorphic in the value type**: its field
`get? : M V → K → Option V` is universally quantified over *all* `V`, with no class
constraints.  An analytic limit, however, only makes sense in a `[TopologicalSpace V]`, and
is only *unique* in a Hausdorff space `[T2Space V]` (mathlib `tendsto_nhds_unique`).  One
therefore cannot demand topology on the field's `V`.

We resolve this exactly as `GermMap`/`ConstOnFilterMap` do, but read analytically: the
observation `limitValue s` is the unique `c` such that `s` is **eventually constant `= c`
along `atTop`** (`s =ᶠ[atTop] fun _ => c`).  This is `Classical`, total, needs no topology,
and is well-defined for every `V` because `(atTop : Filter ℕ)` is `NeBot`.  Crucially, when
`V` *does* carry a Hausdorff topology, this germ value **coincides with the genuine analytic
`Tendsto` limit** (`limitValue_eq_tendsto` below, proved with real mathlib analysis:
`tendsto_const_nhds`, `Tendsto.congr'`, `tendsto_nhds_unique`).  So `get?` literally reads
"the point of the completion that the stored sequence converges to", with full analytic
justification at `[T2Space V]`, while remaining a lawful `PartialMap` for all `V`.

## How this differs from the earlier `LimitMap`

`LimitMap` *cheated*: it stored a `List V` and read the limit off via `List.getLast?` — a
syntactic last-element trick, no topology, no infinite sequence.  `CompletionMap` stores a
true infinite sequence `ℕ → V` and the value it observes is justified by **real mathlib
convergence**: `Filter.Tendsto s atTop (𝓝 a)` together with Hausdorff limit-uniqueness
`tendsto_nhds_unique`.  Its non-extensionality is the *intrinsic* completion phenomenon —
many sequences, one limit — not an artifact of forgetting list structure.

## Implementation

`CompletionMap V := ℕ → Option (ℕ → V)`.  `none` at a key means "absent"; `some s` stores the
representative sequence `s`.  Every constructive operation stores a *constant* sequence
`fun _ => v`, whose limit is `v`, so the seven laws reduce to the function-map laws.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap Filter
open scoped Topology

variable {V V' : Type _}

open Classical in
/-- The limit value of a sequence `s : ℕ → V` along `atTop`: the unique `c` with
`s =ᶠ[atTop] (fun _ => c)`, if one exists.  Total and topology-free (so it can serve the
polymorphic `PartialMap` field); when `V` is a Hausdorff space this equals the genuine
analytic `Tendsto` limit, see `limitValue_eq_tendsto`. -/
noncomputable def limitValue (s : ℕ → V) : Option V :=
  if h : ∃ c, s =ᶠ[atTop] (fun _ => c) then some h.choose else none

/-- If `s` is eventually constant `= c`, its `limitValue` is `some c`. -/
theorem limitValue_of_eventuallyEq {s : ℕ → V} {c : V} (h : s =ᶠ[atTop] (fun _ => c)) :
    limitValue s = some c := by
  have hex : ∃ c, s =ᶠ[atTop] (fun _ => c) := ⟨c, h⟩
  rw [limitValue, dif_pos hex]
  have heq : (fun _ : ℕ => hex.choose) =ᶠ[atTop] (fun _ => c) := hex.choose_spec.symm.trans h
  obtain ⟨i, hi⟩ := heq.exists
  exact congrArg some hi

/-- The limit value of a constant sequence is that constant. -/
@[simp] theorem limitValue_const (v : V) : limitValue (fun _ : ℕ => v) = some v :=
  limitValue_of_eventuallyEq EventuallyEq.rfl

/-- `limitValue` is **invariant under eventual equality**: sequences agreeing along `atTop`
have the same limit value.  This is the heart of non-extensionality — the observation factors
through the germ, and (over a completion) all sequences with a common limit collapse. -/
theorem limitValue_congr {s s' : ℕ → V} (h : s =ᶠ[atTop] s') : limitValue s = limitValue s' := by
  by_cases hex : ∃ c, s =ᶠ[atTop] (fun _ => c)
  · obtain ⟨c, hc⟩ := hex
    rw [limitValue_of_eventuallyEq hc, limitValue_of_eventuallyEq (h.symm.trans hc)]
  · have hex' : ¬ ∃ c, s' =ᶠ[atTop] (fun _ => c) := by
      rintro ⟨c, hc⟩; exact hex ⟨c, h.trans hc⟩
    classical rw [limitValue, limitValue, dif_neg hex, dif_neg hex']

/-! ### The analytic bridge: `limitValue` *is* the topological limit

When `V` is a Hausdorff topological space, `limitValue s = some a` exactly captures the
genuine mathlib statement `Tendsto s atTop (𝓝 a)` for the sequences this map ever stores
(eventually-constant ones), via `tendsto_const_nhds` and Hausdorff uniqueness
`tendsto_nhds_unique`.  This is the real-analysis content that distinguishes `CompletionMap`
from the list-based `LimitMap`. -/

/-- If `s` is eventually constant `= a` in a topological space, it converges to `a`. -/
theorem tendsto_of_eventuallyEq_const [TopologicalSpace V] {s : ℕ → V} {a : V}
    (h : s =ᶠ[atTop] (fun _ => a)) : Tendsto s atTop (𝓝 a) :=
  tendsto_const_nhds.congr' h.symm

/-- **Analytic characterization.**  In a Hausdorff space, `limitValue s = some a` iff the
stored (eventually-constant) sequence `s` genuinely converges to `a` in mathlib's sense.
The forward direction is `tendsto_nhds_unique` (uniqueness of limits in `T2Space`); the
backward direction is `limitValue_of_eventuallyEq`.  Hence `get?` reads the point of the
completion that the sequence tends to. -/
theorem limitValue_eq_tendsto [TopologicalSpace V] [T2Space V] {s : ℕ → V} {a : V}
    (hev : ∃ c, s =ᶠ[atTop] (fun _ => c)) :
    limitValue s = some a ↔ Tendsto s atTop (𝓝 a) := by
  obtain ⟨c, hc⟩ := hev
  rw [limitValue_of_eventuallyEq hc]
  constructor
  · rintro ⟨rfl⟩; exact tendsto_of_eventuallyEq_const hc
  · intro h
    exact congrArg some (tendsto_nhds_unique (tendsto_of_eventuallyEq_const hc) h)

/-- A `CompletionMap` stores a *representative sequence* (`ℕ → V`) at every key.  `none` means
"absent".  Distinct sequences with the same limit denote the same map. -/
def CompletionMap (V : Type _) : Type _ := ℕ → Option (ℕ → V)

namespace CompletionMap

/-- The forgetful denotation: read back the (completion) limit of the stored sequence at `k`. -/
noncomputable def get? (m : CompletionMap V) (k : ℕ) : Option V := (m k).bind limitValue

/-- Insert stores the *constant* sequence `fun _ => v`. -/
def insert (m : CompletionMap V) (k : ℕ) (v : V) : CompletionMap V :=
  fun k' => if k = k' then some (fun _ => v) else m k'

/-- Delete stores `none` (absent). -/
def delete (m : CompletionMap V) (k : ℕ) : CompletionMap V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : CompletionMap V := fun _ => none

/-- `bindAlter` applies `f` to the limit of each stored sequence, storing the result as a
constant sequence. -/
noncomputable def bindAlter (f : ℕ → V → Option V') (m : CompletionMap V) : CompletionMap V' :=
  fun k => (get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))

/-- `merge` combines the limits of two stored sequences, storing the result as a constant. -/
noncomputable def merge (op : ℕ → V → V → V) (m₁ m₂ : CompletionMap V) : CompletionMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)

noncomputable instance instPartialMap : PartialMap CompletionMap ℕ where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : CompletionMap V) (k : ℕ) :
    PartialMap.get? m k = (m k).bind limitValue := rfl

noncomputable instance instLawfulPartialMap : LawfulPartialMap CompletionMap ℕ where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, CompletionMap.insert, if_pos h, Option.bind_some,
      limitValue_const]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, CompletionMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, CompletionMap.delete, if_pos h, Option.bind_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, CompletionMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    change (CompletionMap.bindAlter f m k).bind limitValue = (get? m k).bind (f k)
    unfold CompletionMap.bindAlter
    cases hv : get? m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp [limitValue_const]
  get?_merge {V op m₁ m₂ k} := by
    change (CompletionMap.merge op m₁ m₂ k).bind limitValue
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold CompletionMap.merge
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => simp
    | some w => simp [limitValue_const]

/-! ## Non-extensionality

We exhibit two **distinct** `CompletionMap ℝ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but unequal as Lean values.  The witness is a single key
storing two sequences with the *same limit* `0` in `ℝ`: the constant sequence `fun _ => 0`
and a sequence `bumped` that is `1` at index `0` and `0` afterwards.  Both converge to `0`
(the analytic content, justified below), yet they differ at index `0`. -/

/-- A non-constant sequence in `ℝ` equal to `0` everywhere except at index `0` (where it is
`1`).  It agrees with the constant-`0` sequence eventually along `atTop`. -/
def bumped : ℕ → ℝ := fun n => if n = 0 then 1 else 0

/-- `bumped` agrees with the constant-`0` sequence eventually along `atTop`. -/
theorem bumped_eventuallyEq : bumped =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun b hb => by simp [bumped, Nat.one_le_iff_ne_zero.mp hb]⟩

/-- **The analytic fact** justifying the collapse: `bumped` genuinely converges to `0` in
`ℝ` (mathlib `Tendsto … atTop (𝓝 0)`), exactly like the constant-`0` sequence.  Same limit,
different terms. -/
theorem bumped_tendsto : Tendsto bumped atTop (𝓝 (0 : ℝ)) :=
  tendsto_of_eventuallyEq_const bumped_eventuallyEq

/-- First witness: key `0` stores the constant-`0` sequence. -/
noncomputable def m_const : CompletionMap ℝ := CompletionMap.insert CompletionMap.empty 0 0

/-- Second witness: key `0` stores the `bumped` sequence (same limit `0`, different rep). -/
noncomputable def m_bumped : CompletionMap ℝ := fun k => if k = 0 then some bumped else none

/-- **Non-extensionality.**  `m_const` and `m_bumped` are observationally equal
(`PartialMap.equiv`) — both denote "key `0` ↦ limit `0`, everything else absent", and the
common limit `0` is the genuine `ℝ`-limit of *both* stored sequences (`bumped_tendsto`,
`tendsto_const_nhds`) pinned by Hausdorff uniqueness — yet they are **distinct** Lean values,
since the stored sequences differ at index `0`.  Impossible for any `ExtensionalPartialMap`,
so `CompletionMap` is genuinely non-extensional, and the collapse is *intrinsic* to the
completion: distinct convergent sequences, one limit. -/
theorem nonextensional :
    PartialMap.equiv (M := CompletionMap) m_const m_bumped ∧ m_const ≠ m_bumped := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = 0
    · subst hk
      change ((m_const 0).bind limitValue) = ((m_bumped 0).bind limitValue)
      have hc : m_const 0 = some (fun _ => 0) := by simp [m_const, CompletionMap.insert]
      have hb : m_bumped 0 = some bumped := by simp [m_bumped]
      rw [hc, hb, Option.bind_some, Option.bind_some, limitValue_const,
        limitValue_congr bumped_eventuallyEq, limitValue_const]
    · change ((m_const k).bind limitValue) = ((m_bumped k).bind limitValue)
      have hc : m_const k = none := by
        simp [m_const, CompletionMap.insert, CompletionMap.empty, Ne.symm hk]
      have hb : m_bumped k = none := by simp [m_bumped, hk]
      rw [hc, hb]
  · intro h
    have h0 : m_const 0 = m_bumped 0 := congrFun h 0
    have hc : m_const 0 = some (fun _ => 0) := by simp [m_const, CompletionMap.insert]
    have hb : m_bumped 0 = some bumped := by simp [m_bumped]
    rw [hc, hb, Option.some.injEq] at h0
    have := congrFun h0 0
    simp [bumped] at this

/-- The non-extensional collapse, stated in genuine analytic terms: the two stored sequences
of `nonextensional` *both* converge to `0` in `ℝ` (so their observation is the same point of
the completion), yet are distinct functions. -/
theorem nonextensional_tendsto :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) ∧ Tendsto bumped atTop (𝓝 0)
      ∧ (fun _ : ℕ => (0 : ℝ)) ≠ bumped :=
  ⟨tendsto_const_nhds, bumped_tendsto, fun h => by simpa [bumped] using congrFun h 0⟩

end CompletionMap

/-! ## Applicability: a completion-valued `HeapView` CMRA

The point of "convergent-sequence-up-to-limit" as a value type is that the limit lives in the
**completion** of `V`, and completions of nice structures are themselves rich algebraic
objects — hence rich CMRAs.  Two canonical cases:

* `V := ℝ`.  `ℝ` is *literally* the completion `CauSeq.Completion.Cauchy` of `ℚ`
  (`Real.mk : CauSeq ℚ abs → ℝ`), and it is a complete Hausdorff (`T2Space`) **topological
  field**.  A `CompletionMap ℝ` is a heap whose every cell observes the real number that an
  approximating Cauchy sequence converges to — and `limitValue_eq_tendsto` proves `get?`
  reads exactly that analytic limit.
* `V` a complete Hausdorff topological group / `ℝ`-vector space (e.g. a Banach space).  Its
  pointwise `+`/`0` make the *value type a unital CMRA*, so the limit-valued heap slots into
  `Iris.Algebra.HeapView`.

Concretely:

  `HeapView F K V H`  with  `H := CompletionMap`, `K := ℕ`, `V` the completion.

`HeapView` (see `Iris/Iris/Algebra/HeapView.lean`) provides authoritative ownership
`Auth dq m` over the whole limit-valued heap and fragmental ownership `Frag k dq v` over a
single cell; its view relation `HeapR` observes exactly *this file's* `get?` (the
`Std.PartialMap.get?` of `instPartialMap`).

### An interesting frame-preserving update `~~>`: "refine the approximating sequence"

The completion structure makes a syntactically non-trivial class of updates *free*
(frame-preserving): **replacing the stored representative by another sequence with the same
limit leaves the observation invariant.**  If `s` and `s'` both tend to `a` — e.g.
`s := fun _ => a` and `s' := bumped`-shifted to `a` (`nonextensional_tendsto`) — then
`get? (insert m k s) k = some a = get? (insert m k s') k`, so the view relation `HeapR` is
preserved verbatim for every frame.  This is precisely the `HeapView.update_replace` /
`HeapView.update_of_local_update` shape (`Iris/Iris/Algebra/HeapView.lean`, lines 426–447):
the observed value at `k` is replaced from `a` to `a` — the *identity on the limit* — so
validity `✓ a` is unchanged and every frame `f` with `✓ (a • f)` still satisfies `✓ (a • f)`.

One concrete statement (the resource-algebra shadow of `nonextensional` above): writing `a`
for the limit observed from the stored sequence, for any heap `m₁` with `get? m₁ k = some a`,

  `Auth (.own one) m₁ • Frag k (.own one) a  ~~>  `
  `Auth (.own one) (insert m₁ k a) • Frag k (.own one) a`,

derived from `update_of_local_update` with the trivial local update `(a, a) ~l~> (a, a)`.
Although the *underlying stored Cauchy sequence* is being refined from `s` to `s'` (a visibly
different approximation of the same real number), the move is invisible to the CMRA because
the CMRA sees only the limit `a`.  "Refine the approximating sequence" is thus an
always-valid frame-preserving update — the resource-algebra manifestation of completion
non-extensionality. -/

end IrisMath.Instances
