/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Completion
public import Iris

/-! # `LimitMap`: a non-extensional `PartialMap` observing the *limit of a stored net*

This file defines a `LawfulPartialMap` instance in which each key stores a **finite prefix
of a convergent net** — a `List V` whose entries are successive *approximations* of a value
— and the observation `get?` returns the **limit**: the final / converged term of the net,
read off as the *last* element of the stored list (`List.getLast?`).

The empty list `[]` means "absent" (the net has produced no approximation yet); a nonempty
list `[a₀, a₁, …, aₙ]` is read as the approximation sequence whose *converged value* is its
final term `aₙ`.  Two lists with the **same final term** — e.g. `[v]` (already converged) and
`[a₀, a₁, …, v]` (the same limit reached after some pre-convergence approximations) — denote
the same partial map, yet are distinct Lean values.  The representation is therefore
genuinely **non-extensional** (two `≠` reps with `PartialMap.equiv`), and the
non-extensionality is **intrinsic to the container**: the payload (`List V`) is strictly
richer than `Option V`, and `get?` *forgets* the prefix of pre-limit approximations,
retaining only the limit.

## The "store approximations, observe the limit" / completion pattern

The mathematical content is the **completion** picture.  In a complete metric / uniform
space, a Cauchy net is *determined up to its limit*: two Cauchy nets with the same limit are
interchangeable for every observation that factors through the limit map
`UniformSpace.Completion.mk` (mathlib: `UniformSpace.Completion`, `CauSeq.lim`).  A
`LimitMap` stores at each key an *unquotiented finite prefix* of such a net, and

  `get? : LimitMap V → ℕ → Option V`

is the forgetful *denotation* that reads back only the converged term.  This is the discrete
shadow of `UniformSpace.Completion.mk`/`CauSeq.lim`, which forget the unquotiented Cauchy
representative: many prefixes, one limit.

## How this differs from `GermMap` / `WordMap` / `HistoryMap`

* **`GermMap`** observes a *total* sequence `ℕ → V` by its **germ along `atTop`** (its
  *eventual tail value*), and is *partial on the value side*: it accepts **only eventually
  constant** sequences, returning `none` otherwise.  The reduction is "agree eventually"
  (`Filter.EventuallyEq`), which collapses *finite-prefix* differences but is otherwise total
  in time and requires the tail to stabilize to a single value.
* **`LimitMap`** observes a *finite* `List V` by its **last element** (the *converged
  endpoint* of an approximation net), is **total on the value side** (every nonempty list has
  a limit — `getLast?` never fails on a `cons`), and the reduction is "agree on the final
  term", which collapses *initial-prefix* differences (the pre-convergence approximations
  `a₀ … aₙ₋₁`).  Where `GermMap` forgets a *finite head* of an *infinite* sequence and keeps
  the *infinite tail's* eventual value, `LimitMap` forgets the *entire approximation prefix*
  of a *finite* list and keeps the *single final* value.  The two reductions are dual:
  germ = "tail behaviour of an infinite sequence", limit = "endpoint of a finite net".
* Unlike a `WordMap`/`HistoryMap` "free word / dedup" reduction, this reduction inspects **no
  `V`-equality** (no `DecidableEq V`): `getLast?` is purely structural, so the instance is
  fully polymorphic over an arbitrary value type `V`, as required for wave-1.

## Implementation

`LimitMap V := ℕ → List V`.  At each key the list is the stored net prefix (`[]` = absent).
`get? m k := (m k).getLast?` reads the limit.  Every constructive operation stores a
*singleton* net `[v]` (the already-converged value), whose limit is `v`, so the seven laws
reduce to ordinary function-map laws; non-extensionality is witnessed by a *longer* prefix
with the same final term.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

variable {V V' : Type _}

/-- The limit-flavoured forgetful denotation `den : LimitMap V → (ℕ → Option V)`: read back
the converged endpoint (`List.getLast?`) of the stored net prefix at each key.  This is the
discrete analogue of `UniformSpace.Completion.mk` / `CauSeq.lim`: the *prefix of
approximations* is forgotten and only the limit survives. -/
def den (m : ℕ → List V) (k : ℕ) : Option V := (m k).getLast?

/-- A `LimitMap` stores, at every key, a *finite prefix of a convergent net*: a `List V` of
successive approximations.  `[]` means "absent" (no approximation yet).  Distinct prefixes
with the same final term (limit) denote the same map. -/
def LimitMap (V : Type _) : Type _ := ℕ → List V

namespace LimitMap

/-- The forgetful denotation: read back the limit (converged final term) stored at `k`. -/
def get? (m : LimitMap V) (k : ℕ) : Option V := den m k

/-- Insert stores the *already-converged* singleton net `[v]` (limit `v`). -/
def insert (m : LimitMap V) (k : ℕ) (v : V) : LimitMap V :=
  fun k' => if k = k' then [v] else m k'

/-- Delete stores the empty net `[]` (absent). -/
def delete (m : LimitMap V) (k : ℕ) : LimitMap V :=
  fun k' => if k = k' then [] else m k'

/-- The empty map: every key stores the empty net. -/
def empty : LimitMap V := fun _ => []

/-- `bindAlter` applies `f` to the *limit* of each stored net, storing the result as an
already-converged singleton net. -/
def bindAlter (f : ℕ → V → Option V') (m : LimitMap V) : LimitMap V' :=
  fun k => ((get? m k).bind (f k)).toList

/-- `merge` combines the *limits* of two stored nets, storing the result as an
already-converged singleton net. -/
def merge (op : ℕ → V → V → V) (m₁ m₂ : LimitMap V) : LimitMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).toList

instance instPartialMap : PartialMap LimitMap ℕ where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : LimitMap V) (k : ℕ) :
    PartialMap.get? m k = (m k).getLast? := rfl

/-- The limit of an already-converged singleton net `[v]` is `v`. -/
@[simp] theorem getLast?_singleton (v : V) : List.getLast? [v] = some v := rfl

/-- `Option.toList` of an option has the option itself as its `getLast?`. -/
@[simp] theorem getLast?_toList (o : Option V) : (o.toList).getLast? = o := by
  cases o <;> rfl

instance instLawfulPartialMap : LawfulPartialMap LimitMap ℕ where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, LimitMap.insert, if_pos h, getLast?_singleton]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, LimitMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, LimitMap.delete, if_pos h, List.getLast?_nil]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, LimitMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (LimitMap.bindAlter f m k).getLast? = (get? m k).bind (f k)
    simp only [LimitMap.bindAlter, getLast?_toList]
  get?_merge {V op m₁ m₂ k} := by
    show (LimitMap.merge op m₁ m₂ k).getLast? = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    simp only [LimitMap.merge, getLast?_toList]

/-! ## Non-extensionality

We exhibit two **distinct** `LimitMap ℕ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but are not equal as Lean values.  The witness stores,
at a single key, two net prefixes with the **same limit**: the already-converged singleton
`[7]` and a *longer* prefix `[0, 1, 7]` whose pre-convergence approximations `0, 1` are
forgotten by `get?` (only the final term `7` survives).  This is intrinsic: the payload
`List V` is strictly richer than `Option V` and `get?` forgets everything but the endpoint. -/

/-- First witness: key `0` stores the already-converged net `[7]`. -/
def m_short : LimitMap ℕ := LimitMap.insert LimitMap.empty 0 7

/-- Second witness: key `0` stores the longer net prefix `[0, 1, 7]` (same limit `7`). -/
def m_long : LimitMap ℕ := fun k => if k = 0 then [0, 1, 7] else []

/-- **Non-extensionality.**  `m_short` and `m_long` are observationally equal
(`PartialMap.equiv`) — both denote "key `0` ↦ limit `7`, everything else absent" — yet they
are **distinct** Lean values, because the underlying stored net prefixes (`[7]` versus
`[0, 1, 7]`) differ.  This is impossible for any `ExtensionalPartialMap`, so `LimitMap` is
genuinely non-extensional, and intrinsically so: the extra approximations live *in the
container's payload*, not in a ghost-augmented value. -/
theorem nonextensional :
    PartialMap.equiv (M := LimitMap) m_short m_long ∧ m_short ≠ m_long := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both give `some 7` at key 0, `none` elsewhere
    by_cases hk : k = 0
    · subst hk
      show (m_short 0).getLast? = (m_long 0).getLast?
      have hs : m_short 0 = [7] := by simp [m_short, LimitMap.insert]
      have hl : m_long 0 = [0, 1, 7] := by simp [m_long]
      rw [hs, hl]; rfl
    · show (m_short k).getLast? = (m_long k).getLast?
      have hs : m_short k = [] := by simp [m_short, LimitMap.insert, LimitMap.empty, Ne.symm hk]
      have hl : m_long k = [] := by simp [m_long, hk]
      rw [hs, hl]
  · -- but distinct as Lean values: evaluate at key 0 and compare stored net prefixes
    intro h
    have h0 : m_short 0 = m_long 0 := congrFun h 0
    have hs : m_short 0 = [7] := by simp [m_short, LimitMap.insert]
    have hl : m_long 0 = [0, 1, 7] := by simp [m_long]
    rw [hs, hl] at h0
    cases h0

/-- Consequently the `LimitMap` instance is genuinely non-extensional: `equiv` does NOT imply
`=`.  (Contrast `ExtensionalPartialMap`, which the function / `ExtTreeMap` instances
satisfy.) -/
theorem not_extensionalPartialMap :
    ¬ ∀ {V : Type} {m₁ m₂ : LimitMap V}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro h
  obtain ⟨heq, hne⟩ := nonextensional
  exact hne (h heq)

end LimitMap

/-! ## Applicability: a `HeapView` CMRA over "store approximations, observe the limit"

`HeapView` (`Iris/Iris/Algebra/HeapView.lean`) is parameterized by *any*
`LawfulPartialMap M K`; its authoritative ownership `Auth dq m` over the whole heap, the
fragment `Frag k dq v` over a single cell, the view relation `HeapR`, and every
frame-preserving update (`update_one_alloc`, `update_one_delete`, `update_of_local_update`,
`update_replace`, …) are stated purely through `Std.PartialMap.get?`/`insert`/`delete`,
never through representation equality.  Hence `LimitMap` slots directly into

  `HeapView F ℕ V LimitMap`,

a heap whose cells store *net prefixes* but whose CMRA only ever sees the *limit* via `get?`.

### The value CMRA when `V` carries a completion structure

The reason "limits" are an interesting value type is that the completion of a value space is
itself algebraic.  When `β` is, say, a normed group, `UniformSpace.Completion β` is again a
group (mathlib: `UniformSpace.Completion.instAddGroup`, with `Completion.mk` a group
homomorphism via `Completion.coe_add` / `Completion.coe_zero`); likewise `CauSeq.lim` is
additive/multiplicative (`CauSeq.lim_add`, `CauSeq.lim_mul`).  So the *limit type*
`V := UniformSpace.Completion β` (equivalently a `CauSeq`-limit type) is a candidate CMRA
value, and a `LimitMap`-backed heap stores, at each key, a finite prefix of a Cauchy net
*approximating* an element of that completion, while the CMRA element it denotes is the
limit.

### An interesting frame-preserving update `~~>`: *refine an approximation*

The net-prefix structure makes a class of updates **free** (frame-preserving) that would
otherwise be ordinary value updates: **extending the stored prefix by further pre-limit
approximations, while keeping the same final term, leaves the limit — hence the CMRA element
— invariant.**  Concretely, if two prefixes `l` and `l'` share a final term
(`l.getLast? = l'.getLast?`, e.g. `[7]` vs `[0, 1, 7]` above), then `get?` is unchanged at
that key, so for any frame the view relation `HeapR` is preserved verbatim, and the update

  `Auth (.own one) m₁ • Frag k (.own one) v  ~~>`
  `Auth (.own one) (insert m₁ k v) • Frag k (.own one) v`

is an instance of `HeapView.update_replace` (`Iris/Algebra/HeapView.lean`) with `v₂ := v`:
the *replacement is the identity on the observed limit* `v`, so `✓ v` is preserved and every
frame `f` with `✓ (v • f)` still satisfies `✓ (v • f)`.  In `Iris` terms this is the trivial
local update `(v, v) ~l~> (v, v)` lifted by `update_of_local_update`; the "refinement of the
approximation prefix" is invisible to the CMRA precisely because the CMRA only sees the
limit.  This is the resource-algebra shadow of the non-extensionality theorem above: distinct
net prefixes, identical limit, hence a *trivial* (always-valid) frame-preserving update
between them — "you may always refine a stored approximation without disturbing any frame,
because all that is observed is the value it converges to."

The following lemma is the concrete, machine-checked statement of denotation-invariance under
prefix refinement (the property that makes the above update frame-preserving): -/

section Applicability

variable {V : Type _}

/-- **Refinement is limit-invariant.**  Prepending any list of *pre-convergence
approximations* `pre` in front of a net prefix that already ends in `v` does not change the
observed limit at that key.  Such a rewrite is therefore frame-preserving for every
`HeapView` update built on this instance, since each is stated through
`Std.PartialMap.get?`. -/
theorem refine_prefix_equiv (k : ℕ) (pre : List V) (v : V) (m : LimitMap V) :
    PartialMap.equiv
      (LimitMap.insert m k v)
      (fun k' => if k = k' then pre ++ [v] else m k') := by
  intro k'
  simp only [LimitMap.get?_eq]
  by_cases h : k = k' <;>
    simp [LimitMap.insert, h, List.getLast?_append]

end Applicability

end IrisMath.Instances
