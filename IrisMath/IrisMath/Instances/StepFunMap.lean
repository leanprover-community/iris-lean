/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Tactic.Linter.Header
public import Iris

/-! # A non-extensional `LawfulPartialMap`: step functions via region partitions

This file builds a `LawfulPartialMap` instance whose carrier is an *intensional* (non-canonical)
representation of a partial **step function** `Ω → Option V`.

## Idea

A step function over a domain `Ω` is represented by a finite term built from `(region, value)`
blocks, evaluated by **first match**: to look up `ω`, scan the blocks and return the value of the
first region containing `ω`.  Regions are *decidable subsets* of `Ω`, encoded as predicates
`Ω → Bool` (so everything stays computable and no `Decidable`/measurability side conditions are
needed for the partial-map laws — see the closing remarks for the measure-theoretic refinement).

This is a direct generalization of the `AssocList` prototype in
`Iris/Iris/Std/HeapInstances.lean`: there, keys are *points* `n : Nat` and every "region" is the
singleton predicate `(· == n)`.  Here regions may be *any* `Ω → Bool`, so a single block can decide
infinitely many keys at once.

## Non-extensionality

Because the term is a *partition representative* rather than the denoted function, many distinct
terms denote the same `Ω → Option V`.  E.g. the single block `[(true-everywhere, v)]` and the
refined partition `[({true}, v), ({false}, v)]` denote the same constant function but are
structurally different terms.  This is made precise in `not_extensional` below: two terms with
`PartialMap.equiv` but `≠`.

## The 7 laws

`get?`/`insert`/`delete`/`bindAlter`/`merge`/`empty` are defined on a small *free* inductive
`StepFun` whose denotation `den : StepFun Ω V → (Ω → Option V)` is first-match lookup.  Each
constructor mirrors exactly one partial-map operation, so every law reduces to unfolding `den`,
mirroring the `AssocList` proof shape but for region keys.  The non-extensional content lives in the
`block` (region prepend) constructor, where redundant/overlapping/refined regions are allowed.
-/

@[expose] public section

namespace IrisMath.StepFunMap

open Iris.Std Iris.Std.PartialMap

/-- A *region* of the domain `Ω`: a decidable subset, encoded as a boolean predicate. -/
abbrev Region (Ω : Type _) := Ω → Bool

/-- Membership of a point in a region. -/
abbrev Region.mem {Ω : Type _} (s : Region Ω) (ω : Ω) : Prop := s ω = true

/-- Intensional representation of a partial step function `Ω → Option V`.

This is a *free* term over the partial-map operations, generalizing `AssocList` from point keys to
region keys.  The denotation `den` (first-match lookup) collapses many terms to the same function,
which is the source of non-extensionality.

* `nil`            — the empty map (`fun _ => none`).
* `block s v rest` — prepend the region/value block `(s, v)`: keys in `s` get `v` (first match),
                     all others fall through to `rest`.  This is the non-canonical partition data.
* `remove s rest`  — prepend a "hole" over region `s`: keys in `s` are deleted, others fall through.
* `alter f rest`   — key-dependent value rewrite `f : Ω → V → Option V'` applied to `rest`.
* `merge op a b`   — pointwise merge of `a` and `b` with `op : Ω → V → V → V`. -/
inductive StepFun (Ω : Type _) : Type _ → Type _ where
  | nil    {V} : StepFun Ω V
  | block  {V} (s : Region Ω) (v : V) (rest : StepFun Ω V) : StepFun Ω V
  | remove {V} (s : Region Ω) (rest : StepFun Ω V) : StepFun Ω V
  | alter  {V V'} (f : Ω → V → Option V') (rest : StepFun Ω V) : StepFun Ω V'
  | merge  {V} (op : Ω → V → V → V) (a b : StepFun Ω V) : StepFun Ω V

namespace StepFun

variable {Ω V V' : Type _}

/-- First-match denotation: scan the term and return the value of the first matching block.

Defined by recursion on the term.  The `alter`/`merge` arms recurse at a possibly *different* value
type, so `den` is genuinely polymorphic-recursive (the recursive call instantiates `V` to the
sub-term's value type). -/
def den : {V : Type _} → StepFun Ω V → Ω → Option V
  | _, .nil,            _ => none
  | _, .block s v rest, ω => if s ω then some v else den rest ω
  | _, .remove s rest,  ω => if s ω then none   else den rest ω
  | _, .alter f rest,   ω => (den rest ω).bind (f ω)
  | _, .merge op a b,   ω => Option.merge (op ω) (den a ω) (den b ω)

@[simp] theorem den_nil (ω : Ω) : den (.nil : StepFun Ω V) ω = none := rfl

@[simp] theorem den_block (s : Region Ω) (v : V) (rest : StepFun Ω V) (ω : Ω) :
    den (.block s v rest) ω = if s ω then some v else den rest ω := rfl

@[simp] theorem den_remove (s : Region Ω) (rest : StepFun Ω V) (ω : Ω) :
    den (.remove s rest) ω = if s ω then none else den rest ω := rfl

@[simp] theorem den_alter (f : Ω → V → Option V') (rest : StepFun Ω V) (ω : Ω) :
    den (.alter f rest) ω = (den rest ω).bind (f ω) := rfl

@[simp] theorem den_merge (op : Ω → V → V → V) (a b : StepFun Ω V) (ω : Ω) :
    den (.merge op a b) ω = Option.merge (op ω) (den a ω) (den b ω) := rfl

end StepFun

section Instance

variable {Ω : Type _} [DecidableEq Ω] {V V' : Type _}

open StepFun

/-- The singleton region `{k}` as a boolean predicate. -/
abbrev singletonR (k : Ω) : Region Ω := fun ω => decide (ω = k)

/-- The partial-map structure on intensional step functions.  Keys are points `ω : Ω`; the map is
the first-match denotation.  `insert`/`delete` prepend a *singleton-region* block/hole, exactly
generalizing the `AssocList` point operations; `bindAlter`/`merge` use the dedicated constructors. -/
instance instPartialMap : PartialMap (StepFun Ω) Ω where
  get? m ω := den m ω
  insert m k v := .block (singletonR k) v m
  delete m k := .remove (singletonR k) m
  empty := .nil
  bindAlter f m := .alter f m
  merge op a b := .merge op a b

@[simp] theorem get?_eq_den (m : StepFun Ω V) (ω : Ω) : get? m ω = den m ω := rfl

instance instLawfulPartialMap : LawfulPartialMap (StepFun Ω) Ω where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    show den (StepFun.block (singletonR k) v m) k' = some v
    simp [StepFun.den_block, singletonR, h]
  get?_insert_ne {V m k k' v} h := by
    show den (StepFun.block (singletonR k) v m) k' = den m k'
    rw [StepFun.den_block, if_neg (by simp [singletonR]; exact fun he => h he.symm)]
  get?_delete_eq {V m k k'} h := by
    show den (StepFun.remove (singletonR k) m) k' = none
    simp [StepFun.den_remove, singletonR, h]
  get?_delete_ne {V m k k'} h := by
    show den (StepFun.remove (singletonR k) m) k' = den m k'
    rw [StepFun.den_remove, if_neg (by simp [singletonR]; exact fun he => h he.symm)]
  get?_bindAlter {V V' k m f} := by
    show den (StepFun.alter f m) k = (den m k).bind (f k)
    simp [StepFun.den_alter]
  get?_merge {V op m₁ m₂ k} := by
    show den (StepFun.merge op m₁ m₂) k = Option.merge (op k) (den m₁ k) (den m₂ k)
    simp [StepFun.den_merge]

end Instance

/-! ## Non-extensionality

Two structurally different terms that denote the *same* partial function.  We work over `Bool`
(two points) so the regions are concrete. -/

section NonExtensional

variable {V : Type _}

/-- One block covering everything with value `v`. -/
def whole (v : V) : StepFun Bool V := .block (fun _ => true) v .nil

/-- A *refined* partition denoting the same constant `v`: split `Bool` into `{true}` and its
complement, both mapped to `v`.  A different term, but the same first-match denotation. -/
def split (v : V) : StepFun Bool V :=
  .block (fun b => b) v (.block (fun b => !b) v .nil)

theorem whole_ne_split (v : V) : whole v ≠ split v := by
  intro h
  -- `whole`'s tail block is `.nil`, `split`'s is a `.block`; extract and contradict.
  have hrest : (StepFun.nil : StepFun Bool V) = .block (fun b => !b) v .nil := by
    injection h
  cases hrest

/-- **Non-extensionality.**  `whole v` and `split v` are equivalent as partial maps (they denote the
same total constant function `fun _ => some v`) yet are not equal terms. -/
theorem not_extensional (v : V) :
    PartialMap.equiv (whole v) (split v) ∧ whole v ≠ split v := by
  refine ⟨?_, whole_ne_split v⟩
  intro b
  simp only [get?_eq_den, whole, split, StepFun.den_block, StepFun.den_nil]
  cases b <;> simp

/-- Consequently the `StepFun` instance is genuinely non-extensional: `equiv` does NOT imply `=`.
(Contrast `ExtensionalPartialMap`, which the function / `ExtTreeMap` instances satisfy.) -/
theorem not_extensionalPartialMap :
    ¬ ∀ {V : Type} {m₁ m₂ : StepFun Bool V}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro h
  obtain ⟨heq, hne⟩ := not_extensional (V := Unit) ()
  exact hne (h heq)

end NonExtensional

/-! ## Applicability: a HeapView CMRA over step functions

The HeapView CMRA (`Iris/Iris/Algebra/HeapView.lean`) is parameterized by *any*
`LawfulPartialMap M K`; its authoritative/fragment construction and frame-preserving updates
(`update_one_alloc`, `update_one_delete`, `update_of_local_update`, ...) are stated purely through
`get?`/`insert`/`delete`/`merge`, never through term equality.  Hence `StepFun Ω` instantiates
`HeapView` directly, giving a heap whose cells are indexed by points `ω : Ω` but whose underlying
storage is a *region partition*.

The new structural content this representation unlocks is **partition refinement that preserves the
denotation, hence the CMRA element**.  Splitting a region into sub-regions, or reordering
non-overlapping blocks, changes the term but not `den`, so it is invisible to every HeapView
operation.  Concretely a region `s = s₁ ∪ s₂` may be *split* into two consecutive blocks
`block s₁ v (block s₂ v m)` with the same denotation — a "split a region / refine the partition"
rewrite that is frame-preserving precisely because every HeapView update is stated through `get?`
(see e.g. `HeapView.update_of_local_update`, whose hypotheses and conclusion only mention
`Std.PartialMap.get?`/`insert`).

The following lemma is the concrete, machine-checked statement: -/

section Applicability

variable {Ω V : Type _} [DecidableEq Ω]

/-- Union of two regions. -/
abbrev Region.union (s₁ s₂ : Region Ω) : Region Ω := fun ω => s₁ ω || s₂ ω

/-- **Refinement is denotation-invariant.**  Splitting a block over `s = s₁ ∪ s₂` into two
consecutive blocks with the *same* value does not change the partial map.  Such a rewrite is
therefore frame-preserving for every HeapView update built on this instance. -/
theorem refine_block_equiv (s₁ s₂ : Region Ω) (v : V) (m : StepFun Ω V) :
    PartialMap.equiv
      (StepFun.block (Region.union s₁ s₂) v m)
      (StepFun.block s₁ v (StepFun.block s₂ v m)) := by
  intro ω
  simp only [get?_eq_den, StepFun.den_block, Region.union]
  by_cases h₁ : s₁ ω = true <;> by_cases h₂ : s₂ ω = true <;> simp_all

end Applicability

end IrisMath.StepFunMap
