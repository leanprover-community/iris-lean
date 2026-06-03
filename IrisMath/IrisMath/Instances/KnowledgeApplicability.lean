/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Tactic.Linter.Header
public import Iris
public import IrisMath.Instances.KnowledgeMap

/-! # End-to-end `HeapView` applicability over the `KnowledgeMap`

`KnowledgeMap` is the most conceptually novel instance: its forgetfulness encodes an *information
order* (a cell stores a set of candidate values; the observation pins it only when the set is a
singleton).  This file makes its applicability a theorem, not prose: it instantiates the generic
Iris `HeapView` over `KnowledgeMap ℕ` and discharges a concrete frame-preserving update.

The `KnowledgeMap` instance requires `[DecidableEq K]`; we take `K := ℕ`, value CMRA `Excl ℕ`,
fractions `PNat`. -/

@[expose] public section

namespace IrisMath.Instances.KnowledgeApplicability

open Iris Iris.Std Iris.Algebra
open IrisMath.Instances

/-- Fractions: positive naturals. -/
abbrev F := PNat
/-- Keys. -/
abbrev K := ℕ
/-- Values: exclusive natural numbers (always valid carrier). -/
abbrev Val := Excl ℕ
/-- The knowledge-state heap container. -/
abbrev H := KnowledgeMap (K := K)

/-- The fully-instantiated heap-view CMRA over the information-ordered `KnowledgeMap`.  Its mere
existence is the applicability fact: the non-extensional knowledge map plugs into the generic Iris
`HeapView` with no extra hypotheses (it needs only `[LawfulPartialMap H K] [CMRA V]`). -/
abbrev HV := HeapView F K Val H

/-- A concrete authoritative+fragment element of the knowledge-heap view. -/
noncomputable example (m : H Val) (k : K) (v : Val) : HV :=
  HeapView.Auth (F := F) (.own 1) m • HeapView.Frag (F := F) (H := H) k (.own 1) v

/-- **Concrete frame-preserving update over the knowledge heap.**

`HeapView.update_replace` specialized to `KnowledgeMap`: from the authoritative heap together with
an exclusive `Excl.excl a` fragment at key `k`, one may replace the value by any `Excl.excl b`.
On the authoritative side, `insert m k (Excl.excl b)` stores the *pinned* knowledge state `{Excl.excl b}`
— so this is the resource-algebra form of "the value at `k` has been determined to be `b`".  Because
`KnowledgeMap` is non-extensional, every pre-update authoritative cell that was *unpinned* (a
non-singleton knowledge state, observed as `none`) is `equiv`-compatible with many representatives;
the update is stated through `get?`, so it sees only the pinned observation. -/
theorem update_replace_concrete (m : H Val) (k : K) (a b : ℕ) :
    HeapView.Auth (F := F) (.own 1) m • HeapView.Frag (F := F) (H := H) k (.own 1) (Excl.excl a)
      ~~> HeapView.Auth (F := F) (.own 1) (Std.PartialMap.insert m k (Excl.excl b))
            • HeapView.Frag (F := F) (H := H) k (.own 1) (Excl.excl b) :=
  HeapView.update_replace (F := F) (H := H) (by trivial)

end IrisMath.Instances.KnowledgeApplicability
