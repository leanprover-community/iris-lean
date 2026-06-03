/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Iris
public import IrisMath.Instances.ConstOnFilterMap

/-! # End-to-end `HeapView` applicability over a non-extensional map

The other instance files *sketch* the `HeapView` CMRA and its `~~>` updates.  This file makes the
applicability concrete: it actually instantiates the generic `Iris.HeapView` resource algebra over
the non-extensional `ConstOnFilterMap (atTop) ℕ` and exports a real, type-checked frame-preserving
update — the `update_replace` rule specialized to our map, with `PNat` fractions and `Excl`-valued
cells.

The significance: the generic Iris construction `instStoreCMRA` (`Iris/Algebra/Heap.lean`) and the
whole `HeapView` tower (`Iris/Algebra/HeapView.lean`) require only `[LawfulPartialMap H K] [CMRA V]`.
Since `ConstOnFilterMap atTop ℕ` *is* a `LawfulPartialMap` (proved in `ConstOnFilterMap.lean`), the
entire CMRA + view machinery applies to it for free.  We confirm that here by naming the resulting
type and discharging a concrete update obligation.
-/

@[expose] public section

namespace IrisMath.Instances.HeapViewApplicability

open Iris Iris.Std Iris.Algebra
open scoped Filter
open IrisMath.Instances

/-- The fraction monoid: positive naturals, the simplest `UFraction`. -/
abbrev F := PNat

/-- The key type. -/
abbrev K := ℕ

/-- The value CMRA: exclusive ownership of a natural number.  `Excl.excl n` is always valid, so it
is the cleanest carrier for demonstrating the replace update. -/
abbrev Val := Excl ℕ

/-- The heap container: the non-extensional "eventually-constant along `atTop`" map.  This is the
`GermMap` underlying type, viewed through the general `ConstOnFilterMap` construction. -/
abbrev H := ConstOnFilterMap (Filter.atTop (α := ℕ)) K

/-- The fully-instantiated heap-view CMRA over our non-extensional map.  Its mere existence (it
type-checks) is the core applicability fact: a non-extensional `LawfulPartialMap` plugs into the
generic Iris `HeapView` with no extra hypotheses. -/
abbrev HV := HeapView F K Val H

/-- A concrete authoritative+fragment configuration is a well-formed element of `HV`. -/
noncomputable example (m : H Val) (k : K) (v : Val) : HV :=
  HeapView.Auth (F := F) (.own 1) m • HeapView.Frag (F := F) (H := H) k (.own 1) v

/-- **Concrete frame-preserving update over the non-extensional heap.**

This is `HeapView.update_replace` instantiated at our map, fractions, and value CMRA: owning the
authoritative heap `m` together with the exclusive fragment `Excl.excl a` at key `k`, one may
replace the value by any other `Excl.excl b` (always valid), updating both the authoritative heap
and the fragment.

Because the heap `H` is *non-extensional*, the authoritative side `insert m k (Excl.excl b)` may be
realized by many different stored representatives (sequences that are `atTop`-eventually
`Excl.excl b`); the update holds for all of them uniformly, since the view relation `HeapR` sees the
heap only through `get?`.  This is the resource-algebra payoff of non-extensionality made concrete
and machine-checked. -/
theorem update_replace_concrete (m : H Val) (k : K) (a b : ℕ) :
    HeapView.Auth (F := F) (.own 1) m • HeapView.Frag (F := F) (H := H) k (.own 1) (Excl.excl a)
      ~~> HeapView.Auth (F := F) (.own 1) (Std.PartialMap.insert m k (Excl.excl b))
            • HeapView.Frag (F := F) (H := H) k (.own 1) (Excl.excl b) :=
  HeapView.update_replace (F := F) (H := H) (by trivial)

end IrisMath.Instances.HeapViewApplicability
