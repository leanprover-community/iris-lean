/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Iris

/-! # `GermMap`: a non-extensional `PartialMap` whose stored payload is a *sequence*

This file defines a `LawfulPartialMap` instance in which each key stores a *sequence*
`ℕ → V` rather than a single value, and the observation `get?` collapses that sequence to
the value of its **germ along `Filter.atTop`** — i.e. its eventual (tail) value.  Two
sequences that agree *eventually along `atTop`* (differ only at finitely many indices)
have the same germ, hence the same denotation, yet are distinct Lean values: the
representation is genuinely **non-extensional**
(two `≠` reps with `PartialMap.equiv`).

## Why this is the "germ / `atTop` quotient" pattern

`Filter.Germ Filter.atTop V` is the quotient of sequences `ℕ → V` by the relation "agree
eventually along `atTop`" (`Filter.EventuallyEq`).  A germ is therefore an equivalence
class of sequences, observing only their *tail behaviour* (sequences modulo finite
modification).  A `GermMap` stores, at every key, an unquotiented *representative*
sequence, and the observation

  `get? : GermMap V → ℕ → Option V`

is a forgetful *denotation*: at each key it reads back the eventual value of the stored
sequence — exactly the data of the germ `(↑s : Germ atTop V)` when that germ is constant.
Two sequences with the same germ (`s =ᶠ[atTop] s'`, e.g. differing only at index `0`)
denote the same map even though `s ≠ s'`.  This mirrors `Filter.Germ.ofFun`, which forgets
the unquotiented representative; many distinct sequences map to the same germ.

This is the measure/filter-theoretic analogue of the `WordMap` "free word" pattern: the
filter `atTop` plays the role of the reduction relation, and `get?` plays the role of the
forgetful quotient map `Germ.ofFun`.

## Implementation

`GermMap V := ℕ → Option (ℕ → V)`.  `none` at a key means "absent"; `some s` stores the
representative sequence `s`.  `get?` returns the *eventual value* `eventualValueAtTop s` of the
stored sequence: the unique `c` with `s =ᶠ[atTop] (fun _ ↦ c)` if one exists.  Every
constructive operation stores a *constant* sequence `fun _ ↦ v`, whose eventual value is
just `v`, so the seven laws reduce to the function-map laws; non-extensionality is then
witnessed by a non-constant sequence with a constant tail.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap Filter

variable {V V' : Type _}

open Classical in
/-- The eventual (tail) value of a sequence along `Filter.atTop`: the unique `c` such that
`s` is eventually equal to the constant sequence `fun _ => c`, if one exists.  This is the
observation of the germ `(↑s : Germ atTop V)` whenever that germ is constant. -/
noncomputable def eventualValueAtTop (s : ℕ → V) : Option V :=
  if h : ∃ c, s =ᶠ[atTop] (fun _ => c) then some h.choose else none

/-- If `s` is eventually constant `= c`, its `eventualValueAtTop` is `some c`. -/
theorem eventualValueAtTop_of_eventuallyEq {s : ℕ → V} {c : V} (h : s =ᶠ[atTop] (fun _ => c)) :
    eventualValueAtTop s = some c := by
  have hex : ∃ c, s =ᶠ[atTop] (fun _ => c) := ⟨c, h⟩
  rw [eventualValueAtTop, dif_pos hex]
  have hspec : s =ᶠ[atTop] (fun _ => hex.choose) := hex.choose_spec
  have heq : (fun _ : ℕ => hex.choose) =ᶠ[atTop] (fun _ => c) := hspec.symm.trans h
  exact congrArg some (const_eventuallyEq.mp heq)

/-- The eventual value of a constant sequence is that constant. -/
@[simp] theorem eventualValueAtTop_const (v : V) : eventualValueAtTop (fun _ : ℕ => v) = some v :=
  eventualValueAtTop_of_eventuallyEq EventuallyEq.rfl

/-- `eventualValueAtTop` is **germ-invariant**: sequences that agree eventually along `atTop`
(equal germs) have the same eventual value.  This is the heart of non-extensionality: the
observation factors through `Germ.ofFun`. -/
theorem eventualValueAtTop_congr {s s' : ℕ → V} (h : s =ᶠ[atTop] s') :
    eventualValueAtTop s = eventualValueAtTop s' := by
  by_cases hex : ∃ c, s =ᶠ[atTop] (fun _ => c)
  · obtain ⟨c, hc⟩ := hex
    rw [eventualValueAtTop_of_eventuallyEq hc, eventualValueAtTop_of_eventuallyEq (h.symm.trans hc)]
  · have hex' : ¬ ∃ c, s' =ᶠ[atTop] (fun _ => c) := by
      rintro ⟨c, hc⟩; exact hex ⟨c, h.trans hc⟩
    classical rw [eventualValueAtTop, eventualValueAtTop, dif_neg hex, dif_neg hex']

/-- The germ-flavoured forgetful denotation `den : GermMap V → (ℕ → Option V)`: read back
the eventual value of the stored sequence at each key. -/
noncomputable def denAtTop (m : ℕ → Option (ℕ → V)) (k : ℕ) : Option V :=
  (m k).bind eventualValueAtTop

/-- A `GermMap` stores a *representative sequence* (`ℕ → V`) at every key.  `none` means
"absent".  Distinct sequences with the same germ along `atTop` denote the same map. -/
def GermMap (V : Type _) : Type _ := ℕ → Option (ℕ → V)

namespace GermMap

/-- The forgetful denotation: read back the eventual (germ-`atTop`) value stored at `k`. -/
noncomputable def get? (m : GermMap V) (k : ℕ) : Option V := denAtTop m k

/-- Insert stores the *constant* sequence `fun _ ↦ v`. -/
def insert (m : GermMap V) (k : ℕ) (v : V) : GermMap V :=
  fun k' => if k = k' then some (fun _ => v) else m k'

/-- Delete stores `none` (absent). -/
def delete (m : GermMap V) (k : ℕ) : GermMap V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : GermMap V := fun _ => none

/-- `bindAlter` applies `f` to the eventual value of each stored sequence, storing the
result as a constant sequence. -/
noncomputable def bindAlter (f : ℕ → V → Option V') (m : GermMap V) : GermMap V' :=
  fun k => (get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))

/-- `merge` combines the eventual values of two stored sequences, storing the result as a
constant sequence. -/
noncomputable def merge (op : ℕ → V → V → V) (m₁ m₂ : GermMap V) : GermMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)

noncomputable instance instPartialMap : PartialMap GermMap ℕ where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : GermMap V) (k : ℕ) :
    PartialMap.get? m k = (m k).bind eventualValueAtTop := rfl

noncomputable instance instLawfulPartialMap : LawfulPartialMap GermMap ℕ where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, GermMap.insert, if_pos h, Option.bind_some,
      eventualValueAtTop_const]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, GermMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, GermMap.delete, if_pos h, Option.bind_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, GermMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (GermMap.bindAlter f m k).bind eventualValueAtTop = (get? m k).bind (f k)
    unfold GermMap.bindAlter
    show ((get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))).bind eventualValueAtTop
      = (get? m k).bind (f k)
    cases hv : get? m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp [eventualValueAtTop_const]
  get?_merge {V op m₁ m₂ k} := by
    show (GermMap.merge op m₁ m₂ k).bind eventualValueAtTop
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold GermMap.merge
    show ((Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)).bind
      eventualValueAtTop = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => simp
    | some w => simp [eventualValueAtTop_const]

/-! ## Non-extensionality

We exhibit two **distinct** `GermMap ℕ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but are not equal as Lean values.  The witness is a
single key storing two sequences with the *same germ* along `atTop`: the constant sequence
`fun _ ↦ 0` and the sequence `bumped` that equals `0` everywhere except at index `0`.
These agree for all `n ≥ 1`, hence `=ᶠ[atTop]`, hence have the same eventual value `0`. -/

/-- A sequence equal to `0` everywhere except at index `0` (where it is `1`).  It agrees
with the constant-`0` sequence eventually along `atTop`. -/
def bumped : ℕ → ℕ := fun n => if n = 0 then 1 else 0

/-- `bumped` agrees with the constant-`0` sequence eventually along `atTop`: they coincide
for all `n ≥ 1`. -/
theorem bumped_eventuallyEq : bumped =ᶠ[atTop] (fun _ => 0) := by
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun b hb => by simp [bumped, Nat.one_le_iff_ne_zero.mp hb]⟩

/-- First witness: key `0` stores the constant-`0` sequence. -/
def m_const : GermMap ℕ := GermMap.insert GermMap.empty 0 0

/-- Second witness: key `0` stores the `bumped` sequence (same germ, different rep). -/
def m_bumped : GermMap ℕ := fun k => if k = 0 then some bumped else none

/-- **Non-extensionality.**  `m_const` and `m_bumped` are observationally equal
(`PartialMap.equiv`) — both denote "key `0` ↦ eventual value `0`, everything else absent" —
yet they are **distinct** Lean values, because the underlying stored sequences
(`fun _ ↦ 0` versus `bumped`) differ at index `0`.  This is impossible for any
`ExtensionalPartialMap`, so `GermMap` is genuinely non-extensional. -/
theorem nonextensional :
    PartialMap.equiv (M := GermMap) m_const m_bumped ∧ m_const ≠ m_bumped := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both give `some 0` at key 0, `none` elsewhere
    by_cases hk : k = 0
    · subst hk
      show ((m_const 0).bind eventualValueAtTop) = ((m_bumped 0).bind eventualValueAtTop)
      have hc : m_const 0 = some (fun _ => 0) := by
        simp [m_const, GermMap.insert]
      have hb : m_bumped 0 = some bumped := by simp [m_bumped]
      rw [hc, hb, Option.bind_some, Option.bind_some,
        eventualValueAtTop_const, eventualValueAtTop_congr bumped_eventuallyEq, eventualValueAtTop_const]
    · show ((m_const k).bind eventualValueAtTop) = ((m_bumped k).bind eventualValueAtTop)
      have hc : m_const k = none := by
        simp [m_const, GermMap.insert, GermMap.empty, Ne.symm hk]
      have hb : m_bumped k = none := by simp [m_bumped, hk]
      rw [hc, hb]
  · -- but distinct as Lean values: evaluate at key 0 and compare stored sequences
    intro h
    have h0 : m_const 0 = m_bumped 0 := congrFun h 0
    have hc : m_const 0 = some (fun _ => 0) := by
      simp [m_const, GermMap.insert]
    have hb : m_bumped 0 = some bumped := by simp [m_bumped]
    rw [hc, hb, Option.some.injEq] at h0
    -- `(fun _ => 0) = bumped` would force agreement at index `0`
    have := congrFun h0 0
    simp [bumped] at this

end GermMap

/-! ## Applicability: the `HeapView` CMRA over germ values

The reason germs are an *interesting* value type is that `Filter.Germ l β` inherits all of
`β`'s pointwise algebra: when `β` is a (commutative) monoid, `Germ l β` is a (commutative)
monoid via `Germ.map₂ (· * ·)` (mathlib: `Filter.Germ.commMonoid`, `Germ.coe_mul`,
`Germ.coe_one`).  Hence `Germ atTop β` is a candidate CMRA value type `V`, and a heap whose
values are germs slots directly into `Iris.Algebra.HeapView`:

  `HeapView F K (Germ atTop β) H`  with  `H := GermMap` (this file) and `K := ℕ`.

`HeapView` provides authoritative ownership `Auth (dq) m` over the whole germ-valued heap
and fragmental ownership `Frag k dq v` over a single germ-valued cell, with the view
relation `HeapR` (this file's `get?` is exactly the `Std.PartialMap.get?` that `HeapR`
observes).

### An interesting frame-preserving update `~~>`

The germ structure makes a class of updates *free* (frame-preserving) that would otherwise
not be: **modifying the representative sequence at finitely many indices leaves the germ
invariant.**  Concretely, if `s =ᶠ[atTop] s'` (they differ at only finitely many points,
e.g. `bumped` vs `fun _ ↦ 0` above), then `(↑s : Germ atTop β) = ↑s'`, so for any frame the
view relation `HeapR` is preserved verbatim:

  `Auth (.own one) m₁ • Frag k (.own one) (↑s)  ~~>  `
  `Auth (.own one) (insert m₁ k (↑s')) • Frag k (.own one) (↑s')`.

This is an instance of `HeapView.update_replace` / `HeapView.update_of_local_update`
(`Iris/Algebra/HeapView.lean`): the value at `k` is replaced from germ `↑s` to germ `↑s'`,
and because `↑s = ↑s'` the *replacement is the identity on germs*, so validity `✓ (↑s')`
holds whenever `✓ (↑s)` did and every frame `f` with `✓ ((↑s) • f)` also satisfies
`✓ ((↑s') • f)`.  In `Iris` terms this is the local update `(↑s, ↑s) ~l~> (↑s, ↑s')` lifted
by `update_of_local_update`; the "finite modification" of the representative is invisible to
the CMRA precisely because the CMRA only sees the germ.  This is the resource-algebra
shadow of the non-extensionality theorem above: distinct representatives, identical
denotation, hence a *trivial* (always-valid) frame-preserving update between them. -/

end IrisMath.Instances
