/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Tactic.Linter.Header
public import Iris

/-! # `ResidueMap`: a non-extensional `PartialMap` storing polynomial coefficient lists

This file defines a `LawfulPartialMap` instance in which each key stores a *finite
sequence* of values — a "polynomial" `List V` of coefficients, low-degree first — and the
observation `get?` reads back **only the constant (degree-`0`) coefficient**, namely
`List.head?`.  Two coefficient lists that share a head but differ in higher-degree terms
are indistinguishable under `get?`, yet are distinct Lean values: the representation is
genuinely **non-extensional** (two `≠` reps with `PartialMap.equiv`).

## Why this is the "residue mod `(X)`" pattern

Think of the stored list `[a₀, a₁, a₂, …]` as the polynomial `a₀ + a₁·X + a₂·X² + ⋯` in
`R[X]` (with `R := V`).  The observation

  `get? : ResidueMap V → ℕ → Option V`

reads back `a₀`, the **residue of the polynomial modulo the ideal `(X)`** — equivalently
its *evaluation at `0`*, the image under the canonical ring quotient

  `R[X] ⟶ R[X]/(X) ≅ R`,   `p ↦ p mod X = p(0)`.

All higher coefficients (the multiples of `X`) live in the ideal `(X)` and are forgotten by
the observation.  This mirrors `WordMap`'s head/last forgetful quotient, but framed as a
*residue ring* quotient, which gives a richer algebraic applicability story (see the closing
section): when `V` is a commutative ring, adding any element of the ideal `(X)` to a stored
polynomial is invisible to the CMRA built on this map.

## Implementation

`ResidueMap V := ℕ → List V`.  The empty list `[]` at a key means "absent" (`head? = none`);
a nonempty list `a₀ :: rest` means "present with residue `a₀`".  Every constructive
operation stores a *degree-`0`* polynomial (a singleton list `[v]`), whose residue is just
`v`, so the seven laws reduce to the function-map laws; non-extensionality is then witnessed
by a higher-degree polynomial sharing the same constant term.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

variable {V V' : Type _}

/-- A `ResidueMap` stores a *coefficient list* (`List V`, low-degree coefficient first) at
every key.  The empty list `[]` means "absent".  Distinct lists with the same head (same
residue mod `(X)`) denote the same map. -/
def ResidueMap (V : Type _) : Type _ := Nat → List V

namespace ResidueMap

/-- The forgetful denotation: read back the constant (degree-`0`) coefficient stored at `k`,
i.e. the residue of the stored polynomial modulo `(X)`.  This is `List.head?`. -/
def get? (m : ResidueMap V) (k : Nat) : Option V := (m k).head?

/-- Insert stores the *degree-`0`* polynomial `[v]` (the constant `v`). -/
def insert (m : ResidueMap V) (k : Nat) (v : V) : ResidueMap V :=
  fun k' => if k = k' then [v] else m k'

/-- Delete stores the empty list `[]` (absent). -/
def delete (m : ResidueMap V) (k : Nat) : ResidueMap V :=
  fun k' => if k = k' then [] else m k'

/-- The empty map: every key stores `[]`. -/
def empty : ResidueMap V := fun _ => []

/-- `bindAlter` applies `f` to the residue of each stored polynomial, storing the result as a
degree-`0` polynomial. -/
def bindAlter (f : Nat → V → Option V') (m : ResidueMap V) : ResidueMap V' :=
  fun k => ((get? m k).bind (f k)).toList

/-- `merge` combines the residues of two stored polynomials, storing the result as a
degree-`0` polynomial. -/
def merge (op : Nat → V → V → V) (m₁ m₂ : ResidueMap V) : ResidueMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).toList

instance instPartialMap : PartialMap ResidueMap Nat where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : ResidueMap V) (k : Nat) :
    PartialMap.get? m k = (m k).head? := rfl

instance instLawfulPartialMap : LawfulPartialMap ResidueMap Nat where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, ResidueMap.insert, if_pos h, List.head?_cons]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, ResidueMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, ResidueMap.delete, if_pos h, List.head?_nil]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, ResidueMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (ResidueMap.bindAlter f m k).head? = (get? m k).bind (f k)
    unfold ResidueMap.bindAlter
    cases h : (get? m k).bind (f k) <;> simp [Option.toList]
  get?_merge {V op m₁ m₂ k} := by
    show (ResidueMap.merge op m₁ m₂ k).head? = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold ResidueMap.merge
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) <;> simp [Option.toList]

/-! ## Non-extensionality

We exhibit two **distinct** `ResidueMap ℕ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but are not equal as Lean values.  The witness is a
single key storing two coefficient lists with the *same head* (same residue mod `(X)`): the
degree-`0` polynomial `[0]` and the degree-`1` polynomial `[0, 1]` (i.e. `0 + 1·X`).  Both
have head `0`, hence the same residue, yet differ in the `X`-coefficient. -/

/-- First witness: key `0` stores the constant polynomial `[0]` (residue `0`). -/
def m_const : ResidueMap Nat := ResidueMap.insert ResidueMap.empty 0 0

/-- Second witness: key `0` stores `[0, 1]` = `0 + 1·X` (same residue `0`, different rep). -/
def m_higher : ResidueMap Nat := fun k => if k = 0 then [0, 1] else []

/-- **Non-extensionality.**  `m_const` and `m_higher` are observationally equal
(`PartialMap.equiv`) — both denote "key `0` ↦ residue `0`, everything else absent" — yet
they are **distinct** Lean values, because the underlying stored coefficient lists
(`[0]` versus `[0, 1]`) differ in their degree-`1` term.  This is impossible for any
`ExtensionalPartialMap`, so `ResidueMap` is genuinely non-extensional (type-I: the
non-extensionality is intrinsic to the container, since `get?` forgets all but `head?`). -/
theorem nonextensional :
    PartialMap.equiv (M := ResidueMap) m_const m_higher ∧ m_const ≠ m_higher := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both give `some 0` at key 0, `none` elsewhere
    by_cases hk : k = 0
    · subst hk
      show (m_const 0).head? = (m_higher 0).head?
      have hc : m_const 0 = [0] := by simp [m_const, ResidueMap.insert]
      have hh : m_higher 0 = [0, 1] := by simp [m_higher]
      rw [hc, hh]; rfl
    · show (m_const k).head? = (m_higher k).head?
      have hc : m_const k = [] := by
        simp [m_const, ResidueMap.insert, ResidueMap.empty, Ne.symm hk]
      have hh : m_higher k = [] := by simp [m_higher, hk]
      rw [hc, hh]
  · -- but distinct as Lean values: evaluate at key 0 and compare stored lists
    intro h
    have h0 : m_const 0 = m_higher 0 := congrFun h 0
    have hc : m_const 0 = [0] := by simp [m_const, ResidueMap.insert]
    have hh : m_higher 0 = [0, 1] := by simp [m_higher]
    rw [hc, hh] at h0
    cases h0

end ResidueMap

/-! ## Applicability: the `HeapView` CMRA over residue values

The reason this representation is *interesting* is the algebra of the forgotten higher-degree
terms.  Take the value type `V` to be a commutative (semi)ring `R`.  The stored payload at a
key is a polynomial `p = a₀ + a₁·X + a₂·X² + ⋯ ∈ R[X]`, and `get?` observes only its residue
`a₀ = p mod (X) = p(0) ∈ R`.  A heap of `R`-valued cells slots directly into
`Iris.Algebra.HeapView`:

  `HeapView F K R H`   with   `H := ResidueMap` (this file) and `K := ℕ`.

`HeapView` provides authoritative ownership `Auth (dq) m` over the whole `R`-valued heap and
fragmental ownership `Frag k dq v` over a single cell, with the view relation `HeapR`
observing exactly this file's `get?` (= `Std.PartialMap.get?`).

### An interesting frame-preserving update `~~>`

The polynomial structure makes a whole *ideal's worth* of representation changes **free**
(frame-preserving): **adding any multiple of `X` (any element of the ideal `(X)`) to the
stored polynomial leaves the residue — hence the CMRA element — invariant.**  Concretely, if
`p` and `p'` are coefficient lists with the same head `a₀` (so `p' = p + X·q` for some
`q ∈ R[X]`, e.g. `[a₀]` vs `[a₀, c]` adding `c·X`), then `get? = some a₀` for both, so for
any frame the view relation `HeapR` is preserved verbatim:

  `Auth (.own one) m₁ • Frag k (.own one) a₀  ~~>  `
  `Auth (.own one) (insert' m₁ k p') • Frag k (.own one) a₀`,

where `insert'` swaps in the higher-degree representative `p'`.  This is an instance of
`HeapView.update_of_local_update` (`Iris/Algebra/HeapView.lean` 314–495): the *observed*
value at `k` is replaced from `a₀` to `a₀` — the **identity local update**
`(a₀, a₀) ~l~> (a₀, a₀)` — so validity and every frame condition are preserved trivially,
even though the underlying coefficient list changed by an element of `(X)`.  This is the
resource-algebra shadow of the non-extensionality theorem above: distinct representatives
(differing by a multiple of `X`), identical residue, hence a trivial always-valid
frame-preserving update.  It is the algebraically-richer, ideal-flavored analogue of
`OrbitMap`'s `+n` drift: there the invisible move is a shift; here it is *addition of any
element of the ideal `(X)`*, a genuinely ring-theoretic redundancy. -/

end IrisMath.Instances
