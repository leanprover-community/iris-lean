/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/

import Iris.Std.CoPset
import Iris.Std.DelabRule
import Init.Data.Char.Lemmas

/-! # Namespaces for Invariants

Reference: `stdpp/theories/namespaces.v`

Invariants are organized into a hierarchical namespace tree. Each namespace maps
to a mask (`CoPset`) via `nclose`, which collects all invariant names that have
the namespace as a suffix. This gives two key properties:

1. **Nesting**: extending a namespace (`ndot`) yields a subset of the parent mask,
   so opening a child namespace leaves the parent's other children accessible.
2. **Disjointness**: sibling namespaces (same parent, different extension component)
   produce disjoint masks, preventing conflicts when multiple invariants are open.

## Main Definitions

- `Namespace` — namespace type (list of encoded name components)
- `nroot` — root namespace (covers all names)
- `ndot` / `.@` — extend a namespace with a countable value
- `nclose` / `↑N` — map a namespace to its invariant mask
-/

namespace Iris
open Iris.Std

/-! ## Countable Encodings -/

/-- A lightweight countable encoding into name components. -/
class Countable (A : Type _) where
  /-- Encode a value into a name component. -/
  encode : A → NameComponent
  /-- Decode a name component back into a value. -/
  decode : NameComponent → Option A
  /-- Decoding after encoding returns the original value. -/
  decode_encode : ∀ a, decode (encode a) = some a

/-- Encode is injective thanks to the left inverse. -/
theorem Countable.encode_inj {A : Type _} [Countable A] {x y : A}
    (h : Countable.encode x = Countable.encode y) : x = y := by
  -- apply decode to the equality and simplify
  have h' := congrArg (Countable.decode (A := A)) h
  simpa [Countable.decode_encode] using h'

/-- `Nat` encodes as a singleton component. -/
instance : Countable Nat where
  encode n := [n]
  decode xs :=
    -- singleton lists decode to their element
    match xs with
    | [n] => some n
    | _ => none
  decode_encode := by
    -- decoding the singleton yields the original number
    intro n; rfl

/-- `String` encodes as a list of character codes. -/
instance : Countable String where
  encode s :=
    -- map characters to their numeric codes
    s.toList.map Char.toNat
  decode xs :=
    -- rebuild the string from character codes
    some (String.ofList (xs.map Char.ofNat))
  decode_encode := by
    -- mapping `Char.ofNat` after `Char.toNat` recovers the characters
    intro s
    -- reduce to the corresponding statement without `Option.some`
    apply congrArg some
    have hmap : List.map (Char.ofNat ∘ Char.toNat) s.toList = s.toList := by
      -- map `ofNat ∘ toNat` collapses to the identity, by list induction
      induction s.toList with
      | nil => simp
      | cons _ _ ih =>
        simp [ih]
    -- combine the map identity with `String.ofList_toList`
    calc
      String.ofList (List.map Char.ofNat (List.map Char.toNat s.toList))
          = String.ofList (List.map (Char.ofNat ∘ Char.toNat) s.toList) := by
            -- reassociate the nested map
            simp [List.map_map]
      _ = String.ofList s.toList := by
            -- apply the map identity from `hmap`
            simp [hmap]
      _ = s := by
            -- fold back to the original string
            simp [String.ofList_toList]

/-! ## Namespace Structure -/

/-- Namespaces are lists of name components. -/
structure Namespace where
  /-- Namespace components, ordered from most-specific to root. -/
  parts : List NameComponent

/-- Root namespace (no components). -/
def nroot : Namespace := by
  -- empty namespace list
  exact ⟨[]⟩

/-- Extend a namespace with a new component. -/
def ndot {A : Type _} [Countable A] (N : Namespace) (x : A) : Namespace := by
  -- cons the encoded component at the front
  exact ⟨Countable.encode x :: N.parts⟩

/-- Map a namespace to its mask: all names with the namespace as a suffix. -/
def nclose (N : Namespace) : CoPset := by
  -- suffix predicate on lists of components
  exact ⟨fun p => N.parts <:+ p⟩

instance : Coe Namespace CoPset := ⟨nclose⟩

/-! ## Notation -/

syntax term " .@ " term : term
macro_rules
  | `($N .@ $x) => `(ndot $N $x)

delab_rule nclose
  | `($_ $N) => do
      -- show namespace coercions as `↑N`
      `(↑$N)

/-! ## Namespace Lemmas -/

/-- Helper: dropping the prefix returns the suffix. -/
private theorem drop_append_left {α : Type _} (t s : List α) :
    List.drop t.length (t ++ s) = s := by
  -- prove by induction on the prefix
  induction t with
  | nil => simp
  | cons _ t ih =>
      simp [ih]

/-- Helper: if `x::N` is a suffix of `p`, then `N` is also a suffix of `p`. -/
private theorem suffix_tail {x : NameComponent} {N p : List NameComponent}
    (h : x :: N <:+ p) : N <:+ p := by
  -- extend the witness by one element
  rcases h with ⟨t, rfl⟩
  refine ⟨t ++ [x], ?_⟩
  simp [List.append_assoc]

/-- Helper: equal-length suffixes with the same tail have equal heads. -/
private theorem suffix_cons_eq {x y : NameComponent} {N p : List NameComponent}
    (hx : x :: N <:+ p) (hy : y :: N <:+ p) : x = y := by
  -- unpack both suffix witnesses and compare the drop at equal lengths
  rcases hx with ⟨t1, rfl⟩
  rcases hy with ⟨t2, h2⟩
  have hlen : t1.length = t2.length := by
    -- lengths agree because the suffixes have equal length
    have := congrArg List.length h2
    simp [List.length_append, List.length_cons] at this
    exact this.symm
  have hdrop := congrArg (List.drop t1.length) h2
  -- simplify both sides to the suffixes
  simp [hlen] at hdrop
  -- conclude by head equality
  cases hdrop; rfl

/-- The root namespace covers all names. -/
theorem nclose_nroot : (↑nroot : CoPset) = (CoPset.top : CoPset) := by
  -- suffix of the empty list is always true
  ext p; constructor <;> intro _
  · trivial
  · refine ⟨p, ?_⟩
    -- suffix witness by appending the empty list
    simp [nroot]

/-- Extending a namespace yields a subset of the original mask. -/
theorem nclose_subseteq {A : Type _} [Countable A] (N : Namespace) (x : A) :
    (↑(N .@ x) : CoPset) ⊆ ↑N := by
  -- drop the added head from the suffix witness
  intro p hp
  exact suffix_tail hp

/-- Subset transport for namespace masks. -/
theorem nclose_subseteq' {A : Type _} [Countable A] {E : CoPset} (N : Namespace) (x : A) :
    (↑N : CoPset) ⊆ E → (↑(N .@ x) : CoPset) ⊆ E := by
  -- compose subset with `nclose_subseteq`
  intro h
  exact fun p hp => h _ (nclose_subseteq N x p hp)

/-- Distinct components yield disjoint namespaces. -/
theorem ndot_ne_disjoint {A : Type _} [Countable A]
    (N : Namespace) {x y : A} (hxy : x ≠ y) :
    CoPset.Disjoint (↑(N .@ x)) (↑(N .@ y)) := by
  -- a shared suffix forces the head components to coincide
  intro p hp
  rcases hp with ⟨hx, hy⟩
  have hcomp : Countable.encode x = Countable.encode y := suffix_cons_eq hx hy
  exact hxy (Countable.encode_inj hcomp)

end Iris
