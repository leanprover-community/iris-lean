/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Algebra.BigOp
import Iris.BI.DerivedLaws
import Iris.Std.FiniteMap
import Iris.Std.FiniteSet

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open OFE
open BIBase

/-! # BI-Instantiated Big Operators over Lists
- `bigSepL`: Big separating conjunction `[∗list]`
- `bigAndL`: Big conjunction `[∧list]`
- `bigOrL`: Big disjunction `[∨list]`
-/

section List
/-! ## Core Definitions -/

/-- Big separating conjunction over a list with index access.
    `bigSepL Φ l` computes `Φ 0 l[0] ∗ Φ 1 l[1] ∗ ... ∗ Φ (n-1) l[n-1]` -/
abbrev bigSepL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL sep emp Φ l

/-- Big conjunction over a list with index access.
    `bigAndL Φ l` computes `Φ 0 l[0] ∧ Φ 1 l[1] ∧ ... ∧ Φ (n-1) l[n-1]` -/
abbrev bigAndL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL and iprop(True) Φ l

/-- Big disjunction over a list with index access.
    `bigOrL Φ l` computes `Φ 0 l[0] ∨ Φ 1 l[1] ∨ ... ∨ Φ (n-1) l[n-1]` -/
abbrev bigOrL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL or iprop(False) Φ l

/-! ## Notation -/

-- Notation for bigSepL without index
syntax atomic("[∗list]") ident " ∈ " term ", " term : term
-- Notation for bigSepL with index
syntax atomic("[∗list]") ident " ↦ " ident " ∈ " term ", " term : term
-- Notation for bigSepL2 without index (two lists)
syntax atomic("[∗list]") ident ";" ident " ∈ " term ";" term ", " term : term
-- Notation for bigSepL2 with index (two lists)
syntax atomic("[∗list]") ident " ↦ " ident ";" ident " ∈ " term ";" term ", " term : term

-- Notation for bigAndL without index
syntax atomic("[∧list]") ident " ∈ " term ", " term : term
-- Notation for bigAndL with index
syntax atomic("[∧list]") ident " ↦ " ident " ∈ " term ", " term : term

-- Notation for bigOrL without index
syntax atomic("[∨list]") ident " ∈ " term ", " term : term
-- Notation for bigOrL with index
syntax atomic("[∨list]") ident " ↦ " ident " ∈ " term ", " term : term

macro_rules
  | `([∗list] $x:ident ∈ $l, $P) => `(bigSepL (fun _ $x => $P) $l)
  | `([∗list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigSepL (fun $k $x => $P) $l)
  | `([∧list] $x:ident ∈ $l, $P) => `(bigAndL (fun _ $x => $P) $l)
  | `([∧list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigAndL (fun $k $x => $P) $l)
  | `([∨list] $x:ident ∈ $l, $P) => `(bigOrL (fun _ $x => $P) $l)
  | `([∨list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigOrL (fun $k $x => $P) $l)

-- iprop macro rules
macro_rules
  | `(iprop([∗list] $x:ident ∈ $l, $P)) => `(bigSepL (fun _ $x => iprop($P)) $l)
  | `(iprop([∗list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigSepL (fun $k $x => iprop($P)) $l)
  | `(iprop([∧list] $x:ident ∈ $l, $P)) => `(bigAndL (fun _ $x => iprop($P)) $l)
  | `(iprop([∧list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigAndL (fun $k $x => iprop($P)) $l)
  | `(iprop([∨list] $x:ident ∈ $l, $P)) => `(bigOrL (fun _ $x => iprop($P)) $l)
  | `(iprop([∨list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigOrL (fun $k $x => iprop($P)) $l)

end List

/-! # BI-Instantiated Big Operators over Maps
- `bigSepM`: Big separating conjunction `[∗map]`
- `bigAndM`: Big conjunction `[∧map]`
-/

section Map
/-! ## Core Definitions -/

/-- Big separating conjunction over a map.
    `bigSepM Φ m` computes `∗_{k ↦ v ∈ m} Φ k v` -/
abbrev bigSepM [BI PROP] {M : Type _ → Type _} {K : Type _} {V : Type _} [FiniteMap K M]
    (Φ : K → V → PROP) (m : M V) : PROP :=
  bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList m)

/-- Big conjunction over a map.
    `bigAndM Φ m` computes `∧_{k ↦ v ∈ m} Φ k v` -/
abbrev bigAndM [BI PROP] {M : Type _ → Type _} {K : Type _} {V : Type _} [FiniteMap K M]
    (Φ : K → V → PROP) (m : M V) : PROP :=
  bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) (toList m)

/-! ## Notation -/

-- Notation for bigSepM without key binding
syntax atomic("[∗map]") ident " ∈ " term ", " term : term
-- Notation for bigSepM with key binding
syntax atomic("[∗map]") ident " ↦ " ident " ∈ " term ", " term : term

-- Notation for bigAndM without key binding
syntax atomic("[∧map]") ident " ∈ " term ", " term : term
-- Notation for bigAndM with key binding
syntax atomic("[∧map]") ident " ↦ " ident " ∈ " term ", " term : term

macro_rules
  | `([∗map] $x:ident ∈ $m, $P) => `(bigSepM (fun _ $x => $P) $m)
  | `([∗map] $k:ident ↦ $x:ident ∈ $m, $P) => `(bigSepM (fun $k $x => $P) $m)
  | `([∧map] $x:ident ∈ $m, $P) => `(bigAndM (fun _ $x => $P) $m)
  | `([∧map] $k:ident ↦ $x:ident ∈ $m, $P) => `(bigAndM (fun $k $x => $P) $m)

-- iprop macro rules
macro_rules
  | `(iprop([∗map] $x:ident ∈ $m, $P)) => `(bigSepM (fun _ $x => iprop($P)) $m)
  | `(iprop([∗map] $k:ident ↦ $x:ident ∈ $m, $P)) => `(bigSepM (fun $k $x => iprop($P)) $m)
  | `(iprop([∧map] $x:ident ∈ $m, $P)) => `(bigAndM (fun _ $x => iprop($P)) $m)
  | `(iprop([∧map] $k:ident ↦ $x:ident ∈ $m, $P)) => `(bigAndM (fun $k $x => iprop($P)) $m)

end Map

/-! # BI-Instantiated Big Operators over Sets
- `bigSepS`: Big separating conjunction `[∗set]`
-/

section Set

/-! ## Core Definitions -/

/-- Big separating conjunction over a set.
    `bigSepS Φ S` computes `∗_{x ∈ S} Φ x`

    Corresponds to `big_opS` in Rocq Iris. -/
abbrev bigSepS [BI PROP] {S : Type _} {A : Type _} [FiniteSet S A]
    (Φ : A → PROP) (s : S) : PROP :=
  bigOpL sep emp (fun _ x => Φ x) (toList s)

/-! ## Notation -/

-- Notation for bigSepS
syntax atomic("[∗set]") ident " ∈ " term ", " term : term

macro_rules
  | `([∗set] $x:ident ∈ $s, $P) => `(bigSepS (fun $x => $P) $s)

-- iprop macro rules
macro_rules
  | `(iprop([∗set] $x:ident ∈ $s, $P)) => `(bigSepS (fun $x => iprop($P)) $s)

end Set

end Iris.BI
