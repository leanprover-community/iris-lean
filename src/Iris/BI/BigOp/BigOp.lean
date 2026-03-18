/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.Monoid
public import Iris.Algebra.BigOp
public import Iris.BI.DerivedLaws
import Lean

namespace Iris.BI

public section List
open Iris.Algebra Iris.Std OFE BIBase


/-! ## MonoidOps instances for BI connectives -/

instance sepMonoidOps [BI PROP] : MonoidOps (sep (PROP := PROP)) emp where
  op_ne := BI.sep_ne
  op_assoc := equiv_iff.mpr sep_assoc
  op_comm := equiv_iff.mpr sep_comm
  op_left_id := equiv_iff.mpr emp_sep

instance andMonoidOps [BI PROP] : MonoidOps (and (PROP := PROP)) iprop(True) where
  op_ne := BI.and_ne
  op_assoc := equiv_iff.mpr and_assoc
  op_comm := equiv_iff.mpr and_comm
  op_left_id := equiv_iff.mpr true_and

instance orMonoidOps [BI PROP] : MonoidOps (or (PROP := PROP)) iprop(False) where
  op_ne := BI.or_ne
  op_assoc := equiv_iff.mpr or_assoc
  op_comm := equiv_iff.mpr or_comm
  op_left_id := equiv_iff.mpr false_or

/-! ## Homomorphism helpers for OFE equivalence -/

/-- Build a `MonoidHomomorphism` for OFE equivalence from just the essential fields. -/
@[expose] def MonoidHomomorphism.ofEquiv [OFE PROP] {op₁ op₂ : PROP → PROP → PROP}
    {u₁ u₂ : PROP} [MonoidOps op₁ u₁] [MonoidOps op₂ u₂] {f : PROP → PROP}
    (hne : NonExpansive f) (hop : ∀ {x y}, f (op₁ x y) ≡ op₂ (f x) (f y))
    (hunit : f u₁ ≡ u₂) : MonoidHomomorphism op₁ op₂ u₁ u₂ (· ≡ ·) f where
  rel_refl := .rfl
  rel_trans := .trans
  rel_proper ha hb := ⟨fun h => ha.symm.trans (h.trans hb), fun h => ha.trans (h.trans hb.symm)⟩
  op_proper ha hb := MonoidOps.op_proper ha hb
  map_ne := hne
  map_op := hop
  map_unit := hunit

/-- Build a `WeakMonoidHomomorphism` for OFE equivalence from just the essential fields. -/
@[expose] def WeakMonoidHomomorphism.ofEquiv [OFE PROP] {op₁ op₂ : PROP → PROP → PROP}
    {u₁ u₂ : PROP} [MonoidOps op₁ u₁] [MonoidOps op₂ u₂] {f : PROP → PROP}
    (hne : NonExpansive f) (hop : ∀ {x y}, f (op₁ x y) ≡ op₂ (f x) (f y)) :
    WeakMonoidHomomorphism op₁ op₂ u₁ u₂ (· ≡ ·) f where
  rel_refl := .rfl
  rel_trans := .trans
  rel_proper ha hb := ⟨fun h => ha.symm.trans (h.trans hb), fun h => ha.trans (h.trans hb.symm)⟩
  op_proper ha hb := MonoidOps.op_proper ha hb
  map_ne := hne
  map_op := hop

/-- Big separating conjunction over a list with index access. -/
abbrev bigSepL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL sep Φ l

/-- Big conjunction over a list with index access. -/
abbrev bigAndL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL and Φ l

/-- Big disjunction over a list with index access. -/
abbrev bigOrL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL or Φ l

end List

public meta section
open Lean PrettyPrinter Delaborator SubExpr
/-! ## Notation -/

-- Notation for bigSepL without index
syntax "[∗list] " ident " ∈ " term ", " term : term
-- Notation for bigSepL with index
syntax "[∗list] " ident " ↦ " ident " ∈ " term ", " term : term
-- Notation for bigSepL2 without index
syntax "[∗list] " ident ";" ident " ∈ " term ";" term ", " term : term
-- Notation for bigSepL2 with index
syntax "[∗list] " ident " ↦ " ident ";" ident " ∈ " term ";" term ", " term : term

-- Notation for bigAndL without index
syntax "[∧list] " ident " ∈ " term ", " term : term
-- Notation for bigAndL with index
syntax "[∧list] " ident " ↦ " ident " ∈ " term ", " term : term

-- Notation for bigOrL without index
syntax "[∨list] " ident " ∈ " term ", " term : term
-- Notation for bigOrL with index
syntax "[∨list] " ident " ↦ " ident " ∈ " term ", " term : term

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

/-- Delaborator for `bigSepL` with index -/
@[delab app.Iris.BI.bigSepL]
def delabBigSepL : Delab := do
  let e ← getExpr
  unless e.isApp do failure
  unless e.getAppFn.isConstOf ``bigSepL do failure

  let args := e.getAppArgs
  unless args.size == 5 do failure
  let l ← withNaryArg 4 delab
  let fn := args[3]!

  match fn with
  | .lam xn _ body _ =>
    match body with
    | .lam yn _ fnBody _ =>
      -- Check if index variable is used
      let xUsed := fnBody.hasLooseBVar 1
      let y := mkIdent yn
      let P ← withNaryArg 3 <| withBindingBody yn <| withBindingBody xn <| delab

      if xUsed then
        let x := mkIdent xn
        `([∗list]  $x ↦ $y ∈ $l, $P)
      else
        `([∗list]  $y ∈ $l, $P)
    | _ =>
      -- Single-parameter lambda: fun n => Φ (n + 1) where Φ : Nat → A → PROP
      -- Show it with both index and element variable
      let k := mkIdent xn
      let x := mkIdent `x
      let P ← withNaryArg 3 <| withBindingBody xn <| delab
      `([∗list]  $k ↦ $x ∈ $l, $P $x)
  | _ => failure

/-- Delaborator for `bigAndL` with index -/
@[delab app.Iris.BI.bigAndL]
def delabBigAndL : Delab := do
  let e ← getExpr
  unless e.isApp do failure
  unless e.getAppFn.isConstOf ``bigAndL do failure
  let args := e.getAppArgs
  unless args.size == 5 do failure
  let l ← withNaryArg 4 delab
  let fn := args[3]!
  match fn with
  | .lam xn _ body _ =>
    match body with
    | .lam yn _ fnBody _ =>
      let xUsed := fnBody.hasLooseBVar 1
      let y := mkIdent yn
      let P ← withNaryArg 3 <| withBindingBody yn <| withBindingBody xn <| delab
      if xUsed then
        let x := mkIdent xn
        `([∧list]  $x ↦ $y ∈ $l, $P)
      else
        `([∧list]  $y ∈ $l, $P)
    | _ =>
      let k := mkIdent xn
      let x := mkIdent `x
      let P ← withNaryArg 3 <| withBindingBody xn <| delab
      `([∧list]  $k ↦ $x ∈ $l, $P $x)
  | _ => failure

/-- Delaborator for `bigOrL` with index -/
@[delab app.Iris.BI.bigOrL]
def delabBigOrL : Delab := do
  let e ← getExpr
  unless e.isApp do failure
  unless e.getAppFn.isConstOf ``bigOrL do failure
  let args := e.getAppArgs
  unless args.size == 5 do failure
  let l ← withNaryArg 4 delab
  let fn := args[3]!
  match fn with
  | .lam xn _ body _ =>
    match body with
    | .lam yn _ fnBody _ =>
      let xUsed := fnBody.hasLooseBVar 1
      let y := mkIdent yn
      let P ← withNaryArg 3 <| withBindingBody yn <| withBindingBody xn <| delab
      if xUsed then
        let x := mkIdent xn
        `([∨list]  $x ↦ $y ∈ $l, $P)
      else
        `([∨list]  $y ∈ $l, $P)
    | _ =>
      let k := mkIdent xn
      let x := mkIdent `x
      let P ← withNaryArg 3 <| withBindingBody xn <| delab
      `([∨list]  $k ↦ $x ∈ $l, $P $x)
  | _ => failure

end

end Iris.BI
