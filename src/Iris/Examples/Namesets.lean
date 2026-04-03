/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProofMode
public import Iris.Algebra.IProp
public import Iris.Algebra.GenSet
public import Iris.Instances.UPred.Instance
public import Iris.Instances.IProp.Instance
public import Iris.Std.GenSetsInstances
public import Iris.Std.CoPset
public import Iris.Std.GenSets

@[expose] public section

namespace Iris.Examples.Set
open Iris.BI COFE Std.LawfulSet Iris.Std GenSetDisj

section sets
-- This section demonstrates an example of using set algebra operations
-- with both namespaces and general sets.

variable {α : Type _} {cmp : α → α → Ordering}
variable [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

-- Concrete set implementation
def SetImpl α cmp := Std.ExtTreeSet α cmp
instance : LawfulSet (SetImpl α cmp) α := inferInstanceAs (LawfulSet (Std.ExtTreeSet α cmp) α)
instance : DecidableDisj (SetImpl α cmp) := inferInstanceAs (DecidableDisj (Std.ExtTreeSet α cmp))

@[simp]
def MySet (S : SetImpl α cmp) : GenSetDisjO (SetImpl α cmp) := GenSetDisj.gen_set_valid S
def SetOwn (S : SetImpl α cmp) : UPred (GenSetDisjO (SetImpl α cmp)) := UPred.ownM (MySet S)

-- Example: Owning overlapping sets leads to a contradiction.
example {x y : α} : SetOwn {x, y} ⊢ (SetOwn ({x} : SetImpl α cmp) -∗ False) := by
  iintro H1 H2
  istop
  apply (UPred.ownM_op _ _).2.trans
  apply (UPred.ownM_valid _).trans
  apply UPred.ownM_always_invalid_elim
  intro n H
  simp only [MySet, ←CMRA.valid_iff_validN', valid_op_iff_disj] at H
  apply H x; grind only [insert_union, mem_union, mem_singleton]

abbrev gname := Pos

@[simp]
def MyCoPSet (S : CoPset) : GenSetDisjO CoPset := GenSetDisj.gen_set_valid S
def CoPSetOwn (S : CoPset) : UPred (GenSetDisjO CoPset) := UPred.ownM (MyCoPSet S)

-- Example: Owning a subset and the full set simultaneously leads to a contradiction.
example {x y : gname} : CoPSetOwn {x, y} ⊢ (CoPSetOwn CoPset.full -∗ False) := by
  iintro H1 H2
  istop
  apply (UPred.ownM_op _ _).2.trans
  apply (UPred.ownM_valid _).trans
  apply UPred.ownM_always_invalid_elim
  intro n H
  simp only [MyCoPSet, ←CMRA.valid_iff_validN', valid_op_iff_disj] at H
  apply H x; grind only [mem_singleton, mem_insert, CoPset.mem_full]

end sets

end Iris.Examples.Set
