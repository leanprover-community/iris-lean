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
open Iris.BI COFE Std.LawfulSet Iris.Std

section const_gset

abbrev γ : GType := 1
variable {α : Type _} {cmp : α → α → Ordering}
variable [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

def SetImpl α cmp := Std.ExtTreeSet α cmp
instance : LawfulSet (SetImpl α cmp) α := by simp only [SetImpl]; infer_instance
instance : ∀ X₁ X₂ : SetImpl α cmp, Decidable (X₁ ## X₂) := by simp only [SetImpl]; infer_instance

@[simp]
def MySet (S : SetImpl α cmp) : GenSetDisjO (SetImpl α cmp) := GenSetDisj.gen_set_valid S
def SetOwn (S : SetImpl α cmp) : UPred (GenSetDisjO (SetImpl α cmp)) := UPred.ownM (MySet S)

example {x y : α} : SetOwn {x, y} ⊢ (SetOwn ({x} : SetImpl α cmp) -∗ False) := by
  iintro H1 H2
  istop
  apply (UPred.ownM_op _ _).2.trans
  apply (UPred.ownM_valid _).trans
  apply UPred.ownM_always_invalid_elim
  intro n H
  simp only [MySet, ←CMRA.valid_iff_validN', GenSetDisj.set_disj_valid_op] at H
  apply H x; grind only [insert_union, mem_union, mem_singleton]

end const_gset

end Iris.Examples.Set

namespace Iris.Examples.CoPset
open Iris.BI COFE Std LawfulSet

section const_copset

abbrev γ : GType := 1
abbrev gname := Pos

@[simp]
def MySet (S : CoPset) : GenSetDisjO CoPset := GenSetDisj.gen_set_valid S
def SetOwn (S : CoPset) : UPred (GenSetDisjO CoPset) := UPred.ownM (MySet S)

example {x y : gname} : SetOwn {x, y} ⊢ (SetOwn CoPset.full -∗ False) := by
  iintro H1 H2
  istop
  apply (UPred.ownM_op _ _).2.trans
  apply (UPred.ownM_valid _).trans
  apply UPred.ownM_always_invalid_elim
  intro n H
  simp only [MySet, ←CMRA.valid_iff_validN', GenSetDisj.set_disj_valid_op] at H
  apply H x; grind only [mem_singleton, mem_insert, CoPset.mem_full]

end const_copset

end Iris.Examples.CoPset
