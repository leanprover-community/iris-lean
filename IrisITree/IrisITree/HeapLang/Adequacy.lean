/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import IrisITree.Core.Handler
public import IrisITree.Core.WpiExec
public import IrisITree.HeapLang.ProgramLogic

@[expose] public section

namespace IrisITree

open Iris BI Iris.HeapLang ITree ITree.Effects ITree.Exec

section handler

variable {GF : BundledGFunctors} [InvGS GF] [heaplangHGS GF]

theorem test : sorry := by sorry


end handler

end IrisITree
