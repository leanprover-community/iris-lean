/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.Instances.Lib.Monotone
public meta import Iris.ProofMode

namespace Iris

open Lean Elab Tactic Meta Iris.Std

elab "monotone" : tactic => do
  evalTactic <| ← `(tactic|apply MonotonePred.monotone)
