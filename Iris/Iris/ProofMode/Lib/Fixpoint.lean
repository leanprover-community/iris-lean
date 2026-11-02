/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.ProofMode.Lib.Fixpoint.Lattice
public import Iris.ProofMode.Lib.Fixpoint.Guarded

/-! # Iris fixpoint commands

* `ifix` and `icofix` (`Fixpoint.Lattice`): least and greatest fixpoints of monotone bodies.
* `iguarded` (`Fixpoint.Guarded`): fixpoints of contractive bodies.

`Fixpoint.Tupling` moves the library's lemmas, stated for one argument, to definitions of several,
and `Fixpoint.Common` holds what both share. -/
