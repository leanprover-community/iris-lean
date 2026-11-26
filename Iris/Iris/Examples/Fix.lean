/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.Algebra.COFESolver
public import Iris.Algebra.StepIndexFinite

@[expose] public section

variable {SI : Type _} [Iris.SIdx SI]
local stepindex SI

/-!
Every OFE is Leibniz, so the fold/unfold isomorphisms of the recursive domain equation solver's
fixed point can be stated as propositional equalities rather than OFE equivalences.
See `Dom.unfold_fold` and `Dom.fold_unfold`.

`DomF` is a concrete example: a domain for a simple language with values, errors,
delayed computations, and function values. Its fixed point `Dom V E` satisfies
`Dom V E ≅ V ⊕ E ⊕ Later(Dom V E) ⊕ Later(Dom V E -n> Dom V E)` up to propositional equality,
for any OFEs `V` and `E`, over any step-index type, using the classical truncations.

This should provide better support for rewriting by relying on the default Lean
tactics for simplification/rewriting.

This example also illustrates three ways of using the COFE solver:
using classical truncations, using constructive truncations,
and using the finite step-index type.
For a given locally contractive functor e : F(1, 1), the solver can be called:
- unconditionally classically under classical truncations;
- conditionally constructively if the functor is truncatable;
- unconditionally constructively under finite step-index types.
-/
section Fix
open Iris OFE COFE

variable [OFE Val] [OFE Err] [IsCOFE Val] [IsCOFE Err] [Inhabited Err]

abbrev DomF : OFunctorPre :=
  SumOF (constOF Val) (SumOF (constOF Err) (SumOF (LaterOF IdOF) (LaterOF (HomOF IdOF IdOF))))

instance : Inhabited (DomF (Val := Val) (Err := Err) (ULift Unit) (ULift Unit)) :=
  ⟨.inr (.inr (.inr ⟨id, inferInstance⟩))⟩

end Fix

open Iris OFE COFE Enriched Enriched.COFE in
abbrev Dom (Val : Type _) (Err : Type _) [OFE Val] [OFE Err] [IsCOFE Val] [IsCOFE Err]
    [Inhabited Err] [ETruncatable (oFunctorObj (DomF (Val := Val) (Err := Err)))] :=
  OFunctor.Fix (DomF (Val := Val) (Err := Err))

namespace Dom
open Iris OFE COFE Enriched Enriched.COFE

variable [OFE V] [OFE E] [IsCOFE V] [IsCOFE E] [Inhabited E]
  [ETruncatable (oFunctorObj (DomF (Val := V) (Err := E)))]

def fold : V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E) -n> Dom V E :=
  OFunctor.Fix.fold (F := DomF (Val := V) (Err := E))

def unfold : Dom V E -n> V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E) :=
  OFunctor.Fix.unfold (F := DomF (Val := V) (Err := E))

theorem unfold_fold {x : V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E)} :
    unfold (fold x) = x :=
  OFunctor.Fix.unfold_fold (F := DomF (Val := V) (Err := E)) x

theorem fold_unfold {x : Dom V E} : fold (unfold x) = x :=
  OFunctor.Fix.fold_unfold (F := DomF (Val := V) (Err := E)) x

end Dom

section Classical
open Iris OFE COFE

open Classical in
example [OFE V] [OFE E] [IsCOFE V] [IsCOFE E] [Inhabited E] (x : Dom V E) :
    Dom.fold (Dom.unfold x) = x :=
  Dom.fold_unfold

end Classical

section Constructive
open Iris OFE COFE

example [OFE V] [OFE E] [IsCOFE V] [IsCOFE E] [Inhabited E] [Truncatable V] [Truncatable E]
    (x : Dom V E) : Dom.fold (Dom.unfold x) = x :=
  Dom.fold_unfold

end Constructive

section Nat
open Iris OFE COFE

local stepindex Nat

example [OFE V] [OFE E] [IsCOFE V] [IsCOFE E] [Inhabited E] (x : Dom V E) :
    Dom.fold (Dom.unfold x) = x :=
  Dom.fold_unfold

end Nat
