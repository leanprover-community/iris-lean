/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.COFESolver

@[expose] public section

/-!
This example shows that for Leibniz-preserving functors, which include but not limited to
those built from the combinators in `OFE.lean`, the Leibniz property propagates through the
recursive domain equation solver. As a result, the fold/unfold isomorphisms of the
fixed point can be stated as propositional equalities (`=`) rather than mere OFE
equivalences (`≡`); see `Dom.unfold_fold` and `Dom.fold_unfold`.

`DomF` is a concrete example: a domain for a simple language with values, errors,
delayed computations, and function values. Its fixed point `Dom V E` satisfies
`Dom V E ≅ V ⊕ E ⊕ Later(Dom V E) ⊕ Later(Dom V E -n> Dom V E)` propositionally,
provided `V` and `E` are Leibniz OFEs.

For examples, where it holds, it should provide better support for rewriting
by relying on the default Lean tactics.
-/
section Fix
open Iris OFE COFE

variable [OFE Val] [OFE Err] [IsCOFE Val] [IsCOFE Err] [Inhabited Err]

abbrev DomF : OFunctorPre :=
  SumOF (constOF Val) (SumOF (constOF Err) (SumOF (LaterOF IdOF) (LaterOF (HomOF IdOF IdOF))))

instance : Inhabited (DomF (Val := Val) (Err := Err) (ULift Unit) (ULift Unit)) :=
  ⟨.inr (.inr (.inr ⟨id, inferInstance⟩))⟩

end Fix

open Iris OFE COFE in
abbrev Dom (Val : Type _) (Err : Type _) [OFE Val] [OFE Err] [IsCOFE Val] [IsCOFE Err] [Inhabited Err] :=
  OFunctor.Fix (DomF (Val := Val) (Err := Err))

namespace Dom
open Iris OFE COFE

variable [OFE V] [Leibniz V] [OFE E] [Leibniz E] [IsCOFE V] [IsCOFE E] [Inhabited E]

def fold : V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E) -n> Dom V E :=
  OFunctor.Fix.fold (F := DomF (Val := V) (Err := E))

def unfold : Dom V E -n> V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E) :=
  OFunctor.Fix.unfold (F := DomF (Val := V) (Err := E))

theorem unfold_fold {x : V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E)} :
    unfold (fold x) = x :=
  eq_of_eqv (OFunctor.Fix.unfold_fold (F := DomF (Val := V) (Err := E)) x)

theorem fold_unfold {x : Dom V E} : fold (unfold x) = x :=
  eq_of_eqv (OFunctor.Fix.fold_unfold (F := DomF (Val := V) (Err := E)) x)

end Dom
