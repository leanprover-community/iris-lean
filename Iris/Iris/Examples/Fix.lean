/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.COFESolver

@[expose] public section

variable {SI : Type _} [Iris.SIdx SI]

attribute [local instance] Iris.Enriched.COFE.classicalOFunctorTruncatable

/-!
Every OFE is Leibniz, so the fold/unfold isomorphisms of the recursive domain equation solver's
fixed point can be stated as propositional equalities rather than OFE equivalences.
See `Dom.unfold_fold` and `Dom.fold_unfold`.

`DomF` is a concrete example: a domain for a simple language with values, errors,
delayed computations, and function values. Its fixed point `Dom SI V E` satisfies
`Dom SI V E ≅ V ⊕ E ⊕ Later(Dom SI V E) ⊕ Later(Dom SI V E -n>[SI] Dom SI V E)`
up to propositional equality, for any OFEs `V` and `E`, over any step-index type `SI`,
using the classical truncations.

This should provide better support for rewriting by relying on the default Lean
tactics for simplification/rewriting.
-/
section Fix
open Iris OFE COFE

variable [OFE SI Val] [OFE SI Err] [IsCOFE SI Val] [IsCOFE SI Err] [Inhabited Err]

abbrev DomF : OFunctorPre SI :=
  SumOF (constOF Val) (SumOF (constOF Err) (SumOF (LaterOF IdOF) (LaterOF (HomOF IdOF IdOF))))

instance : Inhabited (DomF (SI := SI) (Val := Val) (Err := Err) (ULift Unit) (ULift Unit)) :=
  ⟨.inr (.inr (.inr ⟨id, inferInstance⟩))⟩

end Fix

variable (SI) in
open Iris OFE COFE in
noncomputable abbrev Dom (Val : Type _) (Err : Type _) [OFE SI Val] [OFE SI Err] [IsCOFE SI Val]
    [IsCOFE SI Err] :=
  OFunctor.Fix (DomF (SI := SI) (Val := Val) (Err := Err))

namespace Dom
open Iris OFE COFE

variable [OFE SI V] [OFE SI E] [IsCOFE SI V] [IsCOFE SI E]

noncomputable def fold :
    V ⊕ E ⊕ Later (Dom SI V E) ⊕ Later (Dom SI V E -n>[SI] Dom SI V E) -n>[SI] Dom SI V E :=
  OFunctor.Fix.fold (F := DomF (SI := SI) (Val := V) (Err := E))

noncomputable def unfold :
    Dom SI V E -n>[SI] V ⊕ E ⊕ Later (Dom SI V E) ⊕ Later (Dom SI V E -n>[SI] Dom SI V E) :=
  OFunctor.Fix.unfold (F := DomF (SI := SI) (Val := V) (Err := E))

theorem unfold_fold {x : V ⊕ E ⊕ Later (Dom SI V E) ⊕ Later (Dom SI V E -n>[SI] Dom SI V E)} :
    unfold (fold x) = x :=
  OFunctor.Fix.unfold_fold (F := DomF (SI := SI) (Val := V) (Err := E)) x

theorem fold_unfold {x : Dom SI V E} : fold (unfold x) = x :=
  OFunctor.Fix.fold_unfold (F := DomF (SI := SI) (Val := V) (Err := E)) x

end Dom
