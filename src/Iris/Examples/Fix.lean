/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.COFESolver

@[expose] public section

section Fix
open Iris OFE COFE

variable [OFE Val] [Leibniz Val] [OFE Err] [Leibniz Err] [IsCOFE Val] [IsCOFE Err] [Inhabited Err]

abbrev DomF : OFunctorPre :=
  SumOF (constOF Val) (SumOF (constOF Err) (SumOF (LaterOF IdOF) (LaterOF (MorOF IdOF IdOF))))

instance : LeibnizPreservingOFunctor (DomF (Val := Val) (Err := Err)) := inferInstance
instance : Inhabited (DomF (Val := Val) (Err := Err) (ULift Unit) (ULift Unit)) := ⟨.inr (.inr (.inr ⟨id, inferInstance⟩))⟩

end Fix

open Iris OFE COFE in
abbrev Dom (Val : Type _) (Err : Type _) [OFE Val] [Leibniz Val] [OFE Err] [Leibniz Err] [IsCOFE Val] [IsCOFE Err] [Inhabited Err] :=
  OFunctor.Fix (DomF (Val := Val) (Err := Err))

namespace Dom
open Iris OFE COFE

variable [OFE V] [Leibniz V] [OFE E] [Leibniz E] [IsCOFE V] [IsCOFE E] [Inhabited E]

instance : OFE (Dom V E) := inferInstance
instance : COFE (Dom V E) := inferInstance

def fold : V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E) -n> Dom V E
  := OFunctor.Fix.fold (F := DomF (Val := V) (Err := E))

def unfold : Dom V E -n> V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E)
  := OFunctor.Fix.unfold (F := DomF (Val := V) (Err := E))

theorem unfold_fold {x : V ⊕ E ⊕ Later (Dom V E) ⊕ Later (Dom V E -n> Dom V E)} : unfold (fold x) = x :=
  eq_of_eqv (OFunctor.Fix.unfold_fold (F := DomF (Val := V) (Err := E)) x)

theorem fold_unfold {x : Dom V E} : fold (unfold x) = x :=
  eq_of_eqv (OFunctor.Fix.fold_unfold (F := DomF (Val := V) (Err := E)) x)

end Dom
