/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra
import Iris.Std.HeapInstances

namespace Iris.Examples
open Iris.BI COFE

section Example1

abbrev F0 : OFunctorPre := constOF (Agree (LeibnizO String))

variable {GF} [E0 : ElemG GF F0]

private theorem autoverse : ⊢
    (|==> ∃ (γ : GName), iOwn (F := F0) γ (toAgree ⟨"Paul Durham"⟩) : IProp GF) := by
  istart
  iapply iOwn_alloc
  exact fun _ => trivial

example : ⊢ |==> ∃ (γ0 γ1 : GName) (s0 s1 : String),
    iOwn (E := E0) γ0 (toAgree ⟨s0⟩) ∗
    iOwn (E := E0) γ1 (toAgree ⟨s1⟩) := by
  let v0 : F0.ap (IProp GF) := toAgree ⟨"string0"⟩
  let v1 : F0.ap (IProp GF) := toAgree ⟨"string1"⟩

  -- Allocate the resources
  imod iOwn_alloc v1 (fun _ => trivial) with ⟨%γ1, Hγ1⟩
  imod iOwn_alloc v0 (fun _ => trivial) with ⟨%γ0, Hγ0⟩
  imodintro

  -- Complete the Iris proof
  iexists γ0, γ1, "string0", "string1"
  isplitl [Hγ0]
  · iexact Hγ0
  · iexact Hγ1


end Example1

/-! Example: a typical separating conjunction -/
section Example2

open HeapView One DFrac Agree LeibnizO

/- Parameterize by a type of UFractions. This example also shows how to deal with this
   kind of polymorphism, which can be tricky. -/
variable {F} [UFraction F]

/- Define an OFunctor for the heap. -/
abbrev F1 : OFunctorPre :=
  constOF <| HeapView F Nat (Agree (LeibnizO String)) AssocList

/- Our OFunctor is present in the global list of OFunctors. -/
variable {GF} [ElemG GF (F1 (F := F))]

/- Allow the types of GF and F, and the UFraction instance for F, to be inferred by γ
   alone. Doing it this way allows us to define a notation for the points-to that does not
   require explicit type parameters. Curiously, I don't need to instantiate this; having it
   in the context is enough for typeclass inference to make this shortcut. I sort of doubt
   that we would want to do this globally for ElemG, but I'm not sure about that. -/
set_option synthInstance.checkSynthOrder false in
class abbrev HasPointsToF1 (γ : GName) (GF : outParam _) (F : outParam (Type _))
    [UFraction F] := ElemG GF (F1 (F := F))

/- Define notation for the heap. -/
def points_to (γ : GName) [HasPointsToF1 γ GF F] (k : Nat) (v : String) :=
  iOwn (GF := GF) (F := F1 (F := F)) γ (Frag k (own one) (toAgree ⟨v⟩))

notation k:50 " ↦[" γ:50 "] " v:50 => points_to γ k v

/- In this example, we assume that the setup is complete and a GName has already been
   allocated. -/
example {γ : GName} : 5 ↦[γ] "A" ∗ 5 ↦[γ] "B" ⊢ False := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  iintro %H
  have _ := dist_inj <| toAgree_op_validN_iff_dist.mp <|
    (frag_op_validN_iff.mp H).2
  grind

end Example2

end Iris.Examples
