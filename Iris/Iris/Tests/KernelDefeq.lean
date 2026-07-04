/-
Copyright (c) 2026 Sebastian Graf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
-- Deliberately not a `module`: non-module importers ignore module-system
-- annotations such as `@[expose]`, so only `opaque` seals `Tower.iso` for them.
-- This file checks the seal from such an importer. Since `module`s can only
-- import `module`s, it is not listed in `Iris.Tests`; the `IrisTest` glob
-- builds it.
-- module

import Iris.Algebra.COFESolver
import Iris.BI.SIProp

/-!
Regression guard for definitional-equality checks that involve the solver.

The final `example` compares two applications of a step-indexed predicate to values of
a recursive domain built from two nested `OFunctor.Fix` towers; the two sides differ
only by an `id` wrapper. Both the elaborator and the kernel must resolve the difference
by congruence, without reducing through the towers: reduction through the towers is
exponential in the recursion depth of the predicate, and the `maxHeartbeats 4000` cap
turns any reintroduction of it into a deterministic timeout. `Tower.iso` being opaque
is what keeps the kernel out of the towers.

All proofs are `sorry`; only the data matters for kernel reduction.
-/

namespace Iris.Tests.KernelDefeq

open Iris Iris.BI Iris.COFE OFE

set_option linter.unusedVariables false
set_option warn.sorry false

/-! ## Inner tower: `Trace V ≅ V ⊕ ▶(Trace V)` -/

abbrev TraceF (V : Type) [COFE V] : ∀ α β [COFE α] [COFE β], Type :=
  fun _α β _ _ => V ⊕ Later β

instance (V : Type) [COFE V] : Inhabited (TraceF V (ULift Unit) (ULift Unit)) :=
  ⟨Sum.inr (Later.next default)⟩

instance (V : Type) [COFE V] : OFunctorContractive (TraceF V) where
  ofe := inferInstance
  map _f g := Sum.mapO .id (laterMap g)
  map_ne := sorry
  map_id := sorry
  map_comp := sorry
  map_contractive := sorry

abbrev Trace (V : Type) [COFE V] : Type := OFunctor.Fix (TraceF V)

section Map
variable {V₁ V₂ : Type} [COFE V₁] [COFE V₂]
def Trace.fold {V : Type} [COFE V] : TraceF V (Trace V) (Trace V) -n> Trace V :=
  OFunctor.Fix.fold (F := TraceF V)
def Trace.unfold {V : Type} [COFE V] : Trace V -n> TraceF V (Trace V) (Trace V) :=
  OFunctor.Fix.unfold (F := TraceF V)
def Trace.mapPre (h : V₁ -n> V₂) (rec : Trace V₁ -n> Trace V₂) : Trace V₁ -n> Trace V₂ :=
  Trace.fold.comp ((Sum.mapO h (laterMap rec)).comp Trace.unfold)
instance (h : V₁ -n> V₂) : OFE.Contractive (Trace.mapPre h) where
  distLater_dist := sorry
def Trace.map (h : V₁ -n> V₂) : Trace V₁ -n> Trace V₂ :=
  (Function.toContractiveHom (Trace.mapPre h)).fixpoint
end Map

/-! ## Outer tower: `D ≅ Trace (Value D)` -/

abbrev ValueOF : OFunctorPre :=
  SumOF (constOF (LeibnizO Unit)) (HomOF (LaterOF IdOF) (LaterOF IdOF))

abbrev DSig : ∀ α β [COFE α] [COFE β], Type :=
  fun α β _ _ => Trace (ValueOF α β)

instance : OFunctorContractive DSig where
  ofe := inferInstance
  map f g := Trace.map (OFunctor.map (F := ValueOF) f g)
  map_ne := sorry
  map_id := sorry
  map_comp := sorry
  map_contractive := sorry

instance : Inhabited (DSig (ULift Unit) (ULift Unit)) := ⟨default⟩

def D : Type := OFunctor.Fix DSig
instance : COFE D := inferInstanceAs (COFE (OFunctor.Fix DSig))
instance : Inhabited D := inferInstanceAs (Inhabited (OFunctor.Fix DSig))
instance : Inhabited (Later D) := ⟨Later.next default⟩

def D.unfold : D -n> Trace (ValueOF D D) := OFunctor.Fix.unfold (F := DSig)
def D.fold : Trace (ValueOF D D) -n> D := OFunctor.Fix.fold (F := DSig)

abbrev VH : Type := ValueOF D D

def Dinvis (dl : Later D) : D :=
  D.fold (Trace.fold (.inr (laterMap D.unfold dl)))
def Dfn : (D -n> D) -n> D :=
  ⟨fun f => D.fold (Trace.fold (.inl (.inr (laterMap f)))), sorry⟩

/-! ## Step-indexed predicates over the towers -/

def sTrue : SiProp := ⟨fun _ => True, sorry⟩
def sLater (P : SiProp) : SiProp :=
  ⟨fun n => match n with | 0 => True | m+1 => P.holds m, sorry⟩

def value (P : D -n> SiProp) : VH -n> SiProp :=
  ⟨fun v => match v with
      | .inl _ => sTrue
      | .inr g => P (Dinvis (g default)), sorry⟩

def trace.body (Ret : VH -n> SiProp) (rec : Trace VH -n> SiProp) : Trace VH -n> SiProp :=
  (⟨fun x => match x with
      | .inl vμ => Ret vμ
      | .inr tl => sLater (rec tl.car), sorry⟩ :
    TraceF VH (Trace VH) (Trace VH) -n> SiProp).comp Trace.unfold
instance (Ret : VH -n> SiProp) : OFE.Contractive (trace.body Ret) where
  distLater_dist := sorry
def trace (Ret : VH -n> SiProp) : Trace VH -n> SiProp :=
  (Function.toContractiveHom (trace.body Ret)).fixpoint

def Pconst : D -n> SiProp := ⟨fun _ => sTrue, sorry⟩
def P1 : D -n> SiProp := ⟨fun d => trace (value Pconst) (D.unfold d), sorry⟩

set_option maxHeartbeats 4000 in
example (f : D -n> D) :
    (trace (value P1) (D.unfold (id (Dfn f))) : SiProp)
      = trace (value P1) (D.unfold (Dfn f)) := rfl

end Iris.Tests.KernelDefeq
