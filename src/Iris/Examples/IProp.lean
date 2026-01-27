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
def points_to (γ : GName) [HasPointsToF1 γ GF F] (k : Nat) (v : String) : IProp GF :=
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

/-! Example: a typical step-indexed weakest precondition -/
section Example3

open OFE

/- In this example, we are given a type of expressions and a type of states, as well as a
   single-stepping function from an operational semantics. -/
class OperationalSemantics (Expr State Value : Type _) where
  step : Expr × State → Expr × State
  to_value : Expr → Option Value
export OperationalSemantics (step to_value)
variable (Expr State Value : Type _) [OperationalSemantics Expr State Value]

/- Let's say that we are also given two OFunctors, and an interpretation of the state into
   state using these resources. -/
variable (F3 F4 : OFunctorPre) [RFunctorContractive F3] [RFunctorContractive F4]
variable {GF} [ElemG GF F3] [ElemG GF F4]
class StateInterpretation (State : Type _) (GF : BundledGFunctors) where
  state_interp : State → IProp GF
export StateInterpretation (state_interp)
variable [StateInterpretation State GF]

/- Again, doing this trick so that we can write WP notations that don't explicitly include
   Expr State and Value. -/
set_option synthInstance.checkSynthOrder false in
class abbrev Ex3WP {Expr : Type _} {State Value : outParam (Type _)} {GF : outParam BundledGFunctors} :=
  OperationalSemantics Expr State Value,
  StateInterpretation State GF

/- Now, we can define a contractive functor for the weakest precondition. -/
def wp_F (wp : Expr → (Value → IProp GF) → IProp GF) (e : Expr) (Φ : Value → IProp GF) :
    IProp GF := iprop(
  (∃ v : Value, ⌜@to_value _ State _ _ e = some v⌝ ∗ |==> Φ v) ∨
  ∀ s, @state_interp State _ _ s -∗
    ∃ e' s', ⌜@step _ _ Value _ (e, s) = (e', s') ⌝ ∗ ▷ |==> (@state_interp _ _ _  s' ∗ wp e' Φ))

instance wp_F_contractive : Contractive (@wp_F Expr State Value _ GF _) where
  distLater_dist {n x y HL} e Φ := by
    refine or_ne.ne (.of_eq rfl) ?_
    refine forall_ne (fun _ => ?_)
    refine wand_ne.ne (.of_eq rfl) ?_
    refine exists_ne (fun v => ?_)
    refine exists_ne (fun _ => ?_)
    refine sep_ne.ne (.of_eq rfl) ?_
    refine Contractive.distLater_dist fun m Hm => ?_
    refine BIUpdate.bupd_ne.ne ?_
    refine sep_ne.ne (.of_eq rfl) ?_
    exact HL m Hm v Φ

def wp {Expr State Value : Type _} [@Ex3WP Expr State Value GF] (e : Expr) (Φ : Value → IProp GF) : IProp GF :=
  (fixpoint <| @wp_F Expr State Value _ GF _) e Φ

theorem wp_unfold (e : Expr) (Φ : Value → IProp GF) :
    wp e Φ ≡ iprop(
        (∃ v : Value, ⌜@to_value _ State _ _ e = some v⌝ ∗ |==> Φ v) ∨
        ∀ s, @state_interp State _ _ s -∗
          ∃ e' s', ⌜@step _ _ Value _ (e, s) = (e', s') ⌝ ∗
          ▷ |==> (@state_interp _ _ _  s' ∗ wp e' Φ)) := by
  apply fixpoint_unfold (f := ⟨(@wp_F Expr State Value _ GF _),
                                @OFE.ne_of_contractive _ _ _ _ (@wp_F Expr State Value _ GF _) _⟩)

/- Now, we can derive some example proof rules. First let's prove a rule for pure deterministic steps: -/
example (e e' : Expr) Φ (Hstep : ∀ {s : State}, @step _ _ Value _ (e, s) = (e', s)) :
    wp e' Φ ⊢ wp e Φ := by
  refine .trans ?_ (equiv_iff.mp (@wp_unfold Expr State Value _ GF _ _ _).symm).mp
  iintro Hspec
  iright
  iintro %s Hs
  iexists e', s
  isplitr
  · ipure_intro
    exact Hstep
  · refine .trans ?_ later_intro      -- FIXME: once iNext is implemented
    refine .trans ?_ BIUpdate.intro   -- FIXME: once iModIntro is implemented
    iintro ⟨Hspec, Hs⟩
    isplitl [Hs]
    · iexact Hs
    · iexact Hspec

/- The pattern of rules for stateful steps, for example, writing to a piece of memory.
   This style of rule applies when ownership over a resource P (eg. k ↦[γ] v) ensures that the state
   can step the expression e to some new expression e', and can be updated to a new resource P'
   in the stepped-to state.
   Then, it suffies to have access to P, and show that access to P' is enough to verify e'. -/
example (e e' : Expr) (P P' : IProp GF) Φ
      (Hstep : ∀ s, iprop(P ∗ @state_interp State GF _ s ⊢ ∃ s',
          ⌜@step _ _ Value _ (e, s) = (e', s')⌝ ∗ |==> (P' ∗ @state_interp State GF _ s'))) :
    P ∗ (P' -∗ wp e' Φ) ⊢ wp e Φ := by
  refine .trans ?_ (equiv_iff.mp (@wp_unfold Expr State Value _ GF _ _ _).symm).mp
  iintro ⟨HP, Hspec⟩
  iright
  iintro %s Hs
  istop -- FIXME: iHave bug?
  refine .trans (sep_mono (sep_mono (wand_intro (Hstep s)) .rfl) .rfl) ?_
  iintro ⟨⟨Hcont, Hspec⟩, HP⟩
  icases Hcont $$ HP with ⟨%s', %Hstep, Hupd⟩
  iexists e', s'
  isplitr
  · ipure_intro; exact Hstep
  refine .trans ?_ later_intro   -- FIXME: once iNext is implemented
  refine .trans bupd_frame_l ?_  -- FIXME: once iMod is implemented
  refine BIUpdate.mono ?_        -- FIXME: once iMod is implemented
  iintro ⟨Hspec, HP', Hs⟩
  isplitl [Hs]
  · iexact Hs
  · iapply Hspec $$ HP'

end Example3

end Iris.Examples
