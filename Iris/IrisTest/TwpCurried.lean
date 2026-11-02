/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalWeakestPre

/-! # `twp` without packed arguments

`Iris.ProgramLogic.TotalWeakestPre` defines the total weakest precondition on a tuple of its
arguments, so that it can be compared with the fixpoint of `Iris.BI.Lib.Fixpoint`, which takes one
argument. `ifix` needs no packing: here it is defined on its curried arguments, and shown equal to
the library's. -/

@[expose] public section

namespace IrisTest.TwpCurried
open Iris ProgramLogic Language BI

variable {hlc : HasLC} {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
  {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

/-- The total weakest precondition, recursive in its mask, expression and postcondition. -/
ifix curriedTwp (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  Iris.twp.pre s (curriedTwp s) E e Φ

-- The generated induction principle quantifies over the three arguments separately.
example (s : Stuckness) (Ψ : CoPset → Expr → (Val → IProp GF) → IProp GF) :
    ⊢ (□ ∀ E e Φ, Iris.twp.pre s Ψ E e Φ -∗ Ψ E e Φ) -∗
      ∀ E e Φ, curriedTwp (ι := ι) s E e Φ -∗ Ψ E e Φ :=
  curriedTwp.iter s Ψ

/-- `curriedTwp` is the library's total weakest precondition. -/
theorem curriedTwp_eq (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    curriedTwp (ι := ι) s E e Φ = WP e @ s ; E [{ Φ }] := by
  refine BIBase.BiEntails.to_eq ⟨?_, ?_⟩
  · iintro H
    iapply (curriedTwp.iter s fun E e Φ => iprop(WP e @ s ; E [{ Φ }])) $$ [] H
    iintro !> %E %e %Φ H
    iapply twp.unfold.2 $$ H
  · -- The library's `twp` is its fixpoint on tuples.
    change twp.Internal.getArgs s (E, e, Φ) ⊢ _
    iintro H
    iapply (twp.Internal.getArgs.iter s fun x => curriedTwp s x.1 x.2.1 x.2.2) $$ [] H
    iintro !>
    -- At a tuple, the library's body is `curriedTwp`'s, by definition.
    exact forall_intro fun ⟨E, e, Φ⟩ =>
      wand_intro (emp_sep.1.trans (curriedTwp.unfold_mpr s E e Φ))

end IrisTest.TwpCurried
