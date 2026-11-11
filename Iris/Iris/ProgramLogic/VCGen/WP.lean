/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.ProgramLogic.VCGen.Lattice
public import Iris.ProgramLogic.WeakestPre

@[expose] public section

/-!
# The iris weakest precondition as a `Std.WP` interpretation

An iris language `Expr` together with a ghost-state assumption `IrisGS_gen hlc Expr GF` has the
weakest precondition `WP e @ s ; E {{ Φ }}`, an `IProp GF` for every postcondition
`Φ : Val → IProp GF`. The program `⟪e @ s ; E⟫ : IrisProg GF Expr` pairs the expression `e` with the
stuckness `s` and the mask `E`, and `IrisProg GF Expr` carries the `Std.WP.WP` instance

  `wp ⟪e @ s ; E⟫ Q () = WP e @ s ; E {{ Q }}`.

So the triple `⦃ P ⦄ ⟪e @ E⟫ ⦃ Q ⦄` is the iris triple `{P} e @ E {Q}`. The resource functors `GF`
are an index of the type, because they determine the assertion type `IProp GF`. Iris programs
throw no exceptions, so the exception postcondition is `EStack⟨⟩`.

`Std.WP.Frames` holds for every program and every frame `R` under `BIBase.sep`, by
`wp_frame_l`.
-/

open Iris Iris.BI Iris.ProgramLogic Lean.Order Std.WP

namespace Iris.VCGen

/-- An iris program of the language `Expr` with assertions in `IProp GF`: the expression `expr`,
verified at stuckness `s` and mask `E`. -/
structure IrisProg (_GF : BundledGFunctors) (Expr : Type _) where
  /-- The program `⟪expr @ s ; E⟫`. -/
  mk ::
  /-- The stuckness of the program. -/
  s : Stuckness
  /-- The mask of the program. -/
  E : CoPset
  /-- The expression of the program. -/
  expr : Expr

/-- The program `⟪e @ s ; E⟫`, after iris's `WP e @ s ; E {{ Φ }}`. It takes every form of the
expression part of `WP`: `⟪e @ E⟫` is at stuckness `NotStuck`, and `⟪e⟫` is at mask `⊤`. -/
syntax "⟪" wpExpr "⟫" : term

macro_rules
  | `(⟪ $w:wpExpr ⟫) => do
    let (e, s, E) ← parseWpExpr w
    `(IrisProg.mk $s $E $e)

/-- The iris weakest precondition of `e` at stuckness `s` and mask `E`. -/
abbrev irisWp {hlc : HasLC} {Expr State Obs Val : Type _} [Language Expr State Obs Val]
    {GF : BundledGFunctors} [IrisGS_gen hlc Expr GF] (s : Stuckness) (E : CoPset) (e : Expr)
    (Q : Val → IProp GF) : IProp GF :=
  Wp.wp (PROP := IProp GF) s E e Q

variable {hlc : HasLC} {Expr State Obs Val : Type _} [Language Expr State Obs Val]
  {GF : BundledGFunctors} [IrisGS_gen hlc Expr GF]

instance : Std.WP.WP (IrisProg GF Expr) Val (IProp GF) EStack⟨⟩ where
  trans p := ⟨fun Q _ => irisWp p.s p.E p.expr Q⟩
  trans_monotone _ _ _ _ _ _ hQ := wp_mono hQ

theorem wp_eq (p : IrisProg GF Expr) (Q : Val → IProp GF) (ε : EStack⟨⟩) :
    Std.WP.WP.wp p Q ε = irisWp p.s p.E p.expr Q := rfl

theorem triple_iff_entails {p : IrisProg GF Expr} {P : IProp GF} {Q : Val → IProp GF}
    {ε : EStack⟨⟩} : Triple p P Q ε ↔ (P ⊢ irisWp p.s p.E p.expr Q) :=
  Triple.iff

theorem Triple.of_entails {p : IrisProg GF Expr} {P : IProp GF} {Q : Val → IProp GF}
    {ε : EStack⟨⟩} (h : P ⊢ irisWp p.s p.E p.expr Q) : Triple p P Q ε :=
  triple_iff_entails.mpr h

theorem frames_sep (p : IrisProg GF Expr) (R P : IProp GF) :
    Std.WP.WP.Frames BIBase.sep p R P :=
  ⟨fun _ _ => PartialOrder.rel_trans (meet_le_right _ _) wp_frame_l⟩

end Iris.VCGen
