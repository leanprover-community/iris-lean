/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Alvin Tang
-/
module

public import Iris.BI.Lib.Fixpoint
public import Iris.BI.Updates
public import Iris.BI.Telescopes
public meta import Iris.ProofMode
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris
open Iris.Std Iris.ProofMode BI OFE

section definition

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {TA TB : Tele}

/-- `atomic_acc` as the "introduction form" of atomic updates: An accessor that can be aborted
back to `P`. -/
@[rocq_alias atomic_acc]
def atomic_acc (Eo Ei : CoPset) (α : TA.Arg → PROP) (P : PROP)
    (β Φ : TA.Arg → TB.Arg → PROP) : PROP := iprop%
    |={Eo,Ei}=> ∃.. x, α x ∗ ((α x ={Ei,Eo}=∗ P) ∧ (∀.. y, β x y ={Ei,Eo}=∗ Φ x y))

@[rocq_alias atomic_acc_wand]
theorem atomic_acc_wand {Eo Ei : CoPset} {α : TA.Arg → PROP} {P1 P2 : PROP}
    {β Φ1 Φ2 : TA.Arg → TB.Arg → PROP} :
    ((P1 -∗ P2) ∧ (∀.. x, ∀.. y, Φ1 x y -∗ Φ2 x y)) -∗
      atomic_acc Eo Ei α P1 β Φ1 -∗ atomic_acc Eo Ei α P2 β Φ2 := by
  iintro HP12 AS
  unfold atomic_acc
  imod AS with ⟨%x, Hα, Hclose⟩
  imodintro
  iexists x
  iframe Hα
  isplit
  · iintro Hα
    icases HP12 with ⟨HP12, -⟩
    icases Hclose with ⟨Hclose, -⟩
    iapply HP12
    iapply Hclose $$ Hα
  · iintro %y Hβ
    icases HP12 with ⟨-, HP12⟩
    icases Hclose with ⟨-, Hclose⟩
    iapply HP12
    iapply Hclose $$ Hβ

@[rocq_alias atomic_acc_mask]
theorem atomic_acc_mask {Eo Ed : CoPset} {α : TA.Arg → PROP} {P : PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} :
    atomic_acc Eo (Eo \ Ed) α P β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → atomic_acc E (E \ Ed) α P β Φ := by
  isplit
  · iintro Hstep %E %HE
    unfold atomic_acc
    iapply fupd_mask_frame_acc HE $$ Hstep
    iintro ⟨%x, Hα, Hclose⟩
    iintro !> Hclose'
    iexists x
    iframe Hα
    isplit
    · icases Hclose with ⟨Hclose, -⟩
      iintro Hα
      iapply Hclose' $$ (Hclose $$ Hα)
    · icases Hclose with ⟨-, Hclose⟩
      iintro %y Hβ
      iapply Hclose' $$ (Hclose $$ Hβ)
  · iintro Hstep
    iapply Hstep $$ %Eo
    ipureintro; rfl

@[rocq_alias atomic_acc_mask_weaken]
theorem atomic_acc_mask_weaken {Eo1 Eo2 Ei : CoPset} {α : TA.Arg → PROP} {P : PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} (HE : Eo1 ⊆ Eo2) :
    atomic_acc Eo1 Ei α P β Φ -∗ atomic_acc Eo2 Ei α P β Φ := by
  iintro Hstep
  unfold atomic_acc
  imod (fupd_mask_subseteq HE) with Hclose1
  imod Hstep with ⟨%x, Hα, Hclose2⟩
  imodintro
  iexists x
  iframe Hα
  isplit
  · iintro Hα
    icases Hclose2 with ⟨Hclose2, -⟩
    imod Hclose2 $$ Hα with $
    itrivial
  · iintro %y Hβ
    icases Hclose2 with ⟨-, Hclose2⟩
    imod Hclose2 $$ %y Hβ with $
    itrivial

/-! `atomic_update` as a fixed-point of the equation `AU = atomic_acc α AU β Q`. -/

-- FIXME: Update this to use the mono fixpoint machinery

@[rocq_alias atomic_update_pre]
def atomic_update_pre (Eo Ei : CoPset) (α : TA.Arg → PROP)
    (β Φ : TA.Arg → TB.Arg → PROP) : (Unit → PROP) → Unit → PROP :=
  fun Ψ _ => atomic_acc Eo Ei α (Ψ ()) β Φ

@[rocq_alias atomic_update_pre_mono]
instance atomic_update_pre_mono {Eo Ei : CoPset} {α : TA.Arg → PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} : BIMonoPred (atomic_update_pre Eo Ei α β Φ) where
  mono_pred {P1 P2 _ _} := by
    unfold atomic_update_pre
    iintro #HP12 %_ AU
    iapply atomic_acc_wand $$ [] AU
    isplit
    · iintro H
      iapply HP12 $$ H
    · iintro %_ %_ $
  mono_pred_ne := ⟨fun _ _ _ _ => .rfl⟩

@[rocq_alias atomic_update]
def atomic_update (Eo Ei : CoPset) (α : TA.Arg → PROP)
    (β Φ : TA.Arg → TB.Arg → PROP) : PROP :=
  bi_greatest_fixpoint (atomic_update_pre Eo Ei α β Φ) ()

#rocq_ignore atomic_update_def "Rocq sealing auxiliary; folded into `atomic_update` (no sealing in Lean)."
#rocq_ignore atomic_update_aux "Rocq sealing auxiliary."
#rocq_ignore atomic_update_unseal "Rocq unsealing lemma; `atomic_update` unfolds definitionally in Lean."

end definition

/-! ## Notation -/

public meta section
open Lean PrettyPrinter Delaborator SubExpr

/-- The `∃∃ x₁ … xₙ,` binder group of the `AU`/`AACC` notation. -/
syntax auExBinders := "∃∃" explicitBinders ", "
/-- The `∀∀ y₁ … yₙ,` binder group of the `AU`/`AACC` notation. -/
syntax auAllBinders := "∀∀" explicitBinders ", "

/-- The leading keyword of the `AU` notation. It is deliberately not a reserved token, so that
`AU` remains usable as an identifier. -/
def auKw := Lean.Parser.nonReservedSymbol "AU" (includeIdent := true)
/-- The leading keyword of the `AACC` notation. It is deliberately not a reserved token, so that
`AACC` remains usable as an identifier. -/
def aaccKw := Lean.Parser.nonReservedSymbol "AACC" (includeIdent := true)

/-- `AU <{ ∃∃ x, α }> @ Eo, Ei <{ ∀∀ y, β, COMM Φ }>` is the atomic update
`atomic_update Eo Ei α β Φ` over the telescopes bound by `∃∃ …` and `∀∀ …`. -/
syntax:max (name := auNotation)
  ppGroup(auKw " <{ " (auExBinders)? term " }>" ppSpace "@ " term ", " term ppSpace
    "<{ " (auAllBinders)? term ", " ppSpace &"COMM " term " }>") : term

/-- `AACC <{ ∃∃ x, α, ABORT P }> @ Eo, Ei <{ ∀∀ y, β, COMM Φ }>` is the atomic accessor
`atomic_acc Eo Ei α P β Φ` over the telescopes bound by `∃∃ …` and `∀∀ …`. -/
syntax:max (name := aaccNotation)
  ppGroup(aaccKw " <{ " (auExBinders)? term ", " ppSpace &"ABORT " term " }>" ppSpace
    "@ " term ", " term ppSpace
    "<{ " (auAllBinders)? term ", " ppSpace &"COMM " term " }>") : term

/-- The telescopes and the telescopic functions `α`, `β` and `Φ` of an `AU`/`AACC` notation. -/
def auArgs (xs : Option (TSyntax ``auExBinders)) (ys : Option (TSyntax ``auAllBinders))
    (α β Φ : Term) : MacroM (Term × Term × Term × Term × Term) := do
  let xstx? := xs.map fun xs => (⟨xs.raw[1]⟩ : TSyntax ``Lean.explicitBinders)
  let ystx? := ys.map fun ys => (⟨ys.raw[1]⟩ : TSyntax ``Lean.explicitBinders)
  let TA ← Tele.expandLiteral xstx?
  let TB ← Tele.expandLiteral ystx?
  return (TA, TB,
    ← Tele.expandFun TA xstx? (← `(iprop($α))),
    ← Tele.expandFun TA xstx? (← Tele.expandFun TB ystx? (← `(iprop($β)))),
    ← Tele.expandFun TA xstx? (← Tele.expandFun TB ystx? (← `(iprop($Φ)))))

macro_rules
  | `(iprop(AU%$tk <{ $[$xs]? $α }> @ $Eo, $Ei <{ $[$ys]? $β, COMM $Φ }>)) => do
    let (TA, TB, α, β, Φ) ← auArgs xs ys α β Φ
    ``($(wrapIprop tk ``atomic_update) (TA := $TA) (TB := $TB) $Eo $Ei $α $β $Φ)
  | `(iprop(AACC%$tk <{ $[$xs]? $α, ABORT $P }> @ $Eo, $Ei
        <{ $[$ys]? $β, COMM $Φ }>)) => do
    let (TA, TB, α, β, Φ) ← auArgs xs ys α β Φ
    ``($(wrapIprop tk ``atomic_acc) (TA := $TA) (TB := $TB) $Eo $Ei $α iprop($P) $β $Φ)

/-! ### Delaboration -/

/-- The `explicitBinders` consisting of the plain binders `xs`. -/
def auPlainBinders (xs : Array Ident) : DelabM (TSyntax ``Lean.explicitBinders) :=
  `(explicitBinders| $[$xs:ident]*)

/-- The `∃∃ x₁ … xₙ,` group, or `none` for the empty telescope. -/
def auExGroup (xs : Array Ident) : DelabM (Option (TSyntax ``auExBinders)) := do
  if xs.isEmpty then return none
  return some (← `(auExBinders| ∃∃ $(← auPlainBinders xs), ))

/-- The `∀∀ y₁ … yₙ,` group, or `none` for the empty telescope. -/
def auAllGroup (ys : Array Ident) : DelabM (Option (TSyntax ``auAllBinders)) := do
  if ys.isEmpty then return none
  return some (← `(auAllBinders| ∀∀ $(← auPlainBinders ys), ))

@[app_delab Iris.atomic_update]
def delabAtomicUpdate : Delab := do
  let e ← getExpr
  unless e.isAppOfArity ``atomic_update 10 do failure
  let some nA := Tele.literalArity? (e.getArg! 3) | failure
  let some nB := Tele.literalArity? (e.getArg! 4) | failure
  let Eo ← withNaryArg 5 delab
  let Ei ← withNaryArg 6 delab
  let (xs, α) ← withNaryArg 7 <| Tele.withFun nA fun xs => return (xs, ← delab)
  let (ys, β) ← withNaryArg 8 <| Tele.withFunUsing nA (xs.map (·.getId)) fun _ =>
    Tele.withFun nB fun ys => return (ys, ← delab)
  let Φ ← withNaryArg 9 <| Tele.withFunUsing nA (xs.map (·.getId)) fun _ =>
    Tele.withFunUsing nB (ys.map (·.getId)) fun _ => delab
  `(iprop(AU <{ $[$(← auExGroup xs)]? $(← unpackIprop α) }> @ $Eo, $Ei
      <{ $[$(← auAllGroup ys)]? $(← unpackIprop β), COMM $(← unpackIprop Φ) }>))

@[app_delab Iris.atomic_acc]
def delabAtomicAcc : Delab := do
  let e ← getExpr
  unless e.isAppOfArity ``atomic_acc 11 do failure
  let some nA := Tele.literalArity? (e.getArg! 3) | failure
  let some nB := Tele.literalArity? (e.getArg! 4) | failure
  let Eo ← withNaryArg 5 delab
  let Ei ← withNaryArg 6 delab
  let (xs, α) ← withNaryArg 7 <| Tele.withFun nA fun xs => return (xs, ← delab)
  let P ← withNaryArg 8 delab
  let (ys, β) ← withNaryArg 9 <| Tele.withFunUsing nA (xs.map (·.getId)) fun _ =>
    Tele.withFun nB fun ys => return (ys, ← delab)
  let Φ ← withNaryArg 10 <| Tele.withFunUsing nA (xs.map (·.getId)) fun _ =>
    Tele.withFunUsing nB (ys.map (·.getId)) fun _ => delab
  `(iprop(AACC <{ $[$(← auExGroup xs)]? $(← unpackIprop α), ABORT $(← unpackIprop P) }>
      @ $Eo, $Ei <{ $[$(← auAllGroup ys)]? $(← unpackIprop β), COMM $(← unpackIprop Φ) }>))

end

section lemmas

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {TA TB : Tele}

@[rocq_alias atomic_acc_ne]
theorem atomic_acc_ne {Eo Ei : CoPset} {n} {α1 α2 : TA.Arg → PROP} {P1 P2 : PROP}
    {β1 β2 Φ1 Φ2 : TA.Arg → TB.Arg → PROP} (hα : ∀ x, α1 x ≡{n}≡ α2 x)
    (hP : P1 ≡{n}≡ P2) (hβ : ∀ x y, β1 x y ≡{n}≡ β2 x y) (hΦ : ∀ x y, Φ1 x y ≡{n}≡ Φ2 x y) :
    atomic_acc Eo Ei α1 P1 β1 Φ1 ≡{n}≡ atomic_acc Eo Ei α2 P2 β2 Φ2 := by
  unfold atomic_acc
  exact BIFUpdate.ne.ne <| texist_ne fun x => sep_ne.ne (hα x) <| and_ne.ne
    (wand_ne.ne (hα x) (BIFUpdate.ne.ne hP))
    (tforall_ne fun y => wand_ne.ne (hβ x y) (BIFUpdate.ne.ne (hΦ x y)))

@[rocq_alias atomic_update_ne]
theorem atomic_update_ne {Eo Ei : CoPset} {n} {α1 α2 : TA.Arg → PROP}
    {β1 β2 Φ1 Φ2 : TA.Arg → TB.Arg → PROP} (hα : ∀ x, α1 x ≡{n}≡ α2 x)
    (hβ : ∀ x y, β1 x y ≡{n}≡ β2 x y) (hΦ : ∀ x y, Φ1 x y ≡{n}≡ Φ2 x y) :
    atomic_update Eo Ei α1 β1 Φ1 ≡{n}≡ atomic_update Eo Ei α2 β2 Φ2 := by
  unfold atomic_update bi_greatest_fixpoint atomic_update_pre
  refine exists_ne fun Ψ => sep_ne.ne (intuitionistically_ne.ne (forall_ne fun _ => ?_)) .rfl
  exact wand_ne.ne .rfl (atomic_acc_ne hα .rfl hβ hΦ)

@[rocq_alias aupd_unfold]
theorem aupd_unfold {Eo Ei : CoPset} {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP} :
    atomic_update Eo Ei α β Φ ⊣⊢ atomic_acc Eo Ei α (atomic_update Eo Ei α β Φ) β Φ := by
  unfold atomic_update
  exact (greatest_fixpoint_unfold (atomic_update_pre Eo Ei α β Φ)).to_bi

@[rocq_alias aupd_aacc]
theorem aupd_aacc {Eo Ei : CoPset} {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP} :
    atomic_update Eo Ei α β Φ ⊢ atomic_acc Eo Ei α (atomic_update Eo Ei α β Φ) β Φ :=
  aupd_unfold.mp

@[rocq_alias atomic_update_mask_weaken]
theorem atomic_update_mask_weaken {Eo1 Eo2 Ei : CoPset} {α : TA.Arg → PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} (HE : Eo1 ⊆ Eo2) :
    atomic_update Eo1 Ei α β Φ ⊢ atomic_update Eo2 Ei α β Φ := by
  show atomic_update Eo1 Ei α β Φ ⊢ bi_greatest_fixpoint (atomic_update_pre Eo2 Ei α β Φ) ()
  iintro HAU
  iapply greatest_fixpoint_coiter (atomic_update_pre Eo2 Ei α β Φ)
    (fun _ => atomic_update Eo1 Ei α β Φ) $$ [] HAU
  iintro !> %_ H
  unfold atomic_update_pre
  iapply atomic_acc_mask_weaken HE
  iapply aupd_aacc $$ H

set_option synthInstance.checkSynthOrder false in
@[rocq_alias elim_mod_aupd]
instance elim_mod_aupd {φ} {io : InOut} {Eo Ei E : CoPset} {α : TA.Arg → PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} {Q Q' : PROP}
    [H : ∀ R, ElimModal φ false .in false iprop(|={E,Ei}=> R) R Q Q'] :
    ElimModal (φ ∧ Eo ⊆ E) false io false (atomic_update Eo Ei α β Φ)
      iprop(∃.. x, α x ∗ ((α x ={Ei,E}=∗ atomic_update Eo Ei α β Φ) ∧
        (∀.. y, β x y ={Ei,E}=∗ Φ x y))) Q Q' where
  elim_modal := by
    rintro ⟨hφ, hsub⟩
    iintro ⟨AU, Hcont⟩
    ihave AC : atomic_acc E Ei α (atomic_update Eo Ei α β Φ) β Φ $$ [AU]
    · iapply atomic_acc_mask_weaken hsub
      iapply aupd_aacc $$ AU
    iunfold atomic_acc at AC
    iapply (H _).elim_modal hφ
    iframe

@[rocq_alias aupd_intro]
theorem aupd_intro {Eo Ei : CoPset} {P Q : PROP} {α : TA.Arg → PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} [Absorbing P] [Persistent P]
    (HAU : P ∧ Q ⊢ atomic_acc Eo Ei α Q β Φ) :
    P ∧ Q ⊢ atomic_update Eo Ei α β Φ := by
  show iprop(P ∧ Q) ⊢ bi_greatest_fixpoint (atomic_update_pre Eo Ei α β Φ) ()
  iintro ⟨#HP, HQ⟩
  iapply greatest_fixpoint_coiter (atomic_update_pre Eo Ei α β Φ) (fun _ => Q) $$ [] HQ
  iintro !> %_ HQ
  unfold atomic_update_pre
  iapply HAU $$ [$]

@[rocq_alias aacc_intro]
private theorem aacc_intro {Eo Ei : CoPset} {α : TA.Arg → PROP} {P : PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} (HEi : Ei ⊆ Eo) :
    ∀.. x, α x -∗
      ((α x ={Eo}=∗ P) ∧ (∀.. y, β x y ={Eo}=∗ Φ x y)) -∗ atomic_acc Eo Ei α P β Φ := by
  iintro %x Hα Hclose
  unfold atomic_acc
  iapply fupd_mask_intro HEi
  iintro Hclose'
  iexists x
  iframe Hα
  isplit
  · iintro Hα
    imod Hclose'
    icases Hclose with ⟨Hclose, -⟩
    iapply Hclose $$ Hα
  · iintro %y Hβ
    imod Hclose'
    icases Hclose with ⟨-, Hclose⟩
    iapply Hclose $$ Hβ

@[rocq_alias elim_acc_aacc]
instance elim_acc_aacc {X} {E1 E2 Ei : CoPset} {α' β' : X → PROP} {γ' : X → Option PROP}
    {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP} {Pas : PROP} :
    ElimAcc True (FUpd.fupd E1 E2) (FUpd.fupd E2 E1) α' β' γ'
      (atomic_acc E1 Ei α Pas β Φ)
      (fun x' => atomic_acc E2 Ei α iprop(β' x' ∗ (γ' x' -∗? Pas)) β
        (λ.. x y, iprop(β' x' ∗ (γ' x' -∗? Φ x y)))) where
  elim_acc := by
    intro _
    simp only [accessor, atomic_acc]
    iintro Hinner >⟨%x', Hα', Hclose⟩
    imod Hinner $$ Hα' with ⟨%x, Hα, Hclose'⟩
    iapply fupd_mask_intro CoPset.subseteq_refl
    iintro Hclose''
    iexists x
    iframe Hα
    isplit
    · iintro Hα
      imod Hclose''
      icases Hclose' with ⟨Hclose', -⟩
      imod Hclose' $$ Hα with ⟨Hβ', HPas⟩
      imod Hclose $$ Hβ' with Hγ'
      imodintro
      iapply HPas $$ Hγ'
    · iintro %y Hβ
      imod Hclose''
      icases Hclose' with ⟨-, Hclose'⟩
      isimp only [Tele.app_bind] at Hclose'
      imod Hclose' $$ Hβ with ⟨Hβ', HΦ⟩
      imod Hclose $$ Hβ' with Hγ'
      imodintro
      iapply HΦ $$ Hγ'

@[rocq_alias elim_modal_acc]
instance elim_modal_acc {p : Bool} {io : InOut} {q : Bool} {φ} {P P' : PROP} {Eo Ei : CoPset}
    {α : TA.Arg → PROP} {Pas : PROP} {β Φ : TA.Arg → TB.Arg → PROP}
    [H : ∀ R, ElimModal φ p io q P P' iprop(|={Eo,Ei}=> R) iprop(|={Eo,Ei}=> R)] :
    ElimModal φ p io q P P' (atomic_acc Eo Ei α Pas β Φ) (atomic_acc Eo Ei α Pas β Φ) :=
  H _

@[rocq_alias aacc_aacc]
theorem aacc_aacc {TA' TB' : Tele} {E1 E1' E2 E3 : CoPset}
    {α : TA.Arg → PROP} {P : PROP} {β Φ : TA.Arg → TB.Arg → PROP}
    {α' : TA'.Arg → PROP} {P' : PROP} {β' Φ' : TA'.Arg → TB'.Arg → PROP} (HE : E1' ⊆ E1) :
    atomic_acc E1' E2 α P β Φ -∗
    iprop((∀.. x, α x -∗ atomic_acc E2 E3 α' iprop(α x ∗ (P ={E1}=∗ P')) β'
      (λ.. x' y', iprop((α x ∗ (P ={E1}=∗ Φ' x' y'))
        ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
      atomic_acc E1 E3 α' P' β' Φ') := by
  iintro Hupd Hstep
  iunfold atomic_acc at Hstep
  iunfold atomic_acc
  ihave HH : atomic_acc E1 E2 α P β Φ $$ [Hupd]
  · iapply atomic_acc_mask_weaken HE $$ Hupd
  iunfold atomic_acc at HH
  imod HH with ⟨%x, Hα, Hclose⟩
  imod Hstep $$ Hα with ⟨%x', Hα', Hclose'⟩
  imodintro
  iexists x'
  iframe Hα'
  isplit
  · iintro Hα'
    icases Hclose' with ⟨Hclose', -⟩
    imod Hclose' $$ Hα' with ⟨Hα, Hupd⟩
    icases Hclose with ⟨Hclose, -⟩
    imod Hclose $$ Hα with HP
    iapply Hupd $$ HP
  · iintro %y' Hβ'
    icases Hclose' with ⟨-, Hclose'⟩
    imod Hclose' $$ Hβ' with Hres
    isimp only [Tele.app_bind] at Hres
    icases Hres with (⟨Hα, HΦ'⟩ | ⟨%y, Hβ, HΦ'⟩)
    · icases Hclose with ⟨Hclose, -⟩
      imod Hclose $$ Hα with HP
      iapply HΦ' $$ HP
    · icases Hclose with ⟨-, Hclose⟩
      imod Hclose $$ %y Hβ with HΦ
      iapply HΦ' $$ HΦ

@[rocq_alias aacc_aupd]
theorem aacc_aupd {TA' TB' : Tele} {E1 E1' E2 E3 : CoPset}
    {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP}
    {α' : TA'.Arg → PROP} {P' : PROP} {β' Φ' : TA'.Arg → TB'.Arg → PROP} (HE : E1' ⊆ E1) :
    atomic_update E1' E2 α β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α'
      iprop(α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ P')) β'
      (λ.. x' y', iprop((α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ Φ' x' y'))
        ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
      atomic_acc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  iapply aacc_aacc HE $$ [Hupd] Hstep
  iapply aupd_aacc $$ Hupd

@[rocq_alias aacc_aupd_commit]
theorem aacc_aupd_commit {TA' TB' : Tele} {E1 E1' E2 E3 : CoPset}
    {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP}
    {α' : TA'.Arg → PROP} {P' : PROP} {β' Φ' : TA'.Arg → TB'.Arg → PROP} (HE : E1' ⊆ E1) :
    atomic_update E1' E2 α β Φ ⊢
    (∀.. x, α x -∗ atomic_acc E2 E3 α'
      iprop(α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ P')) β'
      (λ.. x' y', iprop(∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
      atomic_acc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  iapply aacc_aupd HE $$ Hupd
  iintro %x Hα
  iapply atomic_acc_wand $$ [] (Hstep $$ Hα)
  isplit
  · iintro $
  · iintro %_ %_ H
    isimp only [Tele.app_bind]
    isimp only [Tele.app_bind] at H
    iright; itrivial

@[rocq_alias aacc_aupd_abort]
theorem aacc_aupd_abort {TA' TB' : Tele} {E1 E1' E2 E3 : CoPset}
    {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP}
    {α' : TA'.Arg → PROP} {P' : PROP} {β' Φ' : TA'.Arg → TB'.Arg → PROP} (HE : E1' ⊆ E1) :
    atomic_update E1' E2 α β Φ ⊢
    (∀.. x, α x -∗ atomic_acc E2 E3 α'
      iprop(α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ P')) β'
      (λ.. x' y', iprop(α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ Φ' x' y')))) -∗
      atomic_acc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  iapply aacc_aupd HE $$ Hupd
  iintro %x Hα
  iapply atomic_acc_wand $$ [] (Hstep $$ Hα)
  isplit
  · iintro $
  · iintro %_ %_ H
    isimp only [Tele.app_bind]
    isimp only [Tele.app_bind] at H
    ileft; itrivial

end lemmas

section ProofMode

variable [BI PROP] [BIFUpdate PROP] {TA TB : Tele}

@[rocq_alias tac_aupd_intro]
theorem tac_aupd_intro {e eI eS : PROP} {Eo Ei : CoPset} {α : TA.Arg → PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} (hsplit : e ⊣⊢ eI ∗ eS) (hI : eI ⊢ □ eI)
    (H : e ⊢ atomic_acc Eo Ei α eS β Φ) :
    e ⊢ atomic_update Eo Ei α β Φ := by
  have h : e ⊣⊢ <pers> eI ∧ eS := calc
    _ ⊣⊢ eI ∗ eS        := hsplit
    _ ⊣⊢ □ eI ∗ eS      := sep_congr_left ⟨hI, intuitionistically_elim⟩
    _ ⊣⊢ <pers> eI ∧ eS := persistently_and_intuitionistically_sep_left.symm
  exact h.mp.trans <| aupd_intro (h.mpr.trans H)

omit [BIFUpdate PROP] in
theorem tac_aacc_intro {pa pb : Bool} {e e' A R1 R2 Q : PROP} (hlem : ⊢ □?pa A)
    (hspec : (e' ∗ □?pb ((R1 ∧ R2) -∗ Q) ⊢ Q) → e ∗ □?pa A ⊢ Q) (hR1 : e' ⊢ R1) (hR2 : e' ⊢ R2) : e ⊢ Q := calc
  e ⊢ e ∗ emp    := sep_emp.mpr
  _ ⊢ e ∗ □?pa A := sep_mono_right hlem
  _ ⊢ Q          := hspec <| (sep_mono (and_intro hR1 hR2) intuitionisticallyIf_elim).trans wand_elim_right

theorem aacc_intro_wand (Eo Ei : CoPset) (α : TA.Arg → PROP) (P : PROP)
    (β Φ : TA.Arg → TB.Arg → PROP) (HEi : Ei ⊆ Eo) (x : TA.Arg) :
    ⊢ (α x -∗ ((α x ={Eo}=∗ P) ∧ (∀.. y, β x y ={Eo}=∗ Φ x y)) -∗ atomic_acc Eo Ei α P β Φ) :=
  (Tele.tforall_forall _).mp (aacc_intro HEi) x

public meta section
open Lean Meta Elab Qq Expr

/--
`iauintro` turns a goal that is an atomic update (`atomic_update`) into the
corresponding atomic accessor (`atomic_acc`), whose abort condition is the
separating conjunction of the spatial hypotheses.
-/
elab "iauintro" : tactic => do
  ProofModeM.runTactic `iauintro λ mvar { hyps, goal, .. } => do
    let_expr atomic_update _ _ _ _ _ Eo Ei α β Φ := goal
      | throwIPMError "the goal {goal} is not an atomic update"
    -- Split the context into its intuitionistic and spatial parts
    let ⟨_, eS, pfSplit, pfInt⟩ := hyps.splitIntuitionisticSpatial
    let newGoal ← mkAppM ``atomic_acc #[Eo, Ei, α, eS, β, Φ]
    mvar.assign <| ← mkAppM ``tac_aupd_intro #[pfSplit, pfInt, ← addBIGoal hyps newGoal]

/--
`iaaccintro spats` prove an atomic accessor by applying `aacc_intro`, where
the specialisation patterns `spats` discharge the atomic precondition.
There are three subgoals:
- the mask side condition `Ei ⊆ Eo`,
- the abort goal, and
- the commit goal.

The mask side condition is discharged automatically, if possible.
The latter two subgoals keep the hypotheses left over by the specialisation patterns.
-/
elab "iaaccintro" spats:(colGt ppSpace specPat)+ : tactic => do
  let spats ← liftMacroM <| spats.toList.mapM (SpecPat.parse ·.raw)
  -- A leading specialisation pattern `%t` gives the telescope argument
  let (t, spats) := match spats with
    | ⟨_, .pure t⟩ :: rest => (some t, rest)
    | _                    => (none, spats)

  ProofModeM.runTactic `iaaccintro λ mvar { prop, e, hyps, goal, .. } => do
    let_expr atomic_acc _ _ _ _ _ Eo Ei α P β Φ := goal
      | throwIPMError "the goal {goal} is not an atomic accessor"
    have Eo : Q(CoPset) := Eo
    have Ei : Q(CoPset) := Ei
    let mask : Q($Ei ⊆ $Eo) ← iSolveSidecondition q($Ei ⊆ $Eo)
    -- Handle the argument for the telescopic quantifier
    let xTy := (← whnf <| ← inferType α).bindingDomain!
    let x ← match t with
      | some t => Term.elabTermEnsuringType t xTy
      | none => mkFreshExprMVar xTy
    let pfAacc ← mkAppM ``aacc_intro_wand #[Eo, Ei, α, P, β, Φ, mask, x]
    let A : Q($prop) ← mkFreshExprMVarQ prop
    unless ← isDefEq (← inferType pfAacc) q(⊢ $A) do
      throwIPMError "internal error: unexpected statement of aacc_intro_wand"
    have pfAacc : Q(⊢ □?false $A) := pfAacc
    -- Discharge the atomic precondition `α x` using the given specialisation patterns
    let ⟨e', hyps', pb, B, pfSpec⟩ ← iSpecializeCore hyps q(false) A goal spats
    -- The closing conjunction of the abort and the commit continuation remains
    let ~q(iprop(($abortGoal ∧ $commitGoal) -∗ $Q)) := B
      | throwIPMError "the specialisation patterns must discharge the atomic precondition only, \
          leaving {B}"
    unless ← isDefEq Q goal do
      throwIPMError "internal error: {Q} is not the atomic accessor being proved"
    have pfSpec : Q(($e' ∗ □?$pb iprop(($abortGoal ∧ $commitGoal) -∗ $goal) ⊢ $goal) →
      $e ∗ □?false $A ⊢ $goal) := pfSpec
    let pfAbort ← addBIGoal hyps' abortGoal `abort
    let pfCommit ← addBIGoal hyps' commitGoal `commit
    mvar.assign q(tac_aacc_intro $pfAacc $pfSpec $pfAbort $pfCommit)

end

end ProofMode

end Iris
