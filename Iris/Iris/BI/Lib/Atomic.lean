/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Lib.Fixpoint
public import Iris.BI.Updates
public import Iris.BI.Telescopes
public import Iris.ProofMode
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

/-- Convert `explicitBinders` into the standard binders of a `fun` expression. -/
def auFunBinders (binders? : Option (TSyntax ``Lean.explicitBinders)) :
    MacroM (Option (Array (TSyntax ``Lean.Parser.Term.funBinder))) := do
  let mkBinder (x : Syntax) (ty? : Option Term) :
      TSyntax ``Lean.Parser.Term.funBinder :=
    ⟨Lean.Elab.Term.mkExplicitBinder ⟨x⟩ (ty?.getD (Lean.mkHole x))⟩
  let some binders := binders? | return .none
  let binders := binders.raw[0]
  if binders.getKind == ``Lean.unbracketedExplicitBinders then
    let ty? : Option Term := if binders[1].isNone then none else some ⟨binders[1][1]⟩
    return binders[0].getArgs.map fun binder => mkBinder binder[0] ty?
  else if binders.getArgs.all (·.getKind == ``Lean.bracketedExplicitBinders) then
    return binders.getArgs.flatMap fun binder =>
      binder[1].getArgs.map fun x => mkBinder x[0] (some ⟨binder[3]⟩)
  else
    Macro.throwError "unexpected explicit binder"

/-- The telescope `Tele.cons fun x₁ => … Tele.cons fun xₙ => Tele.nil` binding `binders`. -/
def auTele (binders? : Option (TSyntax ``Lean.explicitBinders)) : MacroM Term := do
  -- The universe of the empty telescope is not otherwise determined.
  let some binders := binders? | return ← `((Tele.nil : Tele.{0}))
  return ⟨← Lean.expandExplicitBinders ``Tele.cons binders (← `(Tele.nil))⟩

/-- The telescopic function `Tele.app fun x₁ … xₙ => ULift.up body` over `TT`, binding `binders`. -/
def auFun (TT : Term) (binders? : Option (Array (TSyntax ``Lean.Parser.Term.funBinder)))
    (body : Term) : MacroM Term := do
  let some binders := binders?
    | return ← `(Tele.app (TT := $TT) (ULift.up $body))
  `(Tele.app (TT := $TT) (fun $binders:funBinder* => ULift.up $body))

/-- The telescopes and the telescopic functions `α`, `β` and `Φ` of an `AU`/`AACC` notation. -/
def auArgs (xs : Option (TSyntax ``auExBinders)) (ys : Option (TSyntax ``auAllBinders))
    (α β Φ : Term) : MacroM (Term × Term × Term × Term × Term) := do
  let xstx? := xs.map fun xs => (⟨xs.raw[1]⟩ : TSyntax ``Lean.explicitBinders)
  let ystx? := ys.map fun ys => (⟨ys.raw[1]⟩ : TSyntax ``Lean.explicitBinders)
  let xbs? ← auFunBinders xstx?
  let ybs? ← auFunBinders ystx?
  let TA ← auTele xstx?
  let TB ← auTele ystx?
  return (TA, TB,
    ← auFun TA xbs? (← `(iprop($α))),
    ← auFun TA xbs? (← auFun TB ybs? (← `(iprop($β)))),
    ← auFun TA xbs? (← auFun TB ybs? (← `(iprop($Φ)))))

macro_rules
  | `(iprop(AU%$tk <{ $[$xs]? $α }> @ $Eo, $Ei <{ $[$ys]? $β, COMM $Φ }>)) => do
    let (TA, TB, α, β, Φ) ← auArgs xs ys α β Φ
    ``($(wrapIprop tk ``atomic_update) (TA := $TA) (TB := $TB) $Eo $Ei $α $β $Φ)
  | `(iprop(AACC%$tk <{ $[$xs]? $α, ABORT $P }> @ $Eo, $Ei
        <{ $[$ys]? $β, COMM $Φ }>)) => do
    let (TA, TB, α, β, Φ) ← auArgs xs ys α β Φ
    ``($(wrapIprop tk ``atomic_acc) (TA := $TA) (TB := $TB) $Eo $Ei $α iprop($P) $β $Φ)

/-! ### Delaboration -/

/-- The number of binders of a literal telescope, if it is one. -/
partial def auTeleLength (e : Expr) : Option Nat :=
  if e.isConstOf ``Tele.nil then
    some 0
  else if e.isAppOfArity ``Tele.cons 2 then
    match e.appArg! with
    | .lam _ _ body _ => (auTeleLength body).map (· + 1)
    | _ => none
  else
    none

/-- Descend through the `n` binders of `fun x₁ … xₙ => ULift.up body`, running `k` on `body` with
the binder identifiers. The binders are named after `names?` if given, so that the components of
an `AU`/`AACC` notation can share their binder names. -/
partial def withAuBinders {α : Type} (n : Nat) (names? : Option (Array Name))
    (acc : Array Ident) (k : Array Ident → DelabM α) : DelabM α := do
  if acc.size < n then
    unless (← getExpr).isLambda do failure
    match names? with
    | some names =>
      let x := names[acc.size]!
      withBindingBody x <| withAuBinders n names? (acc.push (mkIdent x)) k
    | none => withBindingBodyUnusedName fun x => withAuBinders n names? (acc.push ⟨x⟩) k
  else
    unless (← getExpr).isAppOfArity ``ULift.up 2 do failure
    withNaryArg 1 (k acc)

/-- Descend into the body of the telescopic function `Tele.app fun x₁ … xₙ => ULift.up body`. -/
def withAuFun {α : Type} (n : Nat) (names? : Option (Array Name))
    (k : Array Ident → DelabM α) : DelabM α := do
  unless (← getExpr).isAppOfArity ``Tele.app 3 do failure
  withNaryArg 2 (withAuBinders n names? #[] k)

/-- The `explicitBinders` consisting of the plain binders `xs`. -/
def auPlainBinders (xs : Array Ident) : DelabM (TSyntax ``Lean.explicitBinders) := do
  let bs ← xs.mapM fun x => `(binderIdent| $x:ident)
  let unbracketed := Syntax.node2 .none ``Lean.unbracketedExplicitBinders
    (Syntax.node .none nullKind (bs.map (·.raw))) (Syntax.node .none nullKind #[])
  return ⟨Syntax.node1 .none ``Lean.explicitBinders unbracketed⟩

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
  let some nA := auTeleLength (e.getArg! 3) | failure
  let some nB := auTeleLength (e.getArg! 4) | failure
  let Eo ← withNaryArg 5 delab
  let Ei ← withNaryArg 6 delab
  let (xs, α) ← withNaryArg 7 <| withAuFun nA none fun xs => return (xs, ← delab)
  let (ys, β) ← withNaryArg 8 <| withAuFun nA (some (xs.map (·.getId))) fun _ =>
    withAuFun nB none fun ys => return (ys, ← delab)
  let Φ ← withNaryArg 9 <| withAuFun nA (some (xs.map (·.getId))) fun _ =>
    withAuFun nB (some (ys.map (·.getId))) fun _ => delab
  `(iprop(AU <{ $[$(← auExGroup xs)]? $(← unpackIprop α) }> @ $Eo, $Ei
      <{ $[$(← auAllGroup ys)]? $(← unpackIprop β), COMM $(← unpackIprop Φ) }>))

@[app_delab Iris.atomic_acc]
def delabAtomicAcc : Delab := do
  let e ← getExpr
  unless e.isAppOfArity ``atomic_acc 11 do failure
  let some nA := auTeleLength (e.getArg! 3) | failure
  let some nB := auTeleLength (e.getArg! 4) | failure
  let Eo ← withNaryArg 5 delab
  let Ei ← withNaryArg 6 delab
  let (xs, α) ← withNaryArg 7 <| withAuFun nA none fun xs => return (xs, ← delab)
  let P ← withNaryArg 8 delab
  let (ys, β) ← withNaryArg 9 <| withAuFun nA (some (xs.map (·.getId))) fun _ =>
    withAuFun nB none fun ys => return (ys, ← delab)
  let Φ ← withNaryArg 10 <| withAuFun nA (some (xs.map (·.getId))) fun _ =>
    withAuFun nB (some (ys.map (·.getId))) fun _ => delab
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
    (fun _ => atomic_update Eo1 Ei α β Φ)
  · iintro !> %_ H
    unfold atomic_update_pre
    iapply atomic_acc_mask_weaken HE
    iapply aupd_aacc $$ H
  · iexact HAU

set_option synthInstance.checkSynthOrder false in
@[rocq_alias elim_mod_aupd]
instance elim_mod_aupd {φ} {io : InOut} {Eo Ei E : CoPset} {α : TA.Arg → PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} {Q Q' : PROP}
    [H : ∀ R, ElimModal φ false io false iprop(|={E,Ei}=> R) R Q Q'] :
    ElimModal (φ ∧ Eo ⊆ E) false io false
      (atomic_update Eo Ei α β Φ)
      iprop(∃.. x, α x ∗ ((α x ={Ei,E}=∗ atomic_update Eo Ei α β Φ) ∧
        (∀.. y, β x y ={Ei,E}=∗ Φ x y)))
      Q Q' where
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
  iapply greatest_fixpoint_coiter (atomic_update_pre Eo Ei α β Φ) (fun _ => Q)
  · iintro !> %_ HQ
    unfold atomic_update_pre
    iapply HAU
    isplit <;> iassumption
  · iexact HQ

@[rocq_alias aacc_intro]
theorem aacc_intro {Eo Ei : CoPset} {α : TA.Arg → PROP} {P : PROP}
    {β Φ : TA.Arg → TB.Arg → PROP} (HEi : Ei ⊆ Eo) :
    ⊢ (∀.. x, α x -∗
      ((α x ={Eo}=∗ P) ∧ (∀.. y, β x y ={Eo}=∗ Φ x y)) -∗ atomic_acc Eo Ei α P β Φ) := by
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
    iapply Hclose $$ %y Hβ

@[rocq_alias elim_acc_aacc]
instance elim_acc_aacc {X} {E1 E2 Ei : CoPset} {α' β' : X → PROP} {γ' : X → Option PROP}
    {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP} {Pas : PROP} :
    ElimAcc (X := X) True (FUpd.fupd E1 E2) (FUpd.fupd E2 E1) α' β' γ'
      (atomic_acc E1 Ei α Pas β Φ)
      (fun x' => atomic_acc E2 Ei α iprop(β' x' ∗ (γ' x' -∗? Pas)) β
        (fun x y => iprop(β' x' ∗ (γ' x' -∗? Φ x y)))) where
  elim_acc := by
    intro _
    simp only [accessor, atomic_acc]
    iintro Hinner Hacc
    icases Hacc with >⟨%x', Hα', Hclose⟩
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
      imod Hclose' $$ %y Hβ with ⟨Hβ', HΦ⟩
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
    atomic_acc E1' E2 α P β Φ ⊢
    iprop((∀.. x, α x -∗ atomic_acc E2 E3 α' iprop(α x ∗ (P ={E1}=∗ P')) β'
      (fun x' y' => iprop((α x ∗ (P ={E1}=∗ Φ' x' y'))
        ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
      atomic_acc E1 E3 α' P' β' Φ') := by
  iintro Hupd Hstep
  iunfold atomic_acc at Hstep
  iunfold atomic_acc
  ihave HH : atomic_acc E1 E2 α P β Φ $$ [Hupd]
  · iapply atomic_acc_mask_weaken HE $$ Hupd
  iunfold atomic_acc at HH
  imod HH with ⟨%x, Hα, Hclose⟩
  imod Hstep $$ %x Hα with ⟨%x', Hα', Hclose'⟩
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
    imod Hclose' $$ %y' Hβ' with Hres
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
    atomic_update E1' E2 α β Φ ⊢
    (∀.. x, α x -∗ atomic_acc E2 E3 α'
      iprop(α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ P')) β'
      (fun x' y' => iprop((α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ Φ' x' y'))
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
      (fun x' y' => iprop(∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
      atomic_acc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  iapply aacc_aupd HE $$ Hupd
  iintro %x Hα
  iapply atomic_acc_wand $$ [] (Hstep $$ %x Hα)
  isplit
  · iintro $
  · iintro %_ %_ H
    iright
    iexact H

@[rocq_alias aacc_aupd_abort]
theorem aacc_aupd_abort {TA' TB' : Tele} {E1 E1' E2 E3 : CoPset}
    {α : TA.Arg → PROP} {β Φ : TA.Arg → TB.Arg → PROP}
    {α' : TA'.Arg → PROP} {P' : PROP} {β' Φ' : TA'.Arg → TB'.Arg → PROP} (HE : E1' ⊆ E1) :
    atomic_update E1' E2 α β Φ ⊢
    (∀.. x, α x -∗ atomic_acc E2 E3 α'
      iprop(α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ P')) β'
      (fun x' y' => iprop(α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ Φ' x' y')))) -∗
      atomic_acc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  iapply aacc_aupd HE $$ Hupd
  iintro %x Hα
  iapply atomic_acc_wand $$ [] (Hstep $$ %x Hα)
  isplit
  · iintro $
  · iintro %_ %_ H
    ileft
    iexact H

end lemmas

end Iris
