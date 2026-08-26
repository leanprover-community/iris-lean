/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.Invariants
public import Iris.ProgramLogic.WeakestPre

@[expose] public section

/-!  # Logically atomic Hoare triples -/

namespace Iris
open ProgramLogic Language Language.Notation Std Std.LawfulSet BI ProofMode

section definition

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF] {TA TB TP : Tele}

/-- A logically atomic Hoare triple: `e` refines the atomic update from `α` to `β`, and returns
`f x y z` while handing back the private postcondition `POST x y z`.

The inner mask is hard-coded to be empty, because we have yet to find an example where we want it
to be anything else. The mask `E` is the *implementation* mask; the mask left to the client of the
triple is `⊤ \ E`.

For the non-atomic postcondition, we use an `Option`, combined with a `-∗?`. This is to avoid
introducing spurious `emp -∗` into proofs that do not need a non-atomic postcondition (which is
most of them). -/
@[rocq_alias atomic_wp]
def atomic_wp (e : Expr) (E : CoPset) (α : TA.Arg → IProp GF)
    (β : TA.Arg → TB.Arg → IProp GF) (POST : TA.Arg → TB.Arg → TP.Arg → Option (IProp GF))
    (f : TA.Arg → TB.Arg → TP.Arg → Val) : IProp GF :=
  iprop(∀ Φ, atomic_update (⊤ \ E) ∅ α β
    (λ.. x y, iprop(∀.. z, POST x y z -∗? Φ (f x y z))) -∗ WP e {{ Φ }})

end definition

/-! ## Notation -/

public meta section
open Lean PrettyPrinter Delaborator SubExpr

/-- The `z₁ … zₙ,` binder group of the return value of an atomic triple. -/
syntax awpRetBinders := explicitBinders ", "

/-- `<<{ ∀∀ x, α }>> e @ E <<{ ∃∃ y, β | z, RET v ; POST }>>` is the logically atomic Hoare
triple `atomic_wp e E α β POST f` over the telescopes bound by `∀∀ …`, `∃∃ …` and `z …`. Every
binder group and the private postcondition `; POST` may be omitted. -/
syntax:max (name := atomicWpNotation)
  ppGroup("<<{ " (auAllBinders)? term " }>>" ppSpace term:max " @ " term:max ppSpace
    "<<{ " (auExBinders)? term " | " (atomic(awpRetBinders))? &"RET " term
      (" ; " term)? " }>>") : term

/-- The telescopes and the telescopic functions `α`, `β`, `POST` and `f` of an atomic triple. -/
def awpArgs (xs : Option (TSyntax ``auAllBinders)) (ys : Option (TSyntax ``auExBinders))
    (zs : Option (TSyntax ``awpRetBinders)) (α β v : Term) (POST : Option Term) :
    MacroM (Term × Term × Term × Term × Term × Term × Term) := do
  let xstx? := xs.map fun xs => (⟨xs.raw[1]⟩ : TSyntax ``Lean.explicitBinders)
  let ystx? := ys.map fun ys => (⟨ys.raw[1]⟩ : TSyntax ``Lean.explicitBinders)
  let zstx? := zs.map fun zs => (⟨zs.raw[0]⟩ : TSyntax ``Lean.explicitBinders)
  let TA ← Tele.expandLiteral xstx?
  let TB ← Tele.expandLiteral ystx?
  let TP ← Tele.expandLiteral zstx?
  let POSTArg ← match POST with
    | some POST => `(some iprop($POST))
    | none => `(none)
  let underAll (body : Term) : MacroM Term := do
    Tele.expandFun TA xstx? (← Tele.expandFun TB ystx? (← Tele.expandFun TP zstx? body))
  return (TA, TB, TP,
    ← Tele.expandFun TA xstx? (← `(iprop($α))),
    ← Tele.expandFun TA xstx? (← Tele.expandFun TB ystx? (← `(iprop($β)))),
    ← underAll POSTArg, ← underAll v)

macro_rules
  | `(iprop(<<{%$tk $[$xs]? $α }>> $e @ $E <<{ $[$ys]? $β | $[$zs]? RET $v $[; $POST]? }>>)) => do
    let (TA, TB, TP, α, β, POST, f) ← awpArgs xs ys zs α β v POST
    ``($(wrapIprop tk ``atomic_wp) (TA := $TA) (TB := $TB) (TP := $TP) $e $E $α $β $POST $f)

/-! ### Delaboration -/

/-- The `z₁ … zₙ,` group, or `none` for the empty telescope. -/
def awpRetGroup (zs : Array Ident) : DelabM (Option (TSyntax ``awpRetBinders)) := do
  if zs.isEmpty then return none
  return some (← `(awpRetBinders| $(← auPlainBinders zs), ))

@[app_delab Iris.atomic_wp]
def delabAtomicWp : Delab := do
  let e ← getExpr
  unless e.isAppOfArity ``atomic_wp 17 do failure
  let some nA := Tele.literalArity? (e.getArg! 8) | failure
  let some nB := Tele.literalArity? (e.getArg! 9) | failure
  let some nP := Tele.literalArity? (e.getArg! 10) | failure
  let prog ← withNaryArg 11 delab
  let E ← withNaryArg 12 delab
  let (xs, α) ← withNaryArg 13 <| Tele.withFun nA fun xs => return (xs, ← delab)
  let (ys, β) ← withNaryArg 14 <| Tele.withFunUsing nA (xs.map (·.getId)) fun _ =>
    Tele.withFun nB fun ys => return (ys, ← delab)
  let (zs, POST) ← withNaryArg 15 <| Tele.withFunUsing nA (xs.map (·.getId)) fun _ =>
    Tele.withFunUsing nB (ys.map (·.getId)) fun _ =>
      Tele.withFun nP fun zs => do
        let e ← getExpr
        match_expr e with
        | Option.some _ _ => return (zs, some (← unpackIprop (← withNaryArg 1 delab)))
        | Option.none _ => return (zs, none)
        | _ => failure
  let v ← withNaryArg 16 <| Tele.withFunUsing nA (xs.map (·.getId)) fun _ =>
    Tele.withFunUsing nB (ys.map (·.getId)) fun _ =>
      Tele.withFunUsing nP (zs.map (·.getId)) fun _ => delab
  `(iprop(<<{ $[$(← auAllGroup xs)]? $(← unpackIprop α) }>> $prog @ $E
      <<{ $[$(← auExGroup ys)]? $(← unpackIprop β) | $[$(← awpRetGroup zs)]? RET $v
        $[; $POST]? }>>))

end

/-! ## Theory -/

section lemmas

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {TA TB TP : Tele} {e : Expr} {E : CoPset}
variable {α : TA.Arg → IProp GF} {β : TA.Arg → TB.Arg → IProp GF}
variable {POST : TA.Arg → TB.Arg → TP.Arg → Option (IProp GF)}
variable {f : TA.Arg → TB.Arg → TP.Arg → Val}


@[rocq_alias atomic_wp_seq]
theorem atomic_wp_seq :
    atomic_wp e E α β POST f ⊢
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }} := by
  iunfold atomic_wp
  iintro Hwp %Φ %x Hα HΦ
  iapply wp_frame_wand $$ HΦ
  iapply Hwp
  iauintro
  iaaccintro Hα
  · iintro $
  · iintro %y Hβ !>
    isimp only [Tele.app_bind]
    iintro %z Hpost HΦ
    iapply HΦ $$ Hβ Hpost

@[rocq_alias atomic_wp_inv]
theorem atomic_wp_inv {N : Namespace} {I : IProp GF} (HN : (↑N : CoPset) ⊆ E) :
    atomic_wp e (E \ ↑N) (λ.. x, iprop(▷ I ∗ α x)) (λ.. x y, iprop(▷ I ∗ β x y)) POST f ⊢
    inv N I -∗ atomic_wp e E α β POST f := by
  iunfold atomic_wp
  iintro Hwp #Hinv %Φ AU
  iapply Hwp
  iauintro
  iinv N with HI
  · exact ⟨fun x hx => mem_diff.mpr ⟨CoPset.mem_full, fun h => (mem_diff.mp h).right hx⟩, trivial⟩
  iapply aacc_aupd $$ AU
  · intro x hx
    simp only [mem_diff] at hx ⊢
    exact ⟨⟨CoPset.mem_full, fun h => hx.right h.left⟩, fun h => hx.right (HN x h)⟩
  iintro %x Hα
  iaaccintro %x [HI Hα] <;> isimp only [Tele.app_bind]
  · iframe
  · iintro ⟨HI, $⟩
    iintro !> AU !>
    simp []
    iframe
  · iintro %y H
    icases H with ⟨HI, Hβ⟩
    imodintro
    iright
    iexists y
    iintro {$Hβ} HΦ !>
    simp []
    iframe HI HΦ


/-- This version matches the Texan triple, i.e., with a later in front of the
`(∀.. y, β x y -∗ Φ (f x y))`. -/
@[rocq_alias atomic_wp_seq_step]
theorem atomic_wp_seq_step [toVal_e : TCEq (toVal e) none] :
    atomic_wp e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }} := by
  iintro Hwp %Φ %x Hα HΦ
  iapply wp_step_fupd toVal_e.to_eq subset_refl $$ [$HΦ //]
  iapply atomic_wp_seq $$ Hwp Hα
  iintro %y Hβ %z Hpost HΦ
  iapply HΦ $$ Hβ Hpost

/-- Sequential triples with the empty mask for a physically atomic `e` are atomic. -/
@[rocq_alias atomic_seq_wp_atomic]
theorem atomic_seq_wp_atomic [Atomic .WeaklyAtomic e] :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ ∅ {{ Φ }}) ⊢
    atomic_wp e E α β POST f := by
  iunfold atomic_wp
  iintro Hwp %Φ AU
  imod AU with ⟨%x, Hα, -, Hclose⟩
  iapply Hwp $$ Hα
  iintro %y Hβ %z Hpost
  imod Hclose $$ Hβ with HΦ
  isimp only [Tele.app_bind] at HΦ
  iapply HΦ $$ Hpost

/-- Sequential triples with a persistent precondition and no initial quantifier are atomic. -/
@[rocq_alias persistent_seq_wp_atomic]
theorem persistent_seq_wp_atomic {α : Tele.Arg .nil → IProp GF}
    {β : Tele.Arg .nil → TB.Arg → IProp GF}
    {POST : Tele.Arg .nil → TB.Arg → TP.Arg → Option (IProp GF)}
    {f : Tele.Arg .nil → TB.Arg → TP.Arg → Val} [Persistent (α .nil)] :
    (∀ Φ, α .nil -∗
      (∀.. y, β .nil y -∗ ∀.. z, POST .nil y z -∗? Φ (f .nil y z)) -∗ WP e {{ Φ }}) ⊢
    atomic_wp e E α β POST f := by
  iunfold atomic_wp
  iintro Hwp %Φ HΦ
  iapply fupd_wp
  imod HΦ with ⟨%⟨⟩, #Hα, Hclose, -⟩
  imod Hclose $$ Hα with HΦ
  iapply wp_fupd
  iapply Hwp $$ Hα
  iintro !> %y Hβ %z Hpost
  imod HΦ with ⟨%⟨⟩, -, -, Hclose⟩
  imod Hclose $$ Hβ with HΦ
  isimp only [Tele.app_bind] at HΦ
  iapply HΦ $$ Hpost

@[rocq_alias atomic_wp_mask_weaken]
theorem atomic_wp_mask_weaken {E₁ E₂ : CoPset} (HE : E₁ ⊆ E₂) :
    atomic_wp e E₁ α β POST f ⊢ atomic_wp e E₂ α β POST f := by
  iunfold atomic_wp
  iintro Hwp %Φ AU
  iapply Hwp
  iapply atomic_update_mask_weaken (diff_subset_diff_right HE) $$ AU

end lemmas

end Iris
