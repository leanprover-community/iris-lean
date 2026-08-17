module

public import Iris.HeapLang.Instances
public import Iris.HeapLang.Completeness
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.Nonbranching
public import Std.Internal.Do.WP.Basic

@[expose] public section
namespace Iris.HeapLang

open ProgramLogic PrimStep Language Language.Notation Lean.Order

/-! ## Nonbranching weakest precondition for Pure HeapLang

This file constructs an alternative weakest precondition for the fork-free fragment of HeapLang.

The weakest precondition satisfies two important properties:
- It is an instance of the HeapLang axiomatic semantics (`AxSem.lean`)
- It is proven sound: any proof of `wp` implies an analagous `AdequateNoFork` statement.

This weakest precondition serves to connect the automated proofs carried out against the HeapLang
axiomatic semantics to the manual proofs carried out in Iris.
-/


section Iris

open Iris ProgramLogic Iris.BI Language Language.Notation PrimStep Iris.Std Nonbranching

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF] [CInvG GF]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat] [GhostMapG GF Nat Exp H]

include H in
/-- Iris external proof rule for interfacing with `Std.do`.

This rule discharges a proof obligation for a nonbranching HeapLang program stated with the
nonbranching `wp` weakest precondition by turning it into a HeapLang Iris `WP`, via the HeapLang
completeness endpoint `heap_lang_sem_completeness_nofork`. The initial `heapInv σ` is consumed
as a premise (exactly as the completeness endpoint requires it).

NOTE: This is not the most expressive rule possible. For example, both `wp` and the completeness
theorem support state, however the formulation of stateful weakest preconditions is under active
development in `Std.do` as of Lean 4.32.2.
-/
theorem wp_external_pure (e : Exp) (σ : State) (Φ : Val → Prop)
    (hwp : Nonbranching.wp e σ (fun v _ => Φ v)) :
    ⊢@{IProp GF} heapInv σ -∗
      Wp.wp (PROP := IProp GF) Stuckness.NotStuck ⊤ e (fun v => BIBase.pure (Φ v)) := by
  iintro Hheap
  ihave Hcomplete := heap_lang_sem_completeness_nofork e σ (fun v _ => Φ v)
    (wp_adequateNoFork hwp) $$ Hheap
  iapply wp_wand $$ Hcomplete
  iintro %v ⟨%_, _, _⟩
  iframe

end Iris

/-! ## Axiomatic semantics instance for the nonbranching `wp`

The pure value-level stepping rules for HeapLang (each an instance of the generic
`Nonbranching.wp_lift_step` with the relevant `BaseStep` inverted), packaged into an
instance of `HeapLangAxioms` (moved here from `AxSem.lean`). -/

namespace Nonbranching

open ProgramLogic EctxLanguage

/-- The nonbranching weakest precondition, specialized (monomorphic) to HeapLang.
Keeping the type arguments fixed lets dotted notation like `.if`/`.load` resolve. -/
abbrev owp : Exp → State → (Val → State → Prop) → Prop := Nonbranching.wp

/-! ### Pure value-level stepping rules -/

/-- Bind over an evaluation context `fill K`. -/
theorem wp_bind_fill (K : List ECtxItem) {e σ Q}
    (hwp : owp e σ (fun v σ' => owp (ProgramLogic.fill K (Exp.ofVal v)) σ' Q)) :
    owp (ProgramLogic.fill K e) σ Q :=
  Nonbranching.wp_bind (K := ProgramLogic.fill K) hwp

/-- `if #true then e₁ else e₂` reduces to `e₁`. -/
theorem wp_if_true {e₁ e₂ : Exp} {σ Q} (hQ : owp e₁ σ Q) :
    owp (.if (.ofVal (.lit (.bool true))) e₁ e₂) σ Q := by
  have hbred : BaseStep.Reducible (Exp.if (.ofVal (.lit (.bool true))) e₁ e₂, σ) :=
    ⟨[], _, _, _, BaseStep.ifTrueS e₁ e₂ σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | ifTrueS => exact ⟨rfl, hQ⟩

/-- `if #false then e₁ else e₂` reduces to `e₂`. -/
theorem wp_if_false {e₁ e₂ : Exp} {σ Q} (hQ : owp e₂ σ Q) :
    owp (.if (.ofVal (.lit (.bool false))) e₁ e₂) σ Q := by
  have hbred : BaseStep.Reducible (Exp.if (.ofVal (.lit (.bool false))) e₁ e₂, σ) :=
    ⟨[], _, _, _, BaseStep.ifFalseS e₁ e₂ σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | ifFalseS => exact ⟨rfl, hQ⟩

/-- β-reduction: applying a recursive closure substitutes both binders. -/
theorem wp_beta {f x : Binder} {e1 : Exp} {v2 : Val} {σ Q}
    (hQ : owp ((e1.subst f (.rec_ f x e1)).subst x v2) σ Q) :
    owp (.app (.ofVal (.rec_ f x e1)) (.ofVal v2)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.app (.ofVal (.rec_ f x e1)) (.ofVal v2), σ) :=
    ⟨[], _, _, _, BaseStep.betaS f x e1 v2 _ σ rfl⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | betaS _ _ _ _ _ _ heq => subst heq; exact ⟨rfl, hQ⟩

/-- Recursive closures evaluate to themselves as values. -/
theorem wp_rec {f x : Binder} {e : Exp} {σ Q}
    (hQ : Q (.rec_ f x e) σ) : owp (.rec_ f x e) σ Q := by
  have hbred : BaseStep.Reducible (Exp.rec_ f x e, σ) := ⟨[], _, _, _, BaseStep.recS f x e σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | recS _ _ _ _ => exact ⟨rfl, Nonbranching.wp_val.mpr hQ⟩

/-- Unary operator evaluation. -/
theorem wp_unop {op : UnOp} {v v' : Val} {σ Q}
    (hop : op.eval v = some v') (hQ : Q v' σ) : owp (.unop op (.ofVal v)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.unop op (.ofVal v), σ) :=
    ⟨[], _, _, _, BaseStep.unOpS op v v' σ hop⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | unOpS _ _ v'' _ hop' => rw [hop'] at hop; cases hop; exact ⟨rfl, Nonbranching.wp_val.mpr hQ⟩

/-- Binary operator evaluation. -/
theorem wp_binop {op : BinOp} {v1 v2 v' : Val} {σ Q}
    (hop : op.eval v1 v2 = some v') (hQ : Q v' σ) :
    owp (.binop op (.ofVal v1) (.ofVal v2)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.binop op (.ofVal v1) (.ofVal v2), σ) :=
    ⟨[], _, _, _, BaseStep.binOpS op v1 v2 v' σ hop⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | binOpS _ _ _ v'' _ hop' => rw [hop'] at hop; cases hop; exact ⟨rfl, Nonbranching.wp_val.mpr hQ⟩

/-- Pairing two values. -/
theorem wp_pair {v1 v2 : Val} {σ Q} (hQ : Q (.pair v1 v2) σ) :
    owp (.pair (.ofVal v1) (.ofVal v2)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.pair (.ofVal v1) (.ofVal v2), σ) :=
    ⟨[], _, _, _, BaseStep.pairS v1 v2 σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | pairS _ _ _ => exact ⟨rfl, Nonbranching.wp_val.mpr hQ⟩

/-- First projection. -/
theorem wp_fst {v1 v2 : Val} {σ Q} (hQ : Q v1 σ) :
    owp (.fst (.ofVal (.pair v1 v2))) σ Q := by
  have hbred : BaseStep.Reducible (Exp.fst (.ofVal (.pair v1 v2)), σ) :=
    ⟨[], _, _, _, BaseStep.fstS v1 v2 σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | fstS _ _ _ => exact ⟨rfl, Nonbranching.wp_val.mpr hQ⟩

/-- Second projection. -/
theorem wp_snd {v1 v2 : Val} {σ Q} (hQ : Q v2 σ) :
    owp (.snd (.ofVal (.pair v1 v2))) σ Q := by
  have hbred : BaseStep.Reducible (Exp.snd (.ofVal (.pair v1 v2)), σ) :=
    ⟨[], _, _, _, BaseStep.sndS v1 v2 σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | sndS _ _ _ => exact ⟨rfl, Nonbranching.wp_val.mpr hQ⟩

/-- Left injection. -/
theorem wp_injL {v : Val} {σ Q} (hQ : Q (.injL v) σ) : owp (.injL (.ofVal v)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.injL (.ofVal v), σ) := ⟨[], _, _, _, BaseStep.injLS v σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | injLS _ _ => exact ⟨rfl, Nonbranching.wp_val.mpr hQ⟩

/-- Right injection. -/
theorem wp_injR {v : Val} {σ Q} (hQ : Q (.injR v) σ) : owp (.injR (.ofVal v)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.injR (.ofVal v), σ) := ⟨[], _, _, _, BaseStep.injRS v σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | injRS _ _ => exact ⟨rfl, Nonbranching.wp_val.mpr hQ⟩

/-- `case` on a left injection takes the left branch (applied to the payload). -/
theorem wp_case_injL {v : Val} {e1 e2 σ Q} (hQ : owp (.app e1 (.ofVal v)) σ Q) :
    owp (.case (.ofVal (.injL v)) e1 e2) σ Q := by
  have hbred : BaseStep.Reducible (Exp.case (.ofVal (.injL v)) e1 e2, σ) :=
    ⟨[], _, _, _, BaseStep.caseLS v e1 e2 σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | caseLS _ _ _ _ => exact ⟨rfl, hQ⟩

/-- `case` on a right injection takes the right branch (applied to the payload). -/
theorem wp_case_injR {v : Val} {e1 e2 σ Q} (hQ : owp (.app e2 (.ofVal v)) σ Q) :
    owp (.case (.ofVal (.injR v)) e1 e2) σ Q := by
  have hbred : BaseStep.Reducible (Exp.case (.ofVal (.injR v)) e1 e2, σ) :=
    ⟨[], _, _, _, BaseStep.caseRS v e1 e2 σ⟩
  refine Nonbranching.wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | caseRS _ _ _ _ => exact ⟨rfl, hQ⟩

end Nonbranching

/-! ## The HeapLang axiomatic semantics (moved from `AxSem.lean`) -/

namespace Ax

/-- A state-passing weakest precondition `wp e σ Φ` (postcondition `Φ : Val → State → Prop`
sees the reached state) modelling the pure fragment of HeapLang. The reached state threads
through each rule's continuation, so no state quantification is needed. -/
class HeapLangAxioms (wp : Exp → State → (Val → State → Prop) → Prop) where
  wp_mono : (∀ v σ, Φ v σ → Ψ v σ) → wp e σ Φ → wp e σ Ψ
  wp_val : Φ v σ → wp (Exp.ofVal v) σ Φ
  wp_closure : Φ (.rec_ f x e) σ → wp (Exp.rec_ f x e) σ Φ
  wp_app :
    wp e₂ σ (fun v₂ σ' => wp e₁ σ' (fun vf σ'' => ∃ f x body, vf = Val.rec_ f x body ∧
      wp ((body.subst f (.rec_ f x body)).subst x v₂) σ'' Φ)) →
    wp (Exp.app e₁ e₂) σ Φ
  wp_unop :
    wp e σ (fun v σ' => ∃ v', op.eval v = some v' ∧ Φ v' σ') →
    wp (Exp.unop op e) σ Φ
  wp_binop :
    wp e₂ σ (fun v₂ σ' => wp e₁ σ' (fun v₁ σ'' => ∃ v', op.eval v₁ v₂ = some v' ∧ Φ v' σ'')) →
    wp (Exp.binop op e₁ e₂) σ Φ
  wp_cond :
    wp e₀ σ (fun vc σ' => ∃ b, vc = Val.lit (.bool b) ∧ wp (if b then e₁ else e₂) σ' Φ) →
    wp (Exp.if e₀ e₁ e₂) σ Φ
  wp_pair :
    wp e₂ σ (fun v₂ σ' => wp e₁ σ' (fun v₁ σ'' => Φ (Val.pair v₁ v₂) σ'')) →
    wp (Exp.pair e₁ e₂) σ Φ
  wp_fst : wp e σ (fun v σ' => ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ Φ v₁ σ') → wp (Exp.fst e) σ Φ
  wp_snd : wp e σ (fun v σ' => ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ Φ v₂ σ') → wp (Exp.snd e) σ Φ
  wp_injL : wp e σ (fun v σ' => Φ (Val.injL v) σ') → wp (Exp.injL e) σ Φ
  wp_injR : wp e σ (fun v σ' => Φ (Val.injR v) σ') → wp (Exp.injR e) σ Φ
  wp_case :
    wp e₀ σ (fun vc σ' =>
      (∃ v, vc = Val.injL v ∧ wp (Exp.app e₁ (Exp.ofVal v)) σ' Φ) ∨
      (∃ v, vc = Val.injR v ∧ wp (Exp.app e₂ (Exp.ofVal v)) σ' Φ)) →
    wp (Exp.case e₀ e₁ e₂) σ Φ
  wp_bind (K : ECtxItem) :
    wp e σ (fun v σ' => wp (K.fill (Exp.ofVal v)) σ' Φ) → wp (K.fill e) σ Φ

/-- The nonbranching `wp` is a model of the HeapLang axiomatic semantics: the state-passing
postcondition lets the reached state thread through each rule directly, with no state
quantification. -/
instance : HeapLangAxioms Nonbranching.owp where
  wp_mono h H := Nonbranching.wp_mono h H
  wp_val h := Nonbranching.wp_val.mpr h
  wp_closure h := Nonbranching.wp_rec h
  wp_bind K H := Nonbranching.wp_bind_fill [K] H
  wp_unop {e σ op Φ} H :=
    Nonbranching.wp_bind_fill [.unOp op]
      (Nonbranching.wp_mono (fun v σ' hv => hv.elim fun v' hop => Nonbranching.wp_unop hop.1 hop.2) H)
  wp_binop {e₂ σ e₁ op Φ} H :=
    Nonbranching.wp_bind_fill [.binOpR op e₁]
      (Nonbranching.wp_mono (fun v₂ σ' H₂ =>
        Nonbranching.wp_bind_fill [.binOpL op v₂]
          (Nonbranching.wp_mono (fun v₁ σ'' hv => hv.elim fun v' hop =>
            Nonbranching.wp_binop hop.1 hop.2) H₂)) H)
  wp_pair {e₂ σ e₁ Φ} H :=
    Nonbranching.wp_bind_fill [.pairR e₁]
      (Nonbranching.wp_mono (fun v₂ σ' H₂ =>
        Nonbranching.wp_bind_fill [.pairL v₂]
          (Nonbranching.wp_mono (fun v₁ σ'' hΦ => Nonbranching.wp_pair hΦ) H₂)) H)
  wp_app {e₂ σ e₁ Φ} H := by
    refine Nonbranching.wp_bind_fill [.appR e₁] (Nonbranching.wp_mono (fun v₂ σ' H₂ => ?_) H)
    refine Nonbranching.wp_bind_fill [.appL v₂] (Nonbranching.wp_mono (fun vf σ'' hvf => ?_) H₂)
    obtain ⟨f, x, body, rfl, Hbody⟩ := hvf
    exact Nonbranching.wp_beta Hbody
  wp_cond {e₀ σ e₁ e₂ Φ} H := by
    refine Nonbranching.wp_bind_fill [.if e₁ e₂] (Nonbranching.wp_mono (fun vc σ' hvc => ?_) H)
    obtain ⟨b, rfl, Hb⟩ := hvc
    cases b
    · exact Nonbranching.wp_if_false Hb
    · exact Nonbranching.wp_if_true Hb
  wp_fst {e σ Φ} H := by
    refine Nonbranching.wp_bind_fill [.fst] (Nonbranching.wp_mono (fun v σ' hv => ?_) H)
    obtain ⟨v₁, v₂, rfl, hΦ⟩ := hv
    exact Nonbranching.wp_fst hΦ
  wp_snd {e σ Φ} H := by
    refine Nonbranching.wp_bind_fill [.snd] (Nonbranching.wp_mono (fun v σ' hv => ?_) H)
    obtain ⟨v₁, v₂, rfl, hΦ⟩ := hv
    exact Nonbranching.wp_snd hΦ
  wp_injL {e σ Φ} H :=
    Nonbranching.wp_bind_fill [.injL] (Nonbranching.wp_mono (fun v σ' hΦ => Nonbranching.wp_injL hΦ) H)
  wp_injR {e σ Φ} H :=
    Nonbranching.wp_bind_fill [.injR] (Nonbranching.wp_mono (fun v σ' hΦ => Nonbranching.wp_injR hΦ) H)
  wp_case {e₀ σ e₁ Φ e₂} H := by
    refine Nonbranching.wp_bind_fill [.case e₁ e₂] (Nonbranching.wp_mono (fun vc σ' hvc => ?_) H)
    rcases hvc with ⟨v, rfl, Hv⟩ | ⟨v, rfl, Hv⟩
    · exact Nonbranching.wp_case_injL Hv
    · exact Nonbranching.wp_case_injR Hv

end Ax

end Iris.HeapLang
