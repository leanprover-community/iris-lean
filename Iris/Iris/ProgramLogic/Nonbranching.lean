/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Std.GreatestFixpoint
public import Iris.Std.PartialMap
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.AbstractLangCompleteness

namespace Nonbranching

section wp
public section

open Iris ProgramLogic Language.Notation PrimStep Lean.Order Std.Internal.Do

variable {Exp Val State Obs : Type _} [Language Exp State Obs Val]

abbrev WPArg := Exp → State → (Val → State → Prop) → Prop

def wpF (r : @WPArg Exp Val State) : @WPArg Exp Val State := fun e σ Φ  =>
  (∃ v : Val, ToVal.toVal e = some v ∧ Φ v σ) ∨
  (Reducible (e, σ) ∧
    ∀ κ e' σ' efs, (e, σ) -<κ>-> (e', σ', efs) → efs = [] ∧ r e' σ' Φ)

/-- A weakest preconditinon for fork-free HeapLang. -/
noncomputable def wp : @WPArg Exp Val State := gfp wpF

theorem wpF_monotone : monotone (@wpF Exp Val State Obs _) := by
  intro r1 r2 h e σ Φ hr
  rcases hr with hv | ⟨hred, hstep⟩
  · exact .inl hv
  · refine .inr ⟨hred, fun κ e' σ' efs hs => ?_⟩
    obtain ⟨hnil, h1⟩ := hstep κ e' σ' efs hs
    exact ⟨hnil, h _ _ _ h1⟩

theorem wp_unfold : @wp Exp Val State Obs _ = @wpF _ _ _ _ _ wp :=
  gfp_fix wpF_monotone

/-- Coinduction principle: an invariant closed under `wpF` is below `wp`. -/
theorem wp_coind (I : WPArg) (h : ∀ e σ Φ, I e σ Φ → wpF I e σ Φ) :
    ∀ (e : Exp) σ Φ,
      I e σ Φ → wp e σ Φ := le_gfp (x := I) h

/-- `wp` is monotone in its postcondition. -/
theorem wp_mono {e : Exp} {σ} {Q Q' : Val → State → Prop}
    (hQ : ∀ v σ, Q v σ → Q' v σ) (hwp : wp e σ Q) : wp e σ Q' := by
  refine wp_coind (fun e σ R => ∃ Q, (∀ v σ, Q v σ → R v σ) ∧ wp e σ Q)
    (fun e σ R ⟨Q, hQR, hwpQ⟩ => ?_) e σ Q' ⟨Q, hQ, hwp⟩
  rw [wp_unfold] at hwpQ
  rcases hwpQ with ⟨v, hv, hQv⟩ | ⟨hred, hstep⟩
  · exact .inl ⟨v, hv, hQR v σ hQv⟩
  · refine .inr ⟨hred, fun κ e' σ' efs hs => ?_⟩
    obtain ⟨hnil, hwp'⟩ := hstep κ e' σ' efs hs
    exact ⟨hnil, Q, hQR, hwp'⟩

theorem wp_lift_step {e : Exp} {σ Q} (hred : Reducible (e, σ))
    (hcont : ∀ κ e' σ' efs, (e, σ) -<κ>-> (e', σ', efs) → efs = [] ∧ wp e' σ' Q) :
    wp e σ Q := by rw [wp_unfold]; exact .inr ⟨hred, hcont⟩

theorem wp_bind {K : Exp → Exp} [Language.Context K] {e : Exp} {σ Q}
    (hwp : wp e σ (fun v σ' => wp (K (ToVal.ofVal v)) σ' Q)) : wp (K e) σ Q := by
  refine wp_coind
    (fun a σ Q => wp a σ Q ∨ ∃ e, a = K e ∧ wp e σ (fun v σ' => wp (K (ToVal.ofVal v)) σ' Q))
    (fun a σ Q hI => ?_) (K e) σ Q (.inr ⟨e, rfl, hwp⟩)
  rcases hI with hwp | ⟨e, rfl, hwp⟩
  · rw [wp_unfold] at hwp
    rcases hwp with hv | ⟨hred, hstep⟩
    · exact .inl hv
    · exact .inr ⟨hred, fun κ e' σ' efs hs => (hstep κ e' σ' efs hs).imp id (.inl ·)⟩
  · rw (occs := .pos [1]) [wp_unfold] at hwp
    rcases hwp with ⟨v, hv, hcont⟩ | ⟨hred, hstep⟩
    · obtain rfl : e = ToVal.ofVal v := (ToVal.coe_of_toVal_eq_some hv).symm
      rw [wp_unfold] at hcont
      exact hcont.imp id (fun ⟨hr, hs⟩ => ⟨hr, fun κ e' σ' efs hst =>
        (hs κ e' σ' efs hst).imp id (.inl ·)⟩)
    · let ⟨obs, e', σ', eₜ, hst⟩ := hred
      have hKred : Reducible (K e, σ) := ⟨obs, K e', σ', eₜ, Language.Context.primStep_fill hst⟩
      refine .inr ⟨hKred, fun κ Ke' σ' efs hs => ?_⟩
      obtain ⟨e', rfl, hes⟩ := Language.Context.primStep_fill_inv
        (Language.toVal_none_of_reducible hred) hs
      obtain ⟨hnil, hwp'⟩ := hstep κ e' σ' efs hes
      exact ⟨hnil, .inr ⟨e', rfl, hwp'⟩⟩

@[simp] theorem wp_val {v : Val} {σ Q} : wp (ToVal.ofVal v : Exp) σ Q ↔ Q v σ := by
  rw [wp_unfold]
  constructor
  · rintro (⟨v', hv', hQ⟩ | ⟨hred, _⟩)
    · rw [ToVal.toVal_coe] at hv'; cases hv'; exact hQ
    · grind [Language.toVal_none_of_reducible hred]
  · exact fun hQ => .inl ⟨v, ToVal.toVal_coe v, hQ⟩

/-- A primitive step without forks lifts to a weakest precondition. -/
theorem wp_primStep {e : Exp} {σ Φ κ e' σ' efs} (hwp : wp e σ Φ)
    (hstep : (e, σ) -<κ>-> (e', σ', efs)) : efs = [] ∧ wp e' σ' Φ := by
  rcases @wp_unfold Exp Val State Obs _ ▸ hwp with (⟨_, hv, _⟩|⟨_, hwp⟩)
  · simp [Language.val_stuck hstep] at hv
  · exact hwp _ _ _ _ hstep

theorem wp_notStuck {e : Exp} {σ Q} (hwp : wp e σ Q) : NotStuck (e, σ) := by
  rcases @wp_unfold Exp Val State Obs _ ▸ hwp with (⟨_, hv, _⟩|⟨hred, _⟩)
  · simp [NotStuck, hv]
  · exact .inr hred

theorem wp_erasedStep {e : Exp} {σ Q t' σ'} (hwp : wp e σ Q) (hstep : ([e], σ) -·->ₜₚ (t', σ')) :
    ∃ e', t' = [e'] ∧ wp e' σ' Q := by
  obtain ⟨κ, hs⟩ := hstep
  generalize hρ : ([e], σ) = ρ at hs
  cases hs with | @atomic e₀ _ _ e' _ efs hbase t₁ t₂ =>
  obtain ⟨hpool, rfl⟩ := Prod.mk.injEq .. ▸ hρ
  rcases List.append_eq_cons_iff.mp hpool.symm with ⟨rfl, heq⟩ | ⟨a, _, hcontra⟩
  · rw [List.nil_append] at hpool
    cases hpool
    obtain ⟨rfl, h⟩ := wp_primStep hwp hbase
    simpa
  · simp at hcontra

theorem wp_reach {e σ Q} (hwp : wp e σ Q) :
    ∀ {p : List Exp × State}, ([e], σ) -·->ₜₚ* p → ∃ e', p.1 = [e'] ∧ wp e' p.2 Q := by
  intro p hp
  induction hp
  next => simpa
  next p' p'' hstep hp ih =>
    obtain ⟨tq, σq⟩ := p'
    obtain ⟨e₁, rfl, hwp₁⟩ := ih
    obtain ⟨tr, σr⟩ := p''
    exact wp_erasedStep hwp₁ hp

/-- Adequacy: Any closed proof of `wp` implies `AdequateNoFork`. -/
theorem wp_adequateNoFork {e : Exp} {σ : State} {Q : Val → State → Prop}
    (hwp : wp e σ Q) : AdequateNoFork .NotStuck e σ Q where
  no_fork hreach := by
    obtain ⟨e', hq, _⟩ := wp_reach hwp hreach
    grind
  result hreach := by
    obtain ⟨e', hq, hwp'⟩ := wp_reach hwp hreach
    rw [wp_unfold] at hwp'
    rcases hwp' with ⟨_, _, _⟩ | ⟨hred, _⟩
    · grind
    · grind [Language.toVal_none_of_reducible hred]
  not_stuck _ hreach hmem := by
    obtain ⟨e', hq, hwp'⟩ := wp_reach hwp hreach
    simp only at hq
    rw [hq, List.mem_singleton] at hmem
    subst hmem
    exact wp_notStuck hwp'

scoped instance instWPPreExp : Std.Internal.Do.WP Exp Val (State → Prop) EPost.Nil where
  wpTrans e := ⟨fun Q _ σ => wp e σ Q⟩
  wp_trans_monotone e := by
    intro post post' _ _ _ hpost
    exact fun σ h => wp_mono (fun v s => hpost v s) h

end
end wp
end Nonbranching
