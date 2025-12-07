/-
Test file for ipose tactic
-/
import Iris.BI
import Iris.ProofMode

open Iris

namespace pose

/-- Pose a Lean proof `⊢ Q` and use it directly. -/
theorem lean_proof [BI PROP] (Q : PROP) (H : ⊢ Q) : ⊢ Q := by
  istart
  ipose H as HQ
  iexact HQ

/-- Pose a Lean entailment `P ⊢ Q` and apply it. -/
theorem lean_entailment [BI PROP] (P Q : PROP) (H : P ⊢ Q) : P ⊢ Q := by
  iintro HP
  ipose H as HPQ
  iapply HPQ with HP

/-- Pose with forall specialization using `$!`. -/
theorem forall_specialization [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  ipose H $! a, b as H'
  iapply H' with HP

/-- Pose intuitionistic forall with specialization. -/
theorem forall_specialization_intuitionistic [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  ipose H $! a, b as H'
  iapply H' with HP

/-- Pose a hypothesis guarded by a Prop implication. -/
theorem prop_implication [BI PROP] (cond : Prop) (Q R : PROP) (Hcond : cond) (H : cond → (Q ⊢ R)) : Q ⊢ R := by
  iintro HQ
  ipose H as HR
  exact Hcond
  iapply HR with HQ

/-- Pose a hypothesis guarded by nested Prop implications. -/
theorem prop_implication_nested [BI PROP] (c1 c2 : Prop) (Q R : PROP) (Hc1 : c1) (Hc2 : c2)
    (H : c1 → c2 → (Q ⊢ R)) : Q ⊢ R := by
  iintro HQ
  ipose H as HR
  · exact Hc1
  · exact Hc2
  iapply HR with HQ

/-- Pose into an empty spatial context. -/
theorem empty_context [BI PROP] (cond : Prop) (Q : PROP) (Hcond : cond) (H : cond → (⊢ Q)) : ⊢ Q := by
  istart
  ipose H as HQ
  exact Hcond
  iexact HQ

/-- Pose a universally quantified local hypothesis with Prop guard. -/
theorem forall_local_with_guard [BI PROP] (cond : A → Prop) (Q R : A → PROP)
    (HH : ∀ a', cond a' → (Q a' ⊢ R a')) (a : A) (Hcond : cond a) : Q a ⊢ R a := by
  iintro HQ
  ipose HH as HR
  · exact Hcond
  iapply HR with HQ

/-- Helper theorem for testing pose with global theorems. -/
theorem helper_forall_guard [BI PROP] (cond : A → Prop) (Q : A → PROP) :
    ∀ (a' : A), cond a' → (Q a' ⊢ Q a') :=
  fun _ _ => BI.BIBase.Entails.rfl

/-- Pose a global theorem with partial application. -/
theorem global_theorem_application [BI PROP] (cond : A → Prop) (Q : A → PROP) (a : A) (Hcond : cond a) :
    Q a ⊢ Q a := by
  iintro HQ
  ipose (helper_forall_guard cond Q) as HR
  · exact Hcond
  · iapply HR with HQ

/-- A simple let-binding that zeta-reduces to a base entailment.
    This works since whnf reduces `let f := P ⊢ Q; f` to `P ⊢ Q`. -/
theorem let_simple_zeta [BI PROP] (P Q : PROP) (H : let f := P ⊢ Q; f) : P ⊢ Q := by
  iintro HP
  ipose H as HPQ
  iapply HPQ with HP

/-- Test that handleDependentArrows correctly strips Lean-level foralls
    (these are syntactically visible, not hidden behind let). -/
theorem lean_forall_visible [BI PROP] (P Q : α → PROP) (a : α)
    (H : ∀ x, P x ⊢ Q x) : P a ⊢ Q a := by
  iintro HP
  ipose H as HPQ
  iapply HPQ with HP

/-- Test Lean-level forall with Prop guard (both visible). -/
theorem lean_forall_with_guard [BI PROP] (cond : α → Prop) (P Q : α → PROP) (a : α) (Hcond : cond a)
    (H : ∀ x, cond x → (P x ⊢ Q x)) : P a ⊢ Q a := by
  iintro HP
  ipose H as HPQ
  · exact Hcond
  iapply HPQ with HP

/-- Multiple Lean-level foralls. -/
theorem lean_multiple_foralls [BI PROP] (P Q : α → β → PROP) (a : α) (b : β)
    (H : ∀ x y, P x y ⊢ Q x y) : P a b ⊢ Q a b := by
  iintro HP
  ipose H as HPQ
  iapply HPQ with HP

/-- A let-binding that hides a forall (now works with whnf reduction). -/
theorem let_hides_forall [BI PROP] (P Q : α → PROP) (a : α)
    (H : let f := fun x => P x ⊢ Q x; f a) : P a ⊢ Q a := by
  iintro HP
  ipose H as HPQ
  iapply HPQ with HP

/-- A let-binding that hides a Prop implication (now works with whnf reduction). -/
theorem let_hides_implication [BI PROP] (cond : Prop) (P Q : PROP) (Hcond : cond)
    (H : let f := fun (c : Prop) => c → (P ⊢ Q); f cond) : P ⊢ Q := by
  iintro HP
  ipose H as HPQ
  · exact Hcond
  iapply HPQ with HP

end pose
