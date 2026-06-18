-- This code is temporarily being vendored from the Lean 4.31 release candidates
module

@[expose] public section

open Lean.Order

universe u v w z

structure PredTrans (Pred : Type u) (EPred : Type v) (α : Type w) where
  /-- Apply the predicate transformer to a postcondition and exception postcondition. -/
  apply : (α → Pred) → EPred → Pred

/-- Extensionality for predicate transformers. -/
@[ext] theorem PredTrans.ext {x y : PredTrans Pred EPred α}
    (h : ∀ post epost, x.apply post epost = y.apply post epost) : x = y := by
  cases x; cases y; congr; funext post epost; exact h post epost

/-- Partial order on predicate transformers, inherited from the function space. -/
instance [PartialOrder Pred] : PartialOrder (PredTrans Pred EPred α) where
  rel x y := x.apply ⊑ y.apply
  rel_refl := PartialOrder.rel_refl
  rel_trans h1 h2 := PartialOrder.rel_trans h1 h2
  rel_antisymm h1 h2 := PredTrans.ext fun post epost =>
    PartialOrder.rel_antisymm (h1 post epost) (h2 post epost)

/-- Chain-complete partial order on predicate transformers, for fixed-point reasoning. -/
instance [CCPO Pred] : CCPO (PredTrans Pred EPred α) where
  has_csup {c} hc := by
    let c' : ((α → Pred) → EPred → Pred) → Prop := fun f => ∃ pt, c pt ∧ pt.apply = f
    have hc' : chain c' := by
      intro _ _ ⟨pf, hpf, hpf_eq⟩ ⟨pg, hpg, hpg_eq⟩
      subst hpf_eq; subst hpg_eq
      exact hc pf pg hpf hpg
    obtain ⟨sup, hsup⟩ := CCPO.has_csup hc'
    refine ⟨⟨sup⟩, fun q => ?_⟩
    constructor
    · intro h pt hpt
      exact (hsup q.apply).mp h pt.apply ⟨pt, hpt, rfl⟩
    · intro h
      exact (hsup q.apply).mpr fun f ⟨pf, hpf, hpf_eq⟩ => by subst hpf_eq; exact h pf hpf

/-- `Monad` instance for `PredTrans`: `pure` returns the postcondition applied to the value,
and `bind` threads the postcondition through the continuation. -/
instance instMonadPredTrans (Pred : Type u) (EPred : Type v) : Monad (PredTrans Pred EPred) where
  pure x := ⟨fun post _epost => post x⟩
  bind x f := ⟨fun post epost => x.apply (fun a => (f a).apply post epost) epost⟩

/-- `PredTrans` is a lawful monad: all monad laws hold definitionally. -/
instance instLawfulMonadPredTrans (Pred : Type u) (EPred : Type v) :
    LawfulMonad (PredTrans Pred EPred) where
  map_const := funext fun _ => funext fun _ => PredTrans.ext fun _ _ => rfl
  id_map _ := PredTrans.ext fun _ _ => rfl
  seqLeft_eq _ _ := PredTrans.ext fun _ _ => rfl
  seqRight_eq _ _ := PredTrans.ext fun _ _ => rfl
  pure_seq _ _ := PredTrans.ext fun _ _ => rfl
  bind_pure_comp _ _ := PredTrans.ext fun _ _ => rfl
  bind_map _ _ := PredTrans.ext fun _ _ => rfl
  pure_bind _ _ := PredTrans.ext fun _ _ => rfl
  bind_assoc _ _ _ := PredTrans.ext fun _ _ => rfl

/-- Monotonicity property for a predicate transformer: if both `post` and `epost` grow,
then the resulting precondition grows. -/
def PredTrans.monotone [PartialOrder Pred] [PartialOrder EPred] (pt : PredTrans Pred EPred α) :=
  ∀ post post' epost epost', epost ⊑ epost' → post ⊑ post' →
    pt.apply post epost ⊑ pt.apply post' epost'

class abbrev Assertion (α : Type w) := CompleteLattice α

instance [Assertion EPred] : CCPO EPred where
  has_csup {c} _ := CompleteLattice.has_sup c

class WPPre (α : Type u) (ρ : outParam (Type v)) (Pred : outParam (Type w))
    (EPred : outParam (Type w')) [Assertion Pred] [Assertion EPred] where
  /-- The weakest precondition transformer for a monadic program. -/
  wpTrans : α → PredTrans Pred EPred ρ
  /-- Monotonicity: weaker postconditions yield weaker preconditions. -/
  wp_trans_monotone (x : α) : wpTrans x |>.monotone

class WPMonad (m : Type u → Type v) (Pred : outParam (Type w)) (EPred : outParam (Type w'))
    [Monad m] [Assertion Pred] [Assertion EPred] [∀ α, WPPre (m α) α Pred EPred]
    extends LawfulMonad m where
  /-- Soundness of `bind`: composing WPs is at least as strong as the WPMonad of `>>=`. -/
  wp_trans_bind (x : m α) (f : α → m β) :
    WPPre.wpTrans x >>= (WPPre.wpTrans <| f ·) ⊑ WPPre.wpTrans (x >>= f)
  /-- Monotonicity: weaker postconditions yield weaker preconditions. -/
  wp_trans_monotone (x : m α) : WPPre.wpTrans x |>.monotone

/- Example:

-- The simplest IMP + omni-semantics

abbrev Var := String
abbrev State := Var → Nat

def State.update (s : State) (x : Var) (v : Nat) : State :=
  fun y => if y = x then v else s y

@[simp] theorem State.update_same (s : State) (x : Var) (v : Nat) :
    (s.update x v) x = v := by simp [State.update]

@[simp] theorem State.update_other (s : State) (x y : Var) (v : Nat) (h : y ≠ x) :
    (s.update x v) y = s y := by simp [State.update, h]

-- Expressions (arithmetic; conditions via ≠ 0)
inductive Expr
  | lit (n : Nat)
  | var (x : Var)
  | add (e₁ e₂ : Expr)

@[simp] def Expr.eval (s : State) : Expr → Nat
  | .lit n => n
  | .var x => s x
  | .add e₁ e₂ => e₁.eval s + e₂.eval s

-- Commands
inductive Cmd
  | skip
  | assign (x : Var) (e : Expr)
  | seq (c₁ c₂ : Cmd)
  | ite (cond : Expr) (c₁ c₂ : Cmd)
  | while (cond : Expr) (body : Cmd)

-- Omni-semantics as WP (structurally recursive on Cmd)
def wp : Cmd → (State → Prop) → State → Prop
  | .skip, Q, s => Q s
  | .assign x e, Q, s => Q (s.update x (e.eval s))
  | .seq c₁ c₂, Q, s => wp c₁ (fun s' => wp c₂ Q s') s
  | .ite cond c₁ c₂, Q, s =>
    if cond.eval s ≠ 0 then wp c₁ Q s else wp c₂ Q s
  | .while cond body, Q, s =>
    ∃ I : State → Prop,
      I s ∧
      (∀ s', I s' → cond.eval s' ≠ 0 → wp body I s') ∧
      (∀ s', I s' → cond.eval s' = 0 → Q s')

instance : PartialOrder Prop where
  rel p q := p → q
  rel_refl := id
  rel_trans := fun h1 h2 x => h2 (h1 x)
  rel_antisymm := fun h1 h2 => propext ⟨h1, h2⟩

/-- Supremum for Prop: true iff some element of the set is true -/
def propSup (c : Prop → Prop) : Prop := ∃ p, c p ∧ p

theorem propSup_is_sup (c : Prop → Prop) : is_sup c (propSup c) := by
  intro y
  constructor
  · intro hsup z hcz hz
    apply hsup
    exact Exists.intro z (And.intro hcz hz)
  · intro h ⟨z, hcz, hz⟩
    exact h z hcz hz

instance : CompleteLattice Prop where
  has_sup c := ⟨propSup c, propSup_is_sup c⟩

-/

/-- The empty exception postcondition type, used when a monad has no exception layers. -/
structure EPost.nil : Type

instance : PartialOrder EPost.nil where
  rel _ _ := True
  rel_refl := trivial
  rel_trans _ _ := trivial
  rel_antisymm := fun {p q} _ _ => by cases p; cases q; rfl

instance : CompleteLattice EPost.nil where
  has_sup _ := ⟨EPost.nil.mk, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

/- Example (continued):

instance : WPPre Cmd Unit (State → Prop) EPost.nil where
  wpTrans cmd := PredTrans.mk fun Q _ s => wp cmd (Q ()) s
  wp_trans_monotone := sorry
-/
