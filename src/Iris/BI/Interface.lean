import Iris.Std.Classes

namespace Iris.BI
open Iris.Std
open Lean

class BIBase (car : Type) extends Equiv car where
  entails : car → car → Prop
  emp : car
  pure : Prop → car
  and : car → car → car
  or : car → car → car
  impl : car → car → car
  «forall» : (α → car) → car
  «exists» : (α → car) → car
  sep : car → car → car
  wand : car → car → car


section Syntax

-- define `iprop` embedding in `term`
syntax:max "`[iprop| " term "]" : term
syntax:max "`[term| " term "]" : term

macro:25 P:term:29 " ⊢ " Q:term:25 : term => `(BIBase.entails `[iprop| $P] `[iprop| $Q])

-- allow fallback to `term`
macro_rules
  | `(`[iprop| `[term| $t]]) => `($t)
  | `(`[iprop| $t])          => `($t)

-- carry `iprop` over some `term` constructs
macro_rules
  | `(`[iprop| ($P)])  => `(`[iprop| $P])
  | `(`[iprop| $P $Q]) => `(`[iprop| $P] `[iprop| $Q])

-- define new `iprop` syntax
syntax "⌜" term "⌝" : term
syntax:35 term:36 " ∗ " term:35 : term
syntax:27 term:28 " -∗ " term:27 : term

-- overload syntax where necessary
syntax:26 "∀ " explicitBinders ", " term:26 : term

-- define `iprop` syntax interpretation
macro_rules
  | `(`[iprop| emp])       => `(BIBase.emp)
  | `(`[iprop| ⌜$φ⌝])      => `(BIBase.pure $φ)
  | `(`[iprop| $P ∧ $Q])   => `(BIBase.and `[iprop| $P] `[iprop| $Q])
  | `(`[iprop| $P ∨ $Q])   => `(BIBase.or `[iprop| $P] `[iprop| $Q])
  | `(`[iprop| $P → $Q])   => `(BIBase.impl `[iprop| $P] `[iprop| $Q])
  | `(`[iprop| ∀ $xs, $Ψ]) => do expandExplicitBinders ``BIBase.forall xs (← `(`[iprop| $Ψ]))
  | `(`[iprop| ∃ $xs, $Ψ]) => do expandExplicitBinders ``BIBase.exists xs (← `(`[iprop| $Ψ]))
  | `(`[iprop| $P ∗ $Q])   => `(BIBase.sep `[iprop| $P] `[iprop| $Q])
  | `(`[iprop| $P -∗ $Q])  => `(BIBase.wand `[iprop| $P] `[iprop| $Q])

-- define additional `iprop` syntax interpretation
macro_rules
  | `(`[iprop| True])  => `(BIBase.pure True)
  | `(`[iprop| False]) => `(BIBase.pure False)
  | `(`[iprop| ¬$P])   => `(`[iprop| $P → False])

end Syntax


class BI (car : Type) extends BIBase car where
  entails_po : PreOrder entails
  equiv_entails (P Q : car) : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P)

  pure_intro (φ : Prop) (P : car) : φ → P ⊢ ⌜φ⌝
  pure_elim' (φ : Prop) (P : car) : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P

  and_elim_l (P Q : car) : P ∧ Q ⊢ P
  and_elim_r (P Q : car) : P ∧ Q ⊢ Q
  and_intro (P Q R : car) : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R

  or_intro_l (P Q : car) : P ⊢ P ∨ Q
  or_intro_r (P Q : car) : Q ⊢ P ∨ Q
  or_elim (P Q R : car) : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R

  impl_intro_r (P Q R : car) : (P ∧ Q ⊢ R) → P ⊢ Q → R
  impl_elim_l' (P Q R : car) : (P ⊢ Q → R) → P ∧ Q ⊢ R

  forall_intro (P : car) (Ψ : α → car) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a
  forall_elim {Ψ : α → car} (a : α) : (∀ a, Ψ a) ⊢ Ψ a

  exist_intro {Ψ : α → car} (a : α) : Ψ a ⊢ ∃ a, Ψ a
  exist_elim (Φ : α → car) (Q : car) : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q

  sep_mono (P P' Q Q' : car) : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'
  emp_sep_1 (P : car) : P ⊢ emp ∗ P
  emp_sep_2 (P : car) : emp ∗ P ⊢ P
  sep_comm' (P Q : car) : P ∗ Q ⊢ Q ∗ P
  sep_assoc' (P Q R : car) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)
  wand_intro_r (P Q R : car) : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R
  wand_elim_l' (P Q R : car) : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R

end Iris.BI
