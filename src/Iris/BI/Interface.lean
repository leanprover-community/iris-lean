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

declare_syntax_cat iprop

syntax:max "`[iprop| " iprop "]" : term
macro:25 P:iprop:29 " ⊢ " Q:iprop:26 : term => `(BIBase.entails `[iprop| $P] `[iprop| $Q])

syntax:max ident : iprop
syntax:max "(" iprop ")" : iprop
syntax:arg iprop:arg colGt iprop:max : iprop

macro_rules
  | `(`[iprop| $id:ident])   => `($id)
  | `(`[iprop| ($P)])        => `(`[iprop| $P])
  | `(`[iprop| $P $Q:iprop]) => `(`[iprop| $P] `[iprop| $Q])

syntax "⌜" term "⌝" : iprop
syntax:35 iprop:36 " ∧ " iprop:35 : iprop
syntax:30 iprop:31 " ∨ " iprop:30 : iprop
syntax:27 iprop:28 " → " iprop:27 : iprop
syntax:26 "∀ " explicitBinders ", " iprop:26 : iprop
syntax:26 "∃ " explicitBinders ", " iprop:26 : iprop
syntax:35 iprop:36 " ∗ " iprop:35 : iprop
syntax:27 iprop:28 " -∗ " iprop:27 : iprop

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

syntax:max "¬" iprop:40 : iprop

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
