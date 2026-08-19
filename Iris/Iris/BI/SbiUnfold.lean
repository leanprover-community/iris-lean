/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.SIProp
public import Iris.BI.SbiUnfoldAttr

@[expose] public section

/-!
# `sbi_unfold`

A simp set for proving pure SBI facts based on the model.

For example `✓ x ⊣⊢@{PROP} ✓ x.1 ∧ ✓ x.2` converts to `∀ n, ✓{n} x ↔ ✓{n} x.1 ∧ ✓{n} x.2`.

The `sbi_norm` simp set targets implications `⊢` and bi-implications `⊣⊢`. It consists
of three kinds of rules:
- Pushing `.holds n` inwards, and under downward closures `downClose` wherever applicable.
- Converting plain propositions into `<si_pure>`.
- Converting a root `<si_pure>` modality into a statement about `.holds n`

New rules can be added to the simp set with `@[sbi_norm]`. You should add the following:
- A rule of the form `myConn x y = <si_pure> _`
- A rule changing `(myConn x y).holds` into `x.holds` and `y.holds`, under a `downClose` if possible.

## The two sets

`sbi_norm` reaches the step-indexed normal form where down closures are `downClose` terms.
To unfold these as well, use the `sbi_model` simp set.
```
simp only [sbi_norm]
simp only [sbi_model]
```
Simplifying by `sbi_model` must happen after normalization, as it prevents it.
-/

namespace Iris
open BI OFE CMRA Std

namespace SiProp

/- ## Recursive Rules for pushing `.holds` downwards  -/

@[sbi_norm] theorem imp_holds {P Q : SiProp} {n} :
    (iprop(P → Q) : SiProp).holds n = (downClose fun m => P.holds m → Q.holds m).holds n := rfl

@[sbi_norm] theorem wand_holds {P Q : SiProp} {n} :
    (iprop(P -∗ Q) : SiProp).holds n = (downClose fun m => P.holds m → Q.holds m).holds n := rfl

/-- `↔` keeps its shape: a down closure of a meta-level `↔`, not a conjunction of
two implications. Decomposing it would erase the difference between `P ↔ Q` and a
conjunction the user wrote, which Rocq's `sbi_unfold_iff` keeps. -/
@[sbi_norm] theorem iff_holds {P Q : SiProp} {n} :
    (iprop(P ↔ Q) : SiProp).holds n
      ↔ (downClose fun m => P.holds m ↔ Q.holds m).holds n where
  mp h m hm := ⟨h.1 m hm, h.2 m hm⟩
  mpr h := ⟨fun m hm => (h m hm).mp, fun m hm => (h m hm).mpr⟩

/-- `∗-∗` is `↔` on `SiProp`. -/
@[sbi_norm] theorem wandIff_holds {P Q : SiProp} {n} :
    (iprop(P ∗-∗ Q) : SiProp).holds n
      ↔ (downClose fun m => P.holds m ↔ Q.holds m).holds n := iff_holds

/-- Named match statement for `▷`, for clarity. -/
def laterP (φ : Nat → Prop) : Nat → Prop
  | 0 => True
  | m + 1 => φ m

@[simp] theorem laterP_zero {φ : Nat → Prop} : laterP φ 0 = True := rfl

@[simp] theorem laterP_succ {φ : Nat → Prop} {m} : laterP φ (m + 1) = φ m := rfl

@[sbi_norm] theorem later_holds {P : SiProp} {n} :
    (iprop(▷ P) : SiProp).holds n = laterP (fun m => P.holds m) n := rfl

@[sbi_norm] theorem pure_holds' {φ : Prop} {n} : (pure φ).holds n ↔ φ := .rfl

/-- Unfold the `downClosed` predicate. This takes an expression which has been fully converted
into `downClose` expressions, and unlocks the phase of simplification for removing redundant
quantifers. -/
@[sbi_model] theorem downClose_holds {φ : Nat → Prop} {n} :
    (downClose φ).holds n = ∀ m ≤ n, φ m := rfl

theorem entails_iff {P Q : SiProp} :
    (P ⊢@{SiProp} Q) ↔ ∀ n, P.holds n → Q.holds n := .rfl

theorem biEntails_iff {P Q : SiProp} :
    (P ⊣⊢@{SiProp} Q) ↔ ∀ n, P.holds n ↔ Q.holds n :=
  ⟨fun h n => ⟨h.mp n, h.mpr n⟩, fun h => ⟨fun n => (h n).mp, fun n => (h n).mpr⟩⟩

theorem emp_valid_iff {P : SiProp} : (⊢@{SiProp} P) ↔ ∀ n, P.holds n :=
  ⟨fun h n => h n trivial, fun h n _ => h n⟩

end SiProp

attribute [sbi_norm]
  SiProp.and_holds SiProp.sep_holds SiProp.or_holds SiProp.exists_holds
  SiProp.forall_holds SiProp.internalEq_holds SiProp.cmraValid_holds

/-! ## Downwards closed predicates  -/

class DownClosed (φ : Nat → Prop) : Prop where
  downClosed {n m} : m ≤ n → φ n → φ m

export DownClosed (downClosed)

instance downClosed_holds (P : SiProp) : DownClosed (fun n => P.holds n) where
  downClosed hle h := P.closed h hle

instance downClosed_downClose (φ : Nat → Prop) :
    DownClosed (fun n => (SiProp.downClose φ).holds n) where
  downClosed hle h _ hle' := h _ (Nat.le_trans hle' hle)

instance downClosed_validN [CMRA α] (a : α) : DownClosed (fun n => ✓{n} a) where
  downClosed hle h := validN_of_le hle h

instance downClosed_dist [OFE α] (a b : α) : DownClosed (fun n => a ≡{n}≡ b) where
  downClosed hle h := h.le hle

instance downClosed_incN [CMRA α] (a b : α) : DownClosed (fun n => a ≼{n} b) where
  downClosed hle h := incN_of_incN_le hle h

instance downClosed_const (φ : Prop) : DownClosed (fun _ => φ) where
  downClosed _ h := h

instance downClosed_and (φ ψ : Nat → Prop) [DownClosed φ] [DownClosed ψ] :
    DownClosed (fun n => φ n ∧ ψ n) where
  downClosed hle h := ⟨downClosed hle h.1, downClosed hle h.2⟩

instance downClosed_or (φ ψ : Nat → Prop) [DownClosed φ] [DownClosed ψ] :
    DownClosed (fun n => φ n ∨ ψ n) where
  downClosed hle := Or.imp (downClosed hle) (downClosed hle)

instance downClosed_forall {α : Sort _} (φ : α → Nat → Prop) [∀ x, DownClosed (φ x)] :
    DownClosed (fun n => ∀ x, φ x n) where
  downClosed hle h x := downClosed hle (h x)

instance downClosed_exists {α : Sort _} (φ : α → Nat → Prop) [∀ x, DownClosed (φ x)] :
    DownClosed (fun n => ∃ x, φ x n) where
  downClosed hle := fun ⟨x, h⟩ => ⟨x, downClosed hle h⟩

/-! ## Normalization: pull down closures outward -/

/-- `∀ n` eliminates down closures. -/
@[sbi_norm] theorem downClose_absorb {φ : Nat → Prop} :
    (∀ n, (SiProp.downClose φ).holds n) ↔ ∀ n, φ n :=
  ⟨fun h n => h n n (Nat.le_refl n), fun h _ m _ => h m⟩

/-- When the antecedent of an implicaition is downwards closed, it eliminates `downClosed`
from the conclusion. -/
@[sbi_norm] theorem downClose_absorb_imp {H ψ : Nat → Prop} [DownClosed H] :
    (∀ n, H n → (SiProp.downClose ψ).holds n) ↔ ∀ n, H n → ψ n where
  mp h n hH := h n hH n (Nat.le_refl n)
  mpr h _ hH m hm := h m (downClosed hm hH)

/-- A down closure in the conclusion of an implication merges with the enclosing
one, when the antecedent is down closed. -/
@[sbi_norm] theorem downClose_imp {H ψ : Nat → Prop} [DownClosed H] {n} :
    (SiProp.downClose fun m => H m → (SiProp.downClose ψ).holds m).holds n
      ↔ (SiProp.downClose fun m => H m → ψ m).holds n where
  mp h m hm hH := h m hm hH m (Nat.le_refl m)
  mpr h _ hm hH k hk := h k (Nat.le_trans hk hm) (downClosed hk hH)

/-- Two down closures under a conjunction merge. -/
@[sbi_norm] theorem downClose_and {φ ψ : Nat → Prop} {n} :
    ((SiProp.downClose φ).holds n ∧ (SiProp.downClose ψ).holds n)
      ↔ (SiProp.downClose fun m => φ m ∧ ψ m).holds n :=
  ⟨fun h m hm => ⟨h.1 m hm, h.2 m hm⟩,
   fun h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩⟩

/-- A down closure under a universal quantifier merges. -/
@[sbi_norm] theorem downClose_forall {α : Type _} {φ : α → Nat → Prop} {n} :
    (∀ x, (SiProp.downClose (φ x)).holds n)
      ↔ (SiProp.downClose fun m => ∀ x, φ x m).holds n :=
  ⟨fun h m hm x => h x m hm, fun h x m hm => h m hm x⟩

/-- A down closure under `▷` merges. -/
@[sbi_norm] theorem downClose_later {φ : Nat → Prop} {n} :
    SiProp.laterP (fun m => (SiProp.downClose φ).holds m) n
      ↔ (SiProp.downClose fun k => SiProp.laterP φ k).holds n := by
  refine ⟨fun h m _ => ?_, fun h => ?_⟩
  · match m with
    | 0 => trivial
    | m + 1 =>
      match n with
      | 0 => omega
      | _ + 1 => exact h m (by omega)
  · match n with
    | 0 => trivial
    | _ + 1 => exact fun m _ => h (m + 1) (by omega)

#rocq_ignore_file BI "sbi_unfold.v" "Implemented using the `sbi_norm` and `sbi_model` simp sets."

end Iris
