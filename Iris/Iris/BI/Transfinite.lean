/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.BI.DerivedLawsLater
public import Iris.BI.Plainly
public import Iris.BI.Sbi
public import Iris.BI.Updates
public import Iris.Algebra.StepIndexTransfinite

/-! # Generic BI notions of Transfinite Iris

- The *big later* `⧍ P := ∃ n, ▷^n P` (Transfinite Iris, `base_logic/upred.v`), which describes
  that `P` holds after finitely many, but an unbounded number of, steps.
- The *satisfiability* predicate (Transfinite Iris, `bi/satisfiable.v`), which connects truth
  inside the logic with truth outside of it. Its rule for existential quantification
  (`Satisfiable.exists`) is the *existential property* that requires transfinite step-indices
  (`SIdxLarge`).
-/

@[expose] public section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.BI
open Iris.Std BIBase

/-! ## The big later -/

/-- The big later `⧍ P := ∃ n, ▷^n P`: `P` holds after finitely many steps (Transfinite Iris). -/
def bigLater [BI PROP] (P : PROP) : PROP := iprop(∃ n : Nat, ▷^[n] P)

syntax:max "⧍ " term:40 : term

macro_rules
  | `(iprop(⧍%$tk $P)) => ``($(wrapIprop tk ``bigLater) iprop($P))

delab_rule bigLater
  | `($_ $P) => do ``(iprop(⧍ $(← unpackIprop P)))

/-- Iterated big later, `⧍^n P` (Transfinite Iris). -/
def bigLaterN [BI PROP] (n : Nat) (P : PROP) : PROP := n.repeat bigLater P

section BigLater

variable [BI PROP]

theorem bigLater_mono {P Q : PROP} (h : P ⊢ Q) : ⧍ P ⊢ ⧍ Q :=
  exists_mono fun n => laterN_mono n h

theorem bigLater_intro {P : PROP} : P ⊢ ⧍ P :=
  exists_intro_trans 0 .rfl

theorem later_bigLater {P : PROP} : ▷ P ⊢ ⧍ P :=
  exists_intro_trans 1 .rfl

theorem laterN_bigLater (n : Nat) {P : PROP} : ▷^[n] P ⊢ ⧍ P :=
  exists_intro_trans n .rfl

-- Note: `⧍ ⧍ P ⊢ ⧍ P` would require commuting `▷^n` with `∃`, which fails for transfinite
-- step-indices. This is why Transfinite Iris iterates `⧍` explicitly (`bigLaterN`).

instance bigLater_ne : OFE.NonExpansive (bigLater (PROP := PROP)) where
  ne _ _ _ h := exists_ne fun n => (laterN_ne n).ne h

theorem bigLaterN_zero {P : PROP} : bigLaterN 0 P = P := rfl

theorem bigLaterN_succ {n : Nat} {P : PROP} : bigLaterN (n + 1) P = iprop(⧍ bigLaterN n P) := rfl

theorem bigLaterN_mono (n : Nat) {P Q : PROP} (h : P ⊢ Q) : bigLaterN n P ⊢ bigLaterN n Q := by
  induction n with
  | zero => exact h
  | succ n ih => exact bigLater_mono ih

/-- The big later distributes over separating conjunction (the binary case of Rocq's
`list_big_later`). -/
theorem bigLater_sep {P Q : PROP} : ⧍ P ∗ ⧍ Q ⊢ ⧍ (P ∗ Q) :=
  sep_exists_right.mp.trans <| exists_elim fun n1 => sep_exists_left.mp.trans <| exists_elim fun n2 =>
    (sep_mono (laterN_le (Nat.le_add_right n1 n2)) (laterN_le (Nat.le_add_left n2 n1))).trans <|
      (laterN_sep_2 _).trans (laterN_bigLater _)

end BigLater

section BigLaterPlain

variable [Sbi PROP]

/-- Rocq: `plain_big_later`. -/
@[rocq_alias plain_big_later]
instance bigLater_plain (P : PROP) [Plain P] : Plain iprop(⧍ P) :=
  inferInstanceAs (Plain iprop(∃ n : Nat, ▷^[n] P))

/-- Rocq: `plain_big_laterN`. -/
@[rocq_alias plain_big_laterN]
instance bigLaterN_plain (n : Nat) (P : PROP) [Plain P] : Plain (bigLaterN n P) := by
  induction n with
  | zero => exact inferInstanceAs (Plain P)
  | succ n ih => exact inferInstanceAs (Plain iprop(⧍ bigLaterN n P))

end BigLaterPlain

/-! ## Satisfiability -/

/-- A satisfiability predicate for a BI with a basic update modality (Transfinite Iris,
`satisfiable_mixin`/`Satisfiable`).

The rules for existential quantification require properties of the step-index type:
`finite_exists` holds for every type of step-indices (Lean is classical, so Transfinite Iris's
`FiniteExistential` is always available), while `exists` requires `SIdxLarge`. -/
@[rocq_alias Satisfiable]
class Satisfiable.{w, v} {SI : outParam (Type _)} [instSI : outParam (SIdx SI)] (PROP : Type _)
    [outParam (Sbi (SI := SI) PROP)] [outParam (BIUpdate PROP)] where
  satisfiable : PROP → Prop
  intro {P : PROP} : (True ⊢ P) → satisfiable P
  mono {P Q : PROP} : satisfiable P → (P ⊢ Q) → satisfiable Q
  elim {P : PROP} [Plain P] : satisfiable P → True ⊢ P
  later {P : PROP} : satisfiable iprop(▷ P) → satisfiable P
  finite_exists {X : Type w} {P : X → PROP} {Q : X → Prop} (l : List X) :
    (∀ x, Q x → x ∈ l) → (∀ x, P x ⊢ ⌜Q x⌝) → satisfiable iprop(∃ x, P x) → ∃ x, satisfiable (P x)
  exists_ [SIdxLarge.{v} SI] {X : Type v} {P : X → PROP} :
    satisfiable iprop(∃ x, P x) → ∃ x, satisfiable (P x)
  bupd {P : PROP} : satisfiable iprop(|==> P) → satisfiable P

namespace Satisfiable

variable [Sbi PROP] [BIUpdate PROP] [Satisfiable.{0, v} PROP]

theorem forall_elim {X : Type} (x : X) {P : X → PROP} (h : satisfiable iprop(∀ x, P x)) :
    satisfiable (P x) :=
  mono h (BI.forall_elim x)

theorem imp {P Q : PROP} (h : satisfiable iprop(P → Q)) (hP : True ⊢ P) : satisfiable Q :=
  mono h <| (and_intro (true_intro.trans hP) .rfl).trans imp_elim_right

theorem wand {P Q : PROP} (h : satisfiable iprop(P -∗ Q)) (hP : True ⊢ P) : satisfiable Q :=
  mono h <| true_sep_mpr.trans ((sep_mono_left hP).trans wand_elim_right)

theorem pers [BIAffine PROP] {P : PROP} (h : satisfiable iprop(<pers> P)) : satisfiable P :=
  mono h persistently_elim

theorem intuitionistically {P : PROP} (h : satisfiable iprop(□ P)) : satisfiable P :=
  mono h intuitionistically_elim

theorem or {P Q : PROP} (h : satisfiable iprop(P ∨ Q)) : satisfiable P ∨ satisfiable Q := by
  have h' : satisfiable iprop(∃ b : Bool, if b then P else Q) :=
    mono h (or_elim (exists_intro_trans true .rfl) (exists_intro_trans false .rfl))
  obtain ⟨b, hb⟩ := finite_exists (Q := fun _ => True) [true, false]
    (fun b _ => by cases b <;> simp) (fun _ => pure_intro trivial) h'
  cases b
  · exact .inr hb
  · exact .inl hb

theorem laterN {P : PROP} (n : Nat) (h : satisfiable iprop(▷^[n] P)) : satisfiable P := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (later h)

end Satisfiable

end Iris.BI
