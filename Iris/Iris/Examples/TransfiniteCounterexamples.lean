/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.UPred.Transfinite

/-! # Counterexamples of Transfinite Iris

This file ports `theories/examples/counterexamples.v` of Transfinite Iris:

- `transfinite_no_bounded_existential`: a step-index type with a limit `ω` of the finite indices
  cannot validate the *bounded* existential property for `ℕ` at `ω`.
- `no_later_existential_commuting`: a step-indexed logic with a sound later, Löb induction and the
  existential property for `ℕ` cannot let `▷` commute with `∃`. This is why Transfinite Iris drops
  `later_exist_false` for transfinite step-indices.
- `not_limitPreserving_entails`: entailment between `UPred`s is not limit preserving for
  step-indices with a limit `ω` of the finite indices (Rocq:
  `bounded_limit_preserving_entails_counterexample`).
- `ne_not_preserve_lbcompl`: non-expansive maps do not preserve limits of bounded chains (Rocq:
  `ne_does_not_preserve_limits`/`test`).

The hypotheses on the limit ordinal `ω` of the Rocq sections are bundled as `IsOmega`.
-/

@[expose] public section

namespace Iris.Examples.TransfiniteCounterexamples
open Iris SIdx

variable {SI : Type _} [instSI : SIdx SI]

/-- `ω` is the least limit index: it is above all finite indices, and only those are below it. -/
structure IsOmega (ω : SI) : Prop where
  iter_lt (n : Nat) : Nat.repeat SIdx.succ n 0 < ω
  lt_iter (a : SI) : a < ω → ∃ n : Nat, a = Nat.repeat SIdx.succ n 0

theorem IsOmega.limit {ω : SI} (h : IsOmega ω) : Limit ω where
  succ_lt m hm := by
    obtain ⟨n, rfl⟩ := h.lt_iter m hm
    exact h.iter_lt (n + 1)
  ne_zero h0 := lt_irrefl (0 : SI) (h0 ▸ h.iter_lt 0)

theorem forall_lt_lt_iff {k c : SI} : (∀ m, m < k → m < c) ↔ k ≤ c :=
  ⟨fun h => le_ngt.mpr fun hck => lt_irrefl c (h c hck), fun h _ hm => lt_le_trans hm h⟩

/-! ## The bounded existential property fails at `ω` -/

/-- Downward-closed predicates on step-indices (Rocq: `sProp`). -/
structure SProp (SI : Type _) [SIdx SI] where
  prop : SI → Prop
  down {a b : SI} : a < b → prop b → prop a

/-- Later on `SProp` (Rocq: `sProp_later`). -/
def SProp.later (P : SProp SI) : SProp SI where
  prop c := ∀ c', c' < c → P.prop c'
  down hab h c' hc' := h c' (lt_trans hc' hab)

/-- Falsity on `SProp` (Rocq: `sProp_false`). -/
def SProp.false : SProp SI where
  prop _ := False
  down _ h := h

/-- Existential quantification on `SProp` (Rocq: `sProp_ex`). -/
def SProp.ex {X : Type _} (Φ : X → SProp SI) : SProp SI where
  prop a := ∃ x, (Φ x).prop a
  down hab := fun ⟨x, h⟩ => ⟨x, (Φ x).down hab h⟩

/-- The bounded existential property at `a` (Rocq: `bounded_existential`). -/
def BoundedExistential (X : Type _) (Φ : X → SProp SI) (a : SI) : Prop :=
  (∀ b, b < a → ∃ x, (Φ x).prop b) → ∃ x, ∀ b, b < a → (Φ x).prop b

/-- The existential property (Rocq: `existential`). -/
def Existential (X : Type _) (Φ : X → SProp SI) : Prop :=
  (∀ a, ∃ x, (Φ x).prop a) → ∃ x, ∀ a, (Φ x).prop a

theorem SProp.laterN_false_prop (n : Nat) {b : SI} :
    (Nat.repeat SProp.later n SProp.false).prop b ↔ b < Nat.repeat SIdx.succ n 0 := by
  induction n generalizing b with
  | zero => exact ⟨False.elim, not_lt_zero b⟩
  | succ n ih =>
    change (∀ c, c < b → _) ↔ _
    simp only [ih]
    exact forall_lt_lt_iff.trans lt_succ_r.symm

@[rocq_alias transfinite_no_bounded_existential]
theorem transfinite_no_bounded_existential {ω : SI} (hω : IsOmega ω) :
    ¬ BoundedExistential Nat (fun n => Nat.repeat SProp.later n SProp.false) ω := by
  intro H
  obtain ⟨n, hn⟩ := H fun b hb => by
    obtain ⟨m, rfl⟩ := hω.lt_iter b hb
    exact ⟨m + 1, (SProp.laterN_false_prop (m + 1)).mpr (lt_succ_self _)⟩
  exact lt_irrefl _ ((SProp.laterN_false_prop n).mp (hn _ (hω.iter_lt n)))

/-! ## Later cannot commute with existentials -/

section NoLaterExists

variable {PROP : Type _} (entails : PROP → PROP → Prop) (TRUE FALSE : PROP) (later : PROP → PROP)
  (ex : (Nat → PROP) → PROP)

/-- A step-indexed logic (given by its entailment, truth, falsity, later and existential
quantification over `ℕ`) with a sound later, Löb induction, and the existential property for `ℕ`
cannot have `▷ (∃ n, Φ n) ⊢ ∃ n, ▷ Φ n` (Rocq: `no_later_existential_commuting`). -/
@[rocq_alias no_later_existential_commuting]
theorem no_later_existential_commuting
    (cut : ∀ {P Q R}, entails P Q → entails Q R → entails P R)
    (assumption : ∀ P, entails P P)
    (ex_intro : ∀ {P Φ}, (∃ n, entails P (Φ n)) → entails P (ex Φ))
    (ex_elim : ∀ {P Φ}, (∀ n, entails (Φ n) P) → entails (ex Φ) P)
    (logic_sound : ¬ entails TRUE FALSE)
    (later_sound : ∀ {P}, entails TRUE (later P) → entails TRUE P)
    (existential : ∀ {Φ}, entails TRUE (ex Φ) → ∃ n, entails TRUE (Φ n))
    (loeb : ∀ {P}, entails (later P) P → entails TRUE P)
    (comm : ∀ Φ, entails (later (ex Φ)) (ex fun n => later (Φ n))) : False := by
  apply logic_sound
  obtain ⟨n, hf⟩ : ∃ n, entails TRUE (Nat.repeat later n FALSE) :=
    existential <| loeb <| cut (comm _) <| ex_elim fun n => ex_intro ⟨n + 1, assumption _⟩
  induction n with
  | zero => exact hf
  | succ n ih => exact ih (later_sound hf)

end NoLaterExists

/-! ## Counterexamples in the `UPred` model -/

section UPred

local stepindex SI
open BI

variable {M : Type _} [UCMRA M]

theorem laterN_false_holds (n : Nat) {k : SI} (x : ValidAt M k) :
    iprop(▷^[n] (False : UPred M)) k x ↔ k < Nat.repeat SIdx.succ n 0 := by
  induction n generalizing k with
  | zero => exact ⟨False.elim, not_lt_zero k⟩
  | succ n ih =>
    change (∀ m (hm : m < k), _) ↔ _
    exact (forall_congr' fun _ => forall_congr' fun _ => ih _).trans
      (forall_lt_lt_iff.trans lt_succ_r.symm)

/-- `⧍ False` holds exactly below `ω`. -/
theorem bigLater_false_holds {ω : SI} (hω : IsOmega ω) {k : SI} (x : ValidAt M k) :
    iprop(⧍ (False : UPred M)) k x ↔ k < ω := by
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, h⟩
    exact lt_trans ((laterN_false_holds n x).mp h) (hω.iter_lt n)
  · intro hk
    obtain ⟨n, rfl⟩ := hω.lt_iter k hk
    exact ⟨_, ⟨n + 1, rfl⟩, (laterN_false_holds (n + 1) x).mpr (lt_succ_self _)⟩

/-- Entailment is not limit preserving: the constant chain `⧍ False` satisfies
`fun P => P ⊢ ⧍ False` everywhere below `ω`, but its limit (which holds at `ω`) does not (Rocq:
`bounded_limit_preserving_entails_counterexample`). -/
@[rocq_alias bounded_limit_preserving_entails_counterexample]
theorem not_limitPreserving_entails {ω : SI} (hω : IsOmega ω) :
    ¬ LimitPreserving (fun P : UPred M => P ⊢ ⧍ (False : UPred M)) := by
  intro H
  have h := H.lbcompl hω.limit (BChain.const iprop(⧍ (False : UPred M)) ω) fun _ _ => .rfl
  have hlim : (IsCOFE.lbcompl hω.limit (BChain.const iprop(⧍ (False : UPred M)) ω))
      ω ⟨UCMRA.unit, CMRA.unit_validN⟩ :=
    fun m hm _ => (bigLater_false_holds hω _).mpr hm
  exact lt_irrefl ω ((bigLater_false_holds hω _).mp (h _ _ hlim))

/-- The non-expansive map `fun P => P ∧ ⧍ False` (Rocq: `f`). -/
def andBigLaterFalse : UPred M -n> UPred M where
  f P := iprop(P ∧ ⧍ False)
  ne := ⟨fun _ _ _ h => and_ne.ne h .rfl⟩

/-- Non-expansive maps do not preserve limits of bounded chains (Rocq:
`ne_does_not_preserve_limits`). -/
@[rocq_alias test]
theorem ne_not_preserve_lbcompl {ω : SI} (hω : IsOmega ω) :
    andBigLaterFalse (IsCOFE.lbcompl hω.limit (BChain.const iprop(True : UPred M) ω)) ≠
      IsCOFE.lbcompl hω.limit ((BChain.const iprop(True : UPred M) ω).map andBigLaterFalse) := by
  intro h
  have h' := (OFE.eq_dist.mp h ω) ω UCMRA.unit SIdx.le_refl CMRA.unit_validN
  have hr : (IsCOFE.lbcompl hω.limit
      ((BChain.const iprop(True : UPred M) ω).map andBigLaterFalse)) ω
        ⟨UCMRA.unit, CMRA.unit_validN⟩ :=
    fun m hm _ => ⟨trivial, (bigLater_false_holds hω _).mpr hm⟩
  exact lt_irrefl ω ((bigLater_false_holds hω _).mp (h'.mpr hr).2)

end UPred

end Iris.Examples.TransfiniteCounterexamples
