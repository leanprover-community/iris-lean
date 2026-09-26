/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.UPred.Instance
public import Iris.BI.Transfinite

/-! # Transfinite Iris: properties of the `UPred` model

This file ports the parts of Transfinite Iris's `base_logic/upred.v`, `base_logic/derived.v` and
`base_logic/satisfiable.v` that are specific to (transfinite) step-indices:

- soundness of the big later `⧍` for transfinite step-indices (`big_later_soundness`,
  `big_laterN_soundness`, `transfinite_soundness`),
- timelessness of `∗` and `∃` in the model for arbitrary step-indices (`timeless_zero`,
  `later_sep_timeless`, `later_exist_timeless`), which the generic BI laws only provide for finite
  step-indices,
- the satisfiability predicate (`UPred.satisfiable`, instance `Satisfiable (UPred M)`), whose
  existential rule holds for large step-indices (`SIdxLarge`),
- `later_or_is_classical` (`dec_halting`): commuting `▷` with `∨` at a limit index decides a
  halting problem.
-/

@[expose] public section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

universe w v

namespace Iris.UPred
open BI CMRA

variable {M : Type _} [UCMRA M]

/-! ## Big later -/

theorem iter_succ_le : ∀ (n : Nat) (m : SI), m ≤ Nat.repeat SIdx.succ n m
  | 0, _ => SIdx.le_refl
  | n + 1, m => SIdx.le_trans (iter_succ_le n m) SIdx.le_succ_diag_r

/-- If `▷^[n] P` holds at `succᵢ^[n] m`, then `P` holds at `m`. -/
theorem laterN_holds_iter {P : UPred M} :
    ∀ (n : Nat) {m : SI} (x : M) (hx : ✓{Nat.repeat SIdx.succ n m} x),
      iprop(▷^[n] P).holds _ ⟨x, hx⟩ → P m ⟨x, validN_of_le (iter_succ_le n m) hx⟩
  | 0, _, _, _, h => h
  | n + 1, _, x, _, h => laterN_holds_iter n x _ (h _ (SIdx.lt_succ_self _))

@[rocq_alias uPred_primitive.big_later_soundness]
theorem big_later_soundness [SIdxTransfinite SI] (P : UPred M) :
    iprop(True ⊢ ⧍ P) → iprop((True : UPred M) ⊢ P) := by
  intro H n x _
  obtain ⟨_, ⟨k, rfl⟩, Hk⟩ :=
    H (SIdxTransfinite.upperLimit n) ⟨unit, unit_validN⟩ trivial
  have Hk' : iprop(▷^[k] P).holds (Nat.repeat SIdx.succ k n) ⟨unit, unit_validN⟩ :=
    UPred.mono _ Hk (incN_refl _) (SIdx.lt_le_incl (SIdxTransfinite.iter_succ_lt_upperLimit k n))
  exact UPred.mono _ (laterN_holds_iter k unit unit_validN Hk') incN_unit SIdx.le_refl

@[rocq_alias uPred_primitive.big_laterN_soundness]
theorem big_laterN_soundness [SIdxTransfinite SI] (n : Nat) (P : UPred M) :
    iprop(True ⊢ bigLaterN n P) → iprop((True : UPred M) ⊢ P) := by
  induction n generalizing P with
  | zero => exact id
  | succ n ih => exact fun h => ih P (big_later_soundness _ h)

/-- Soundness of the big later for pure propositions (Transfinite Iris, `transfinite_soundness`):
a pure proposition that holds after finitely many steps holds. -/
@[rocq_alias uPred.transfinite_soundness]
theorem transfinite_soundness [SIdxTransfinite SI] (φ : Prop) :
    iprop((True : UPred M) ⊢ ⧍ ⌜φ⌝) → φ :=
  fun h => pure_soundness (big_later_soundness _ h)

/-! ## Timelessness in the model -/

/-- A timeless proposition that holds at index `0` holds (Transfinite Iris, `timeless_zero`). -/
@[rocq_alias uPred_primitive.timeless_zero]
theorem timeless_zero (P : UPred M) [Timeless P] : iprop(▷ False → P) ⊢ P := by
  intro n
  induction n using instSI.lt_wf.induction with
  | h n ih =>
    intro x H
    by_cases hn : n = 0
    · subst hn
      exact H x (inc_refl _) SIdx.le_refl fun m hm => absurd hm (SIdx.not_lt_zero m)
    · have hlater : iprop(▷ P).holds n x := fun m hm =>
        ih m hm (x.le (SIdx.lt_le_incl hm))
          fun {_} y hy hk HF => H y hy (SIdx.le_trans hk (SIdx.lt_le_incl hm)) HF
      have ht : iprop(▷ P ⊢ ◇ P) := Timeless.timeless
      rcases ht n x hlater with HF | HP
      · exact absurd (HF 0 (SIdx.neq_0_lt_0.mp hn)) id
      · exact HP

/-- `P` holds at index `0` (as a proposition of the model). -/
private theorem holds_of_zero {P : UPred M} [Timeless P] {n : SI} {x : ValidAt M n} {x0 : M}
    {hx0 : ✓{0} x0} (H : P 0 ⟨x0, hx0⟩) (hinc : x0 ≼{0} x.val) : P n x :=
  timeless_zero P n x fun {n'} y hy hle HF => by
    by_cases hn' : n' = 0
    · subst hn'
      exact UPred.mono _ H (incN_trans hinc (hy.incN)) SIdx.le_refl
    · exact absurd (HF 0 (SIdx.neq_0_lt_0.mp hn')) id

@[rocq_alias uPred_primitive.later_sep_timeless]
theorem later_sep_timeless (P Q : UPred M) [Timeless P] [Timeless Q] :
    iprop(▷ (P ∗ Q)) ⊣⊢ iprop(▷ P ∗ ▷ Q) := by
  refine ⟨fun n x H => ?_, later_sep_2⟩
  by_cases hn : n = 0
  · subst hn
    exact ⟨core x.val, x.val, (core_op x.val).symm.dist, fun m hm => absurd hm (SIdx.not_lt_zero m),
      fun m hm => absurd hm (SIdx.not_lt_zero m)⟩
  · obtain ⟨x1, x2, H1, H2, H3⟩ := H 0 (SIdx.neq_0_lt_0.mp hn)
    obtain ⟨y1, y2, Hx, Hy1, Hy2⟩ := extend (validN_of_le SIdx.le_0_l x.property) H1
    refine ⟨y1, y2, Hx.dist, fun m _ => ?_, fun m _ => ?_⟩
    · exact holds_of_zero H2 Hy1.symm.to_incN
    · exact holds_of_zero H3 Hy2.symm.to_incN

/-- In the model, `∗` of timeless propositions is timeless for arbitrary step-indices (the
generic `sep_timeless` requires finite step-indices). -/
instance sep_timeless' (P Q : UPred M) [Timeless P] [Timeless Q] : Timeless iprop(P ∗ Q) where
  timeless := (later_sep_timeless P Q).1.trans <|
    (sep_mono Timeless.timeless Timeless.timeless).trans except0_sep.2

@[rocq_alias uPred_primitive.later_exist_timeless]
theorem later_exist_timeless {A : Sort _} (Ψ : A → UPred M) [∀ a, Timeless (Ψ a)] :
    iprop(▷ ∃ a, Ψ a) ⊢ iprop(▷ False ∨ ∃ a, ▷ Ψ a) := by
  intro n x H
  by_cases hn : n = 0
  · subst hn; exact .inl fun m hm => absurd hm (SIdx.not_lt_zero m)
  · obtain ⟨_, ⟨a, rfl⟩, Ha⟩ := H 0 (SIdx.neq_0_lt_0.mp hn)
    exact .inr ⟨_, ⟨a, rfl⟩, fun m _ => holds_of_zero Ha (incN_refl _)⟩

/-- In the model, `∃` of timeless propositions is timeless for arbitrary step-indices (the
generic `exists_timeless` requires finite step-indices). -/
instance exists_timeless' {A : Sort _} (Ψ : A → UPred M) [∀ a, Timeless (Ψ a)] :
    Timeless iprop(∃ a, Ψ a) where
  timeless := (later_exist_timeless Ψ).trans <|
    or_elim or_intro_l (exists_elim fun a =>
      Timeless.timeless.trans (except0_mono (exists_intro a)))

/-! ## Satisfiability -/

/-- A proposition of the model is satisfiable if at every index it holds for some valid resource
(Transfinite Iris, `uPred_satisfiable`). The resource may depend on the index. -/
@[rocq_alias uPred_satisfiable]
def satisfiable (P : UPred M) : Prop := ∀ n, ∃ x, ∃ h : ✓{n} x, P n ⟨x, h⟩

theorem satisfiable_intro {P : UPred M} (H : iprop(True ⊢ P)) : satisfiable P :=
  fun n => ⟨unit, unit_validN, H n _ trivial⟩

theorem satisfiable_mono {P Q : UPred M} (hP : satisfiable P) (H : P ⊢ Q) : satisfiable Q :=
  fun n => let ⟨x, hx, HP⟩ := hP n; ⟨x, hx, H n _ HP⟩

theorem satisfiable_elim {P : UPred M} [Plain P] (hP : satisfiable P) : iprop(True ⊢ P) :=
  fun n _ _ =>
    let ⟨_, _, HP⟩ := hP n
    have hpl : iprop(P ⊢ ■ P) := Plain.plain
    UPred.mono _ (hpl n _ HP) incN_unit SIdx.le_refl

theorem satisfiable_later {P : UPred M} (hP : satisfiable iprop(▷ P)) : satisfiable P :=
  fun n =>
    let ⟨x, hx, HP⟩ := hP (succᵢ n)
    ⟨x, validN_of_le SIdx.le_succ_diag_r hx, HP n (SIdx.lt_succ_self n)⟩

theorem satisfiable_bupd {P : UPred M} (hP : satisfiable iprop(|==> P)) : satisfiable P :=
  fun n =>
    let ⟨_, hx, HP⟩ := hP n
    let ⟨x', H, HP'⟩ := HP n unit SIdx.le_refl (validN_ne unit_right_id.symm.dist hx)
    ⟨x', validN_op_left H, HP'⟩

theorem satisfiable_finite_exists {X : Type w} {P : X → UPred M} {Q : X → Prop} (l : List X)
    (hfin : ∀ x, Q x → x ∈ l) (hent : ∀ x, P x ⊢ ⌜Q x⌝) (hP : satisfiable iprop(∃ x, P x)) :
    ∃ x, satisfiable (P x) :=
  SIdx.commute_finite_exists (fun a n => ∃ y, ∃ h : ✓{n} y, P a n ⟨y, h⟩) Q l hfin
    (fun _ _ _ hab ⟨y, hy, H⟩ => ⟨y, validN_of_le hab hy, UPred.mono _ H (incN_refl _) hab⟩)
    (fun n =>
      let ⟨y, hy, _, ⟨a, rfl⟩, Ha⟩ := hP n
      ⟨a, hent a n _ Ha, y, hy, Ha⟩)

theorem satisfiable_exists [SIdxLarge.{v} SI] {X : Type v} {P : X → UPred M}
    (hP : satisfiable iprop(∃ x, P x)) : ∃ x, satisfiable (P x) :=
  SIdxLarge.commute_exists (fun a n => ∃ y, ∃ h : ✓{n} y, P a n ⟨y, h⟩)
    (fun _ _ _ hab ⟨y, hy, H⟩ =>
      ⟨y, validN_of_le (SIdx.lt_le_incl hab) hy, UPred.mono _ H (incN_refl _) (SIdx.lt_le_incl hab)⟩)
    (fun n => let ⟨y, hy, _, ⟨a, rfl⟩, Ha⟩ := hP n; ⟨a, y, hy, Ha⟩)

@[rocq_alias uPred_Satisfiable]
instance instSatisfiable : Satisfiable.{w, v} (UPred M) where
  satisfiable := satisfiable
  intro := satisfiable_intro
  mono := satisfiable_mono
  elim := satisfiable_elim
  later := satisfiable_later
  finite_exists := satisfiable_finite_exists
  exists_ := satisfiable_exists
  bupd := satisfiable_bupd

/-! ## Commuting `▷` with `∨` is classical -/

/-- Transfinite Iris's `later_or_is_classical` (`dec_halting`): if `▷` commutes with `∨` (as it
does in Lean, `later_or_1`), then at a limit index `ω` one can decide whether a function
`f : SI → Bool` becomes `true`. (In Lean this is trivial classically; the point of the lemma is
that the commuting law is only justified by classical reasoning in the model.) -/
@[rocq_alias uPred_primitive.dec_halting]
theorem later_or_is_classical (ω : SI) (m : M) (f : SI → Bool)
    (comm : ∀ P Q : UPred M, iprop(▷ (P ∨ Q)) ⊢ iprop(▷ P ∨ ▷ Q))
    (Hdec : ∀ n, n < ω → (∀ m, m ≤ n → f m = false) ∨ (∃ m, f m = true))
    (Hm : ✓{ω} m) (Hl : 0 < ω) :
    (∀ n, n < ω → f n = false) ∨ (∃ m, f m = true) := by
  let P : UPred M := {
    holds n _ := ∀ n', n' ≤ n → f n' = false
    mono H _ hle n' hn' := H n' (SIdx.le_trans hn' hle) }
  rcases comm P iprop(⌜∃ m, f m = true⌝) ω ⟨m, Hm⟩ (fun n hn => Hdec n hn) with H | H
  · exact .inl fun n hn => H n hn n SIdx.le_refl
  · exact .inr (H 0 Hl)

end Iris.UPred
