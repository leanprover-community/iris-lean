/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Cmra

@[expose] public section

/-!
# `sbi_unfold`

The tactic takes a (bi-)entailment of plain propositions and turns it into a
(bi-)implication in the pure step-indexed model. For example, given the goal

  `x ≼ y ⊣⊢ x.1 ≼ y.1 ∧ x.2 ≼ y.2`

the tactic `sbi_unfold` turns it into

  `∀ n, x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2`

The tactic `sbi_unfold` works for goals of the shape `⊢ P`, `P ⊢ Q`, `P ⊣⊢ Q`.
Here, `P` and `Q` should be in the "plain" subset of propositions, i.e. `⌜_⌝`,
`<si_pure>`, `✓`, `≡`, `≼`, closed under `∧`, `∨`, `→`, `↔`, `∀`, `∃`, and `▷`.
The separating connectives `∗`/`-∗`/`∗-∗` are translated to `∧`/`→`/`↔`.

The tactic attempts to minimize the number of "down closures" `∀ n' ≤ n, _` due
to the use of nested implications. For example, given

  `⊢ x.1 ≼ y.1 → x.2 ≼ y.2 → x ≼ y`

the tactic `sbi_unfold` turns it into

  `∀ n, x.1 ≼{n} y.1 → x.2 ≼{n} y.2 → x ≼{n} y`

instead of (the logically equivalent, but more verbose)

  `∀ n, ∀ n' ≤ n, x.1 ≼{n'} y.1 → ∀ n'' ≤ n', x.2 ≼{n''} y.2 → x ≼{n''} y`

The tactic is implemented using the type class `SbiUnfold clo P Pi`, which takes
a proposition `P` (which is intended to be plain) as input and produces its
interpretation `Pi : Nat → Prop` in the step-indexed model as output, so that
the down closure of `Pi` is equivalent to `P`.

The input indicator `clo` indicates whether the output `Pi` should be down
closed, i.e. `Pi` should satisfy `Pi n₁ → n₂ ≤ n₁ → Pi n₂`. In this case there
is no need to explicitly down close `Pi`. We use the `clo` parameter to avoid
needless down closures in the translation of implications (see the example
above). In the instance `sbiUnfold_imp` for `P → Q` we call `SbiUnfold` on `Q`
with `clo` being `.notClosed`. This optimization is sound because
`∀ n' ≤ n, Pi n' → Qi n'` and `∀ n' ≤ n, Pi n' → downClose Qi n'` are equivalent
if `Pi` is down closed.

A goal whose head is a `match` is not translated: it has to be case split (with
`cases`/`rcases`) before calling `sbi_unfold`.
-/

namespace Iris
open BI OFE CMRA SiProp

/-- Whether the interpretation produced by `SbiUnfold` has to be downwards closed. -/
@[rocq_alias sbi_unfold_closure_indicator.sbi_unfold_closure_indicator]
inductive SbiUnfoldClosure where
  /-- The interpretation is downwards closed, so no down closure is needed. -/
  | downClosed
  /-- The interpretation need not be downwards closed. -/
  | notClosed

/-- `SbiUnfold clo P Pi` states that the plain proposition `P` is the `<si_pure>`
embedding of the down closure of `Pi`, and that `Pi` is downwards closed whenever
`clo` demands it. -/
@[rocq_alias SbiUnfold]
class SbiUnfold [Sbi PROP] (clo : SbiUnfoldClosure) (P : PROP)
    (Pi : outParam (Nat → Prop)) where
  closed {n₁ n₂} : clo = .downClosed → Pi n₁ → n₂ ≤ n₁ → Pi n₂
  as_siPure : P ⊣⊢ iprop(<si_pure> downClose Pi)

/-- Implications and bi-implications need to be down closed when `clo = .downClosed`. -/
@[rocq_alias sbi_unfold_maybe_downclose]
def SbiUnfoldClosure.maybeDownClose : SbiUnfoldClosure → (Nat → Prop) → Nat → Prop
  | .downClosed, Pi, n => ∀ m ≤ n, Pi m
  | .notClosed, Pi, n => Pi n

namespace SbiUnfold
variable [Sbi PROP] {clo : SbiUnfoldClosure} {P : PROP} {Pi : Nat → Prop}

theorem downClose_of_closed (h : ∀ {n₁ n₂}, Pi n₁ → n₂ ≤ n₁ → Pi n₂) {n} :
    (downClose Pi).holds n ↔ Pi n :=
  ⟨(· n .refl), fun hh _ hm => h hh hm⟩

@[rocq_alias SbiUnfold_closed]
theorem of_closed (hPi : ∀ {n₁ n₂}, Pi n₁ → n₂ ≤ n₁ → Pi n₂)
    (h : P ⊣⊢ iprop(<si_pure> (⟨Pi, hPi⟩ : SiProp))) : SbiUnfold clo P Pi where
  closed _ := hPi
  as_siPure := h.trans <| siPure_mono_bi <| biEntails_of_iff fun _ => (downClose_of_closed hPi).symm

/-- Wrap the interpretation in a down closure when `clo` demands one. -/
@[rocq_alias SbiUnfold_downclose]
theorem of_downClose (h : P ⊣⊢ iprop(<si_pure> downClose Pi)) :
    SbiUnfold clo P (clo.maybeDownClose Pi) := by
  cases clo with
  | notClosed => exact ⟨(nomatch ·), h⟩
  | downClosed => exact of_closed (fun hh hm _ hk => hh _ (Nat.le_trans hk hm)) h

@[rocq_alias sbi_unfold_closed_weaken]
theorem weaken [h : SbiUnfold .downClosed P Pi] : SbiUnfold clo P Pi where
  closed _ := h.closed rfl
  as_siPure := h.as_siPure

end SbiUnfold

/-- This instance can be applied to any `P : SiProp` so it has a low priority to
make sure it's only used if no other instance can be used. -/
@[rocq_alias sbi_unfold_siprop]
instance (priority := low) sbiUnfold_siProp (clo : SbiUnfoldClosure) (P : SiProp) :
    SbiUnfold clo P P.holds :=
  .of_closed P.closed .rfl

section
variable [Sbi PROP] {clo : SbiUnfoldClosure} {P Q : PROP} {Pi Qi : Nat → Prop}

/-! ## The top-level lemmas used by the tactic -/

namespace SbiUnfold

@[rocq_alias sbi_unfold_entails]
theorem entails_iff [hP : SbiUnfold .downClosed P Pi] [hQ : SbiUnfold .notClosed Q Qi] :
    (P ⊢ Q) ↔ ∀ n, Pi n → Qi n :=
  calc (P ⊢ Q)
    _ ↔ (iprop(<si_pure> downClose Pi) ⊢ iprop(<si_pure> downClose Qi)) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact hP.as_siPure.mpr.trans (h.trans hQ.as_siPure.mp)
      · exact hP.as_siPure.mp.trans (h.trans hQ.as_siPure.mpr)
    _ ↔ (downClose Pi ⊢@{SiProp} downClose Qi) := siPure_entails
    _ ↔ ∀ n, Pi n → Qi n := by
      refine ⟨fun h n hp => ?_, fun h _ hp m hm => ?_⟩
      · exact h n (fun _ hm => hP.closed rfl hp hm) n .refl
      · exact h m (hp m hm)

@[rocq_alias sbi_unfold_equiv]
theorem biEntails_iff [hP : SbiUnfold .downClosed P Pi] [hQ : SbiUnfold .downClosed Q Qi] :
    (P ⊣⊢ Q) ↔ ∀ n, Pi n ↔ Qi n := by
  have hPQ := entails_iff (hP := hP) (hQ := .weaken (h := hQ))
  have hQP := entails_iff (hP := hQ) (hQ := .weaken (h := hP))
  refine ⟨fun h n => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · exact hPQ.mp h.mp n
  · exact hQP.mp h.mpr n
  · exact hPQ.mpr fun n => (h n).mp
  · exact hQP.mpr fun n => (h n).mpr

@[rocq_alias sbi_unfold_emp_valid]
theorem empValid_iff [hQ : SbiUnfold .notClosed Q Qi] : (⊢ Q) ↔ ∀ n, Qi n :=
  calc (⊢ Q)
    _ ↔ (⊢ iprop(<si_pure> downClose Qi)) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact h.trans hQ.as_siPure.mp
      · exact h.trans hQ.as_siPure.mpr
    _ ↔ (⊢@{SiProp} downClose Qi) := siPure_emp_valid
    _ ↔ ∀ n, Qi n := by
      refine ⟨fun h n => ?_, fun h _ _ m _ => ?_⟩
      · exact h n trivial n .refl
      · exact h m

end SbiUnfold

/-! ## The instances -/

@[rocq_alias sbi_unfold_pure]
instance sbiUnfold_pure {φ : Prop} : SbiUnfold clo (iprop(⌜φ⌝) : PROP) (fun _ => φ) :=
  .of_closed (fun h _ => h) <|
    siPure_pure.symm.trans <| siPure_mono_bi <| biEntails_of_iff fun _ => .rfl

@[rocq_alias sbi_unfold_internal_eq]
instance sbiUnfold_internalEq [OFE A] {a b : A} :
    SbiUnfold clo (iprop(a ≡ b) : PROP) (fun n => a ≡{n}≡ b) :=
  .of_closed Dist.le <| siPure_mono_bi <| biEntails_of_iff fun _ => .rfl

@[rocq_alias sbi_unfold_internal_cmra_valid]
instance sbiUnfold_cmraValid [CMRA A] {a : A} :
    SbiUnfold clo (iprop(✓ a) : PROP) (fun n => ✓{n} a) :=
  .of_closed (fun h hm => validN_of_le hm h) <|
    siPure_mono_bi <| biEntails_of_iff fun _ => .rfl

@[rocq_alias sbi_unfold_internal_included]
instance sbiUnfold_included [CMRA A] {a b : A} :
    SbiUnfold clo (iprop(a ≼ b) : PROP) (fun n => a ≼{n} b) :=
  .of_closed (fun h hm => incN_of_incN_le hm h) <|
    siPure_mono_bi <| biEntails_of_iff fun _ => exists_holds

@[rocq_alias sbi_unfold_si_pure]
instance sbiUnfold_siPure {Psi : SiProp} [h : SbiUnfold clo Psi Pi] :
    SbiUnfold clo (iprop(<si_pure> Psi) : PROP) Pi where
  closed := h.closed
  as_siPure := siPure_mono_bi h.as_siPure

@[rocq_alias sbi_unfold_and]
instance sbiUnfold_and [hP : SbiUnfold clo P Pi] [hQ : SbiUnfold clo Q Qi] :
    SbiUnfold clo iprop(P ∧ Q) (fun n => Pi n ∧ Qi n) where
  closed hc hh hm := ⟨hP.closed hc hh.1 hm, hQ.closed hc hh.2 hm⟩
  as_siPure := by
    refine (and_congr hP.as_siPure hQ.as_siPure).trans ?_
    refine siPure_and.symm.trans ?_
    refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
    · exact fun hh m hm => ⟨hh.1 m hm, hh.2 m hm⟩
    · exact fun hh => ⟨fun m hm => (hh m hm).1, fun m hm => (hh m hm).2⟩

@[rocq_alias sbi_unfold_sep]
instance sbiUnfold_sep [hP : SbiUnfold clo P Pi] [hQ : SbiUnfold clo Q Qi] :
    SbiUnfold clo iprop(P ∗ Q) (fun n => Pi n ∧ Qi n) where
  closed hc hh hm := ⟨hP.closed hc hh.1 hm, hQ.closed hc hh.2 hm⟩
  as_siPure := by
    refine (sep_congr hP.as_siPure hQ.as_siPure).trans ?_
    refine siPure_and_sep.symm.trans ?_
    refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
    · exact fun hh m hm => ⟨hh.1 m hm, hh.2 m hm⟩
    · exact fun hh => ⟨fun m hm => (hh m hm).1, fun m hm => (hh m hm).2⟩

/-- The instance for disjunction needs the sub-expressions to be already down
closed because `∨` and `∀` do not commute. -/
@[rocq_alias sbi_unfold_or]
instance sbiUnfold_or [hP : SbiUnfold .downClosed P Pi] [hQ : SbiUnfold .downClosed Q Qi] :
    SbiUnfold clo iprop(P ∨ Q) (fun n => Pi n ∨ Qi n) := by
  refine .of_closed (fun hh hm => hh.imp (hP.closed rfl · hm) (hQ.closed rfl · hm)) ?_
  refine (or_congr hP.as_siPure hQ.as_siPure).trans ?_
  refine siPure_or.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun n => ⟨?_, ?_⟩)
  · exact fun hh => hh.imp (· n .refl) (· n .refl)
  · refine fun hh => hh.imp (fun hp _ hm => ?_) (fun hq _ hm => ?_)
    · exact hP.closed rfl hp hm
    · exact hQ.closed rfl hq hm

@[rocq_alias sbi_unfold_impl]
instance sbiUnfold_imp [hP : SbiUnfold .downClosed P Pi] [hQ : SbiUnfold .notClosed Q Qi] :
    SbiUnfold clo iprop(P → Q) (clo.maybeDownClose fun n => Pi n → Qi n) := by
  refine .of_downClose ?_
  refine (imp_congr hP.as_siPure hQ.as_siPure).trans ?_
  refine siPure_imp.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
  · refine fun hh m hm hp => hh m hm ?_ m .refl
    exact fun _ hk => hP.closed rfl hp hk
  · refine fun hh _ hm hp k hk => hh k ?_ (hp k hk)
    exact Nat.le_trans hk hm

@[rocq_alias sbi_unfold_wand]
instance sbiUnfold_wand [hP : SbiUnfold .downClosed P Pi] [hQ : SbiUnfold .notClosed Q Qi] :
    SbiUnfold clo iprop(P -∗ Q) (clo.maybeDownClose fun n => Pi n → Qi n) := by
  refine .of_downClose ?_
  refine (wand_congr hP.as_siPure hQ.as_siPure).trans ?_
  refine siPure_imp_wand.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
  · refine fun hh m hm hp => hh m hm ?_ m .refl
    exact fun _ hk => hP.closed rfl hp hk
  · refine fun hh _ hm hp k hk => hh k ?_ (hp k hk)
    exact Nat.le_trans hk hm

@[rocq_alias sbi_unfold_iff]
instance sbiUnfold_iff [hP : SbiUnfold .downClosed P Pi] [hQ : SbiUnfold .downClosed Q Qi] :
    SbiUnfold clo iprop(P ↔ Q) (clo.maybeDownClose fun n => Pi n ↔ Qi n) := by
  refine .of_downClose ?_
  refine (and_congr (imp_congr hP.as_siPure hQ.as_siPure)
    (imp_congr hQ.as_siPure hP.as_siPure)).trans ?_
  refine siPure_iff.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
  · refine fun hh m hm => ⟨fun hp => ?_, fun hq => ?_⟩
    · exact hh.1 m hm (fun _ hk => hP.closed rfl hp hk) m .refl
    · exact hh.2 m hm (fun _ hk => hQ.closed rfl hq hk) m .refl
  · refine fun hh => ⟨fun _ hm hp k hk => ?_, fun _ hm hq k hk => ?_⟩
    · exact (hh k (Nat.le_trans hk hm)).mp (hp k hk)
    · exact (hh k (Nat.le_trans hk hm)).mpr (hq k hk)

@[rocq_alias sbi_unfold_iff_wand]
instance sbiUnfold_wandIff [hP : SbiUnfold .downClosed P Pi] [hQ : SbiUnfold .downClosed Q Qi] :
    SbiUnfold clo iprop(P ∗-∗ Q) (clo.maybeDownClose fun n => Pi n ↔ Qi n) := by
  refine .of_downClose ?_
  refine (wandIff_congr hP.as_siPure hQ.as_siPure).trans ?_
  refine siPure_iff_wandIff.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
  · refine fun hh m hm => ⟨fun hp => ?_, fun hq => ?_⟩
    · exact hh.1 m hm (fun _ hk => hP.closed rfl hp hk) m .refl
    · exact hh.2 m hm (fun _ hk => hQ.closed rfl hq hk) m .refl
  · refine fun hh => ⟨fun _ hm hp k hk => ?_, fun _ hm hq k hk => ?_⟩
    · exact (hh k (Nat.le_trans hk hm)).mp (hp k hk)
    · exact (hh k (Nat.le_trans hk hm)).mpr (hq k hk)

@[rocq_alias sbi_unfold_forall]
instance sbiUnfold_forall {A : Sort _} {Φ : A → PROP} {Φi : A → Nat → Prop}
    [h : ∀ x, SbiUnfold clo (Φ x) (Φi x)] :
    SbiUnfold clo iprop(∀ x, Φ x) (fun n => ∀ x, Φi x n) where
  closed hc hh hm x := (h x).closed hc (hh x) hm
  as_siPure := by
    refine (forall_congr fun x => (h x).as_siPure).trans ?_
    refine siPure_forall.symm.trans ?_
    refine siPure_mono_bi (biEntails_of_iff fun _ => forall_holds.trans ⟨?_, ?_⟩)
    · exact fun hh m hm x => hh x m hm
    · exact fun hh x m hm => hh m hm x

/-- The instance for existentials needs the sub-expression to be already down
closed because `∃` and `∀` do not commute. -/
@[rocq_alias sbi_unfold_exist]
instance sbiUnfold_exists {A : Sort _} {Φ : A → PROP} {Φi : A → Nat → Prop}
    [h : ∀ x, SbiUnfold .downClosed (Φ x) (Φi x)] :
    SbiUnfold clo iprop(∃ x, Φ x) (fun n => ∃ x, Φi x n) := by
  refine .of_closed (fun ⟨x, hx⟩ hm => ⟨x, (h x).closed rfl hx hm⟩) ?_
  refine (exists_congr fun x => (h x).as_siPure).trans ?_
  refine siPure_exist.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun n => exists_holds.trans ⟨?_, ?_⟩)
  · exact fun ⟨x, hx⟩ => ⟨x, hx n .refl⟩
  · exact fun ⟨x, hx⟩ => ⟨x, fun _ hm => (h x).closed rfl hx hm⟩

@[rocq_alias sbi_unfold_later]
instance sbiUnfold_later [hP : SbiUnfold clo P Pi] :
    SbiUnfold clo iprop(▷ P) (fun n => match n with | 0 => True | m + 1 => Pi m) where
  closed {n₁ n₂} hc hh hm :=
    match n₁, n₂ with
    | _, 0 => trivial
    | 0, _ + 1 => absurd hm (by omega)
    | _ + 1, _ + 1 => hP.closed hc hh (by omega)
  as_siPure := by
    refine (later_congr hP.as_siPure).trans ?_
    refine siPure_later.symm.trans ?_
    refine siPure_mono_bi (biEntails_of_iff fun n => ?_)
    match n with
    | 0 =>
      refine ⟨fun _ m hm => ?_, fun _ => trivial⟩
      match m with
      | 0 => exact trivial
      | _ + 1 => omega
    | _ + 1 =>
      refine ⟨fun hh m hm => ?_, fun hh k hk => hh (k + 1) (by omega)⟩
      match m with
      | 0 => exact trivial
      | _ + 1 => exact hh _ (by omega)

end

/-- Turn a (bi-)entailment of plain propositions into a (bi-)implication in the
pure step-indexed model. -/
syntax (name := sbiUnfoldTac) "sbi_unfold" : tactic

macro_rules
  | `(tactic| sbi_unfold) =>
    -- Some instances leave a down closure, which the `dsimp` reduces away.
    `(tactic|
      (first
        | refine SbiUnfold.empValid_iff.mpr ?_
        | refine SbiUnfold.biEntails_iff.mpr ?_
        | refine SbiUnfold.entails_iff.mpr ?_
        | fail "sbi_unfold: not a BI entailment") <;>
      try dsimp only [SbiUnfoldClosure.maybeDownClose])

#rocq_ignore sbi_unfold_tceq "Only needed for the Rocq `Hint Extern` that translates `match`."
#rocq_concept bi "sbi_unfold" ported "Implemented as the sbi_unfold tactic."
#rocq_concept bi "sbi_unfold" "match" missing
  "No Lean analogue of the Hint Extern; case split by hand."

end Iris
