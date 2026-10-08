/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Cmra
public meta import Lean.Elab.Tactic

@[expose] public section


variable {SI : Type _} [Iris.SIdx SI]

/-!
# `sbi_unfold`

The tactic takes a (bi-)entailment of plain propositions and turns it into a
(bi-)implication in the pure step-indexed model. For example, given the goal

  `x ≼ₒ y ⊣⊢ x.1 ≼ₒ y.1 ∧ x.2 ≼ₒ y.2`

the tactic `sbi_unfold` turns it into

  `∀ (n : SI), x ≼ₒ{n} y ↔ x.1 ≼ₒ{n} y.1 ∧ x.2 ≼ₒ{n} y.2`

The tactic `sbi_unfold` works for goals of the shape `⊢ P`, `P ⊢ Q`, `P ⊣⊢ Q`.
Here, `P` and `Q` should be in the "plain" subset of propositions, i.e. `⌜_⌝`,
`<si_pure>`, `✓`, `≡`, `≼ₒ`, closed under `∧`, `∨`, `→`, `↔`, `∀`, `∃`, and `▷`.
The separating connectives `∗`/`-∗`/`∗-∗` are translated to `∧`/`→`/`↔`.

The tactic attempts to minimize the number of "down closures" `∀ n' ≤ n, _` due
to the use of nested implications. For example, given

  `⊢ x.1 ≼ₒ y.1 → x.2 ≼ₒ y.2 → x ≼ₒ y`

the tactic `sbi_unfold` turns it into

  `∀ (n : SI), x.1 ≼ₒ{n} y.1 → x.2 ≼ₒ{n} y.2 → x ≼ₒ{n} y`

instead of (the logically equivalent, but more verbose)

  `∀ (n : SI), ∀ n' ≤ n, x.1 ≼ₒ{n'} y.1 → ∀ n'' ≤ n', x.2 ≼ₒ{n''} y.2 → x ≼ₒ{n''} y`

The tactic is implemented using the type class `SbiUnfold SI clo P Pi`, which takes
a proposition `P` (which is intended to be plain) as input and produces its
interpretation `Pi : SI → Prop` in the step-indexed model as output, so that
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
open BI OFE ORA _root_.Iris.SiProp

/-- Whether the interpretation produced by `SbiUnfold` has to be downwards closed. -/
@[rocq_alias sbi_unfold_closure_indicator.sbi_unfold_closure_indicator]
inductive SbiUnfoldClosure where
  /-- The interpretation is downwards closed, so no down closure is needed. -/
  | downClosed
  /-- The interpretation need not be downwards closed. -/
  | notClosed

/-- `SbiUnfold SI clo P Pi` states that the plain proposition `P` is the `<si_pure>`
embedding of the down closure of `Pi`, and that `Pi` is downwards closed whenever
`clo` demands it. -/
@[rocq_alias SbiUnfold]
class SbiUnfold (SI : Type _) [SIdx SI] {PROP : Type _} [BI PROP] [BIStepIndexed SI PROP] [Sbi SI PROP] (clo : SbiUnfoldClosure) (P : PROP)
    (Pi : outParam (SI → Prop)) where
  closed {n₁ n₂ : SI} : clo = .downClosed → Pi n₁ → n₂ ≤ n₁ → Pi n₂
  as_siPure : P ⊣⊢ iprop(<si_pure> downClose Pi)

/-- Implications and bi-implications need to be down closed when `clo = .downClosed`. -/
@[rocq_alias sbi_unfold_maybe_downclose]
def SbiUnfoldClosure.maybeDownClose : SbiUnfoldClosure → (SI → Prop) → SI → Prop
  | .downClosed, Pi, n => ∀ (m : SI), m ≤ n → Pi m
  | .notClosed, Pi, n => Pi n

namespace SbiUnfold
variable [BI PROP] [BIStepIndexed SI PROP] [Sbi SI PROP] {clo : SbiUnfoldClosure} {P : PROP} {Pi : SI → Prop}

theorem downClose_of_closed (h : ∀ {n₁ n₂ : SI}, Pi n₁ → n₂ ≤ n₁ → Pi n₂) {n : SI} :
    (downClose Pi).holds n ↔ Pi n :=
  ⟨(· n SIdx.le_refl), fun hh _ hm => h hh hm⟩

@[rocq_alias SbiUnfold_closed]
theorem of_closed (hPi : ∀ {n₁ n₂ : SI}, Pi n₁ → n₂ ≤ n₁ → Pi n₂)
    (h : P ⊣⊢ iprop(<si_pure> (⟨Pi, hPi⟩ : SiProp SI))) : SbiUnfold SI clo P Pi where
  closed _ := hPi
  as_siPure := h.trans <| siPure_mono_bi <| biEntails_of_iff fun _ => (downClose_of_closed hPi).symm

/-- Wrap the interpretation in a down closure when `clo` demands one. -/
@[rocq_alias SbiUnfold_downclose]
theorem of_downClose (h : P ⊣⊢ iprop(<si_pure> downClose Pi)) :
    SbiUnfold SI clo P (clo.maybeDownClose Pi) := by
  cases clo with
  | notClosed => exact ⟨(nomatch ·), h⟩
  | downClosed => exact of_closed (fun hh hm _ hk => hh _ (SIdx.le_trans hk hm)) h

@[rocq_alias sbi_unfold_closed_weaken]
theorem weaken [h : SbiUnfold SI .downClosed P Pi] : SbiUnfold SI clo P Pi where
  closed _ := h.closed rfl
  as_siPure := h.as_siPure

end SbiUnfold

/-- This instance can be applied to any `P : SiProp SI` so it has a low priority to
make sure it's only used if no other instance can be used. -/
@[rocq_alias sbi_unfold_siprop]
instance (priority := low) sbiUnfold_siProp (clo : SbiUnfoldClosure) (P : SiProp SI) :
    SbiUnfold SI clo P P.holds :=
  .of_closed P.closed .rfl

section
variable [BI PROP] [BIStepIndexed SI PROP] [Sbi SI PROP] {clo : SbiUnfoldClosure} {P Q : PROP} {Pi Qi : SI → Prop}

/-! ## The top-level lemmas used by the tactic -/

namespace SbiUnfold

@[rocq_alias sbi_unfold_entails]
theorem entails_iff [hP : SbiUnfold SI .downClosed P Pi] [hQ : SbiUnfold SI .notClosed Q Qi] :
    (P ⊢ Q) ↔ ∀ (n : SI), Pi n → Qi n :=
  calc (P ⊢ Q)
    _ ↔ (iprop(<si_pure> downClose Pi) ⊢ iprop(<si_pure> downClose Qi)) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact hP.as_siPure.mpr.trans (h.trans hQ.as_siPure.mp)
      · exact hP.as_siPure.mp.trans (h.trans hQ.as_siPure.mpr)
    _ ↔ (downClose Pi ⊢@{SiProp SI} downClose Qi) := siPure_entails
    _ ↔ ∀ (n : SI), Pi n → Qi n := by
      refine ⟨fun h n hp => ?_, fun h _ hp m hm => ?_⟩
      · exact h n (fun _ hm => hP.closed rfl hp hm) n SIdx.le_refl
      · exact h m (hp m hm)

@[rocq_alias sbi_unfold_equiv]
theorem biEntails_iff [hP : SbiUnfold SI .downClosed P Pi] [hQ : SbiUnfold SI .downClosed Q Qi] :
    (P ⊣⊢ Q) ↔ ∀ (n : SI), Pi n ↔ Qi n := by
  have hPQ := entails_iff (hP := hP) (hQ := .weaken (h := hQ))
  have hQP := entails_iff (hP := hQ) (hQ := .weaken (h := hP))
  refine ⟨fun h n => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · exact hPQ.mp h.mp n
  · exact hQP.mp h.mpr n
  · exact hPQ.mpr fun n => (h n).mp
  · exact hQP.mpr fun n => (h n).mpr

@[rocq_alias sbi_unfold_emp_valid]
theorem empValid_iff [hQ : SbiUnfold SI .notClosed Q Qi] : (⊢ Q) ↔ ∀ (n : SI), Qi n :=
  calc (⊢ Q)
    _ ↔ (⊢ iprop(<si_pure> downClose Qi)) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact h.trans hQ.as_siPure.mp
      · exact h.trans hQ.as_siPure.mpr
    _ ↔ (⊢@{SiProp SI} downClose Qi) := siPure_emp_valid
    _ ↔ ∀ (n : SI), Qi n := by
      refine ⟨fun h n => ?_, fun h _ _ m _ => ?_⟩
      · exact h n trivial n SIdx.le_refl
      · exact h m

end SbiUnfold

/-! ## The instances -/

@[rocq_alias sbi_unfold_pure]
instance sbiUnfold_pure {φ : Prop} : SbiUnfold SI clo (iprop(⌜φ⌝) : PROP) (fun _ => φ) :=
  .of_closed (fun h _ => h) <|
    siPure_pure.symm.trans <| siPure_mono_bi <| biEntails_of_iff fun _ => .rfl

@[rocq_alias sbi_unfold_internal_eq]
instance sbiUnfold_internalEq [OFE SI A] {a b : A} :
    SbiUnfold SI clo (iprop(a ≡[SI] b) : PROP) (fun (n : SI) => a ≡{n}≡ b) :=
  .of_closed Dist.le <| siPure_mono_bi <| biEntails_of_iff fun _ => .rfl

@[rocq_alias sbi_unfold_internal_cmra_valid]
instance sbiUnfold_cmraValid [ORA SI A] {a : A} :
    SbiUnfold SI clo (iprop(✓[SI] a) : PROP) (fun (n : SI) => ✓{n} a) :=
  .of_closed (fun h hm => validN_of_le hm h) <|
    siPure_mono_bi <| biEntails_of_iff fun _ => .rfl

instance sbiUnfold_included [ORA SI A] {a b : A} :
    SbiUnfold SI clo (iprop(a ≼ₒ[SI] b) : PROP) (fun (n : SI) => a ≼ₒ{n} b) :=
  .of_closed (fun h hm => ordN_of_ordN_le hm h) <| siPure_mono_bi <| biEntails_of_iff fun _ => .rfl

@[rocq_alias sbi_unfold_internal_included]
instance sbiUnfold_inc [ORA SI A] {a b : A} :
    SbiUnfold SI clo (iprop(a ≼[SI] b) : PROP) (fun (n : SI) => a ≼{n} b) :=
  .of_closed (fun h hm => incN_of_incN_le hm h) <|
    siPure_mono_bi <| biEntails_of_iff fun _ => exists_holds

@[rocq_alias sbi_unfold_si_pure]
instance sbiUnfold_siPure {Psi : SiProp SI} [h : SbiUnfold SI clo Psi Pi] :
    SbiUnfold SI clo (iprop(<si_pure> Psi) : PROP) Pi where
  closed := h.closed
  as_siPure := siPure_mono_bi h.as_siPure

@[rocq_alias sbi_unfold_and]
instance sbiUnfold_and [hP : SbiUnfold SI clo P Pi] [hQ : SbiUnfold SI clo Q Qi] :
    SbiUnfold SI clo iprop(P ∧ Q) (fun (n : SI) => Pi n ∧ Qi n) where
  closed hc hh hm := ⟨hP.closed hc hh.1 hm, hQ.closed hc hh.2 hm⟩
  as_siPure := by
    refine (and_congr hP.as_siPure hQ.as_siPure).trans ?_
    refine siPure_and.symm.trans ?_
    refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
    · exact fun hh m hm => ⟨hh.1 m hm, hh.2 m hm⟩
    · exact fun hh => ⟨fun m hm => (hh m hm).1, fun m hm => (hh m hm).2⟩

@[rocq_alias sbi_unfold_sep]
instance sbiUnfold_sep [hP : SbiUnfold SI clo P Pi] [hQ : SbiUnfold SI clo Q Qi] :
    SbiUnfold SI clo iprop(P ∗ Q) (fun (n : SI) => Pi n ∧ Qi n) where
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
instance sbiUnfold_or [hP : SbiUnfold SI .downClosed P Pi] [hQ : SbiUnfold SI .downClosed Q Qi] :
    SbiUnfold SI clo iprop(P ∨ Q) (fun (n : SI) => Pi n ∨ Qi n) := by
  refine .of_closed (fun hh hm => hh.imp (hP.closed rfl · hm) (hQ.closed rfl · hm)) ?_
  refine (or_congr hP.as_siPure hQ.as_siPure).trans ?_
  refine siPure_or.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun n => ⟨?_, ?_⟩)
  · exact fun hh => hh.imp (· n SIdx.le_refl) (· n SIdx.le_refl)
  · refine fun hh => hh.imp (fun hp _ hm => ?_) (fun hq _ hm => ?_)
    · exact hP.closed rfl hp hm
    · exact hQ.closed rfl hq hm

@[rocq_alias sbi_unfold_impl]
instance sbiUnfold_imp [hP : SbiUnfold SI .downClosed P Pi] [hQ : SbiUnfold SI .notClosed Q Qi] :
    SbiUnfold SI clo iprop(P → Q) (clo.maybeDownClose fun (n : SI) => Pi n → Qi n) := by
  refine .of_downClose ?_
  refine (imp_congr hP.as_siPure hQ.as_siPure).trans ?_
  refine siPure_imp.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
  · refine fun hh m hm hp => hh m hm ?_ m SIdx.le_refl
    exact fun _ hk => hP.closed rfl hp hk
  · refine fun hh _ hm hp k hk => hh k ?_ (hp k hk)
    exact SIdx.le_trans hk hm

@[rocq_alias sbi_unfold_wand]
instance sbiUnfold_wand [hP : SbiUnfold SI .downClosed P Pi] [hQ : SbiUnfold SI .notClosed Q Qi] :
    SbiUnfold SI clo iprop(P -∗ Q) (clo.maybeDownClose fun (n : SI) => Pi n → Qi n) := by
  refine .of_downClose ?_
  refine (wand_congr hP.as_siPure hQ.as_siPure).trans ?_
  refine siPure_imp_wand.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
  · refine fun hh m hm hp => hh m hm ?_ m SIdx.le_refl
    exact fun _ hk => hP.closed rfl hp hk
  · refine fun hh _ hm hp k hk => hh k ?_ (hp k hk)
    exact SIdx.le_trans hk hm

@[rocq_alias sbi_unfold_iff]
instance sbiUnfold_iff [hP : SbiUnfold SI .downClosed P Pi] [hQ : SbiUnfold SI .downClosed Q Qi] :
    SbiUnfold SI clo iprop(P ↔ Q) (clo.maybeDownClose fun (n : SI) => Pi n ↔ Qi n) := by
  refine .of_downClose ?_
  refine (and_congr (imp_congr hP.as_siPure hQ.as_siPure)
    (imp_congr hQ.as_siPure hP.as_siPure)).trans ?_
  refine siPure_iff.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
  · refine fun hh m hm => ⟨fun hp => ?_, fun hq => ?_⟩
    · exact hh.1 m hm (fun _ hk => hP.closed rfl hp hk) m SIdx.le_refl
    · exact hh.2 m hm (fun _ hk => hQ.closed rfl hq hk) m SIdx.le_refl
  · refine fun hh => ⟨fun _ hm hp k hk => ?_, fun _ hm hq k hk => ?_⟩
    · exact (hh k (SIdx.le_trans hk hm)).mp (hp k hk)
    · exact (hh k (SIdx.le_trans hk hm)).mpr (hq k hk)

@[rocq_alias sbi_unfold_iff_wand]
instance sbiUnfold_wandIff [hP : SbiUnfold SI .downClosed P Pi] [hQ : SbiUnfold SI .downClosed Q Qi] :
    SbiUnfold SI clo iprop(P ∗-∗ Q) (clo.maybeDownClose fun (n : SI) => Pi n ↔ Qi n) := by
  refine .of_downClose ?_
  refine (wandIff_congr hP.as_siPure hQ.as_siPure).trans ?_
  refine siPure_iff_wandIff.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun _ => ⟨?_, ?_⟩)
  · refine fun hh m hm => ⟨fun hp => ?_, fun hq => ?_⟩
    · exact hh.1 m hm (fun _ hk => hP.closed rfl hp hk) m SIdx.le_refl
    · exact hh.2 m hm (fun _ hk => hQ.closed rfl hq hk) m SIdx.le_refl
  · refine fun hh => ⟨fun _ hm hp k hk => ?_, fun _ hm hq k hk => ?_⟩
    · exact (hh k (SIdx.le_trans hk hm)).mp (hp k hk)
    · exact (hh k (SIdx.le_trans hk hm)).mpr (hq k hk)

@[rocq_alias sbi_unfold_forall]
instance sbiUnfold_forall {A : Sort _} {Φ : A → PROP} {Φi : A → SI → Prop}
    [h : ∀ x, SbiUnfold SI clo (Φ x) (Φi x)] :
    SbiUnfold SI clo iprop(∀ x, Φ x) (fun (n : SI) => ∀ x, Φi x n) where
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
instance sbiUnfold_exists {A : Sort _} {Φ : A → PROP} {Φi : A → SI → Prop}
    [h : ∀ x, SbiUnfold SI .downClosed (Φ x) (Φi x)] :
    SbiUnfold SI clo iprop(∃ x, Φ x) (fun (n : SI) => ∃ x, Φi x n) := by
  refine .of_closed (fun ⟨x, hx⟩ hm => ⟨x, (h x).closed rfl hx hm⟩) ?_
  refine (exists_congr fun x => (h x).as_siPure).trans ?_
  refine siPure_exist.symm.trans ?_
  refine siPure_mono_bi (biEntails_of_iff fun n => exists_holds.trans ⟨?_, ?_⟩)
  · exact fun ⟨x, hx⟩ => ⟨x, hx n SIdx.le_refl⟩
  · exact fun ⟨x, hx⟩ => ⟨x, fun _ hm => (h x).closed rfl hx hm⟩

@[rocq_alias sbi_unfold_later]
instance sbiUnfold_later [hP : SbiUnfold SI clo P Pi] :
    SbiUnfold SI clo iprop(▷ P) (fun (n : SI) => ∀ (m : SI), m < n → Pi m) where
  closed _ hh hm m hlt := hh m (SIdx.lt_le_trans hlt hm)
  as_siPure := by
    refine (later_congr hP.as_siPure).trans ?_
    refine siPure_later.symm.trans ?_
    refine siPure_mono_bi (biEntails_of_iff fun n => ⟨?_, ?_⟩)
    · exact fun hh _ hn' m hm => hh m (SIdx.lt_le_trans hm hn') m SIdx.le_refl
    · exact fun hh m hm k hk => hh n SIdx.le_refl k (SIdx.le_lt_trans hk hm)

end

/-- Turn a (bi-)entailment of plain propositions into a (bi-)implication in the
pure step-indexed model. -/
syntax (name := sbiUnfoldTac) "sbi_unfold" : tactic

/-- `sbi_unfold` at a fixed step index `si`. -/
syntax (name := sbiUnfoldAtTac) "sbi_unfold_at " term : tactic

macro_rules
  | `(tactic| sbi_unfold_at $si) =>
    -- Some instances leave a down closure, which the `dsimp` reduces away.
    `(tactic|
      (first
        | refine (SbiUnfold.empValid_iff (SI := $si)).mpr ?_
        | refine (SbiUnfold.biEntails_iff (SI := $si)).mpr ?_
        | refine (SbiUnfold.entails_iff (SI := $si)).mpr ?_) <;>
      try dsimp only [SbiUnfoldClosure.maybeDownClose])

open Lean Elab Tactic Meta in
/-- The step index is not determined by an (SI-free) entailment, so it is taken from the
`Sbi s _` instances in the local context (in order), falling back to `Nat`. -/
@[tactic sbiUnfoldTac] meta def evalSbiUnfold : Tactic := fun _ => withMainContext do
  let mut cands : Array Expr := #[]
  for li in (← getLocalInstances) do
    let ty ← instantiateMVars (← inferType li.fvar)
    if ty.isAppOf ``Sbi && ty.getAppNumArgs ≥ 1 then
      let si := ty.getAppArgs[0]!
      unless cands.any (· == si) do cands := cands.push si
  unless cands.any (·.isConstOf ``Nat) do cands := cands.push (mkConst ``Nat)
  for si in cands do
    let s ← saveState
    try
      let siStx ← Term.exprToSyntax si
      evalTactic (← `(tactic| sbi_unfold_at $siStx))
      return
    catch _ => s.restore
  throwError "sbi_unfold: not a BI entailment"

#rocq_ignore sbi_unfold_tceq "Only needed for the Rocq `Hint Extern` that translates `match`."
#rocq_concept bi "sbi_unfold" ported "Implemented as the sbi_unfold tactic."
#rocq_concept bi "sbi_unfold" "match" missing
  "No Lean analogue of the Hint Extern; case split by hand."

end Iris
