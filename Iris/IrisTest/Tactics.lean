/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Oliver Soeser, Michael Sammler, Yunsong Yang, Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.Token
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.WeakestPre
public import Iris.Algebra.CMRA
public import Iris.Instances.Lib.Invariants
public import Iris.Instances.Lib.CInvariants
public import Iris.Instances.Lib.NaInvariants
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.WeakestPre

@[expose] public section

namespace IrisTest
open Iris BI CMRA DFrac CancelableInvariant NonAtomicInvariant ProgramLogic

/- This file contains tests with various scenarios for all available tactics. -/

section istart

/-- Tests `istart` and `istop` for entering and exiting proof mode. -/
example [BI PROP] (Q : PROP) (H : Q ⊢ Q) : Q ⊢ Q := by
  istart
  iintro _HQ
  have HH : True := by trivial
  istop
  exact H

/-- Tests `istart` with a BI instance specified. -/
example [BI PROP1] [BI PROP2] (P1 : PROP1) (P2 : PROP2)
    (_ : ⊢@{PROP1} P1) : ⊢@{PROP2} P2 -∗ P2 := by
  istart PROP2
  iintro HP
  iassumption

/- Tests `istart` with the wrong BI instance specified. -/
/-- error: istart: ⊢ P2 is not an emp valid in PROP1 -/
#guard_msgs in
example [BI PROP1] [BI PROP2] (P1 : PROP1) (P2 : PROP2)
    (h : ⊢@{PROP1} P1) : ⊢@{PROP2} P2 := by
  istart PROP1

/- Tests `istart` with an invalid type specified as the BI instance. -/
/-- error: istart: True is not a valid BI instance type -/
#guard_msgs in
example [BI PROP1] [BI PROP2] (P1 : PROP1) (P2 : PROP2)
    (h : ⊢@{PROP1} P1) : ⊢@{PROP2} P2 := by
  istart True

/- Tests `istart` within the Iris Proof Mode. -/
example [BI PROP1] [BI PROP2] (P1 : PROP1) (P2 : PROP2)
    (_ : ⊢@{PROP1} P1) : ⊢@{PROP2} P2 -∗ P2 := by
  iintro P2
  istart PROP2
  istart
  istart PROP2
  iassumption

/- Tests `istart` within the Iris Proof Mode with the wrong BI instance specified. -/
/-- error: istart: currently in the Iris Proof Mode with PROP2 rather than PROP1 -/
#guard_msgs in
example [BI PROP1] [BI PROP2] (P1 : PROP1) (P2 : PROP2)
    (_ : ⊢@{PROP1} P1) : ⊢@{PROP2} P2 -∗ P2 := by
  iintro P2
  istart PROP1

/- Tests `istart` with BI specified and embedding involved. -/
example [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2] (P : PROP1)
    (h : ⊢@{PROP1} P) : ⊢@{PROP1} P := by
  istart PROP2
  guard_target = ProofMode.Entails' (PROP:=PROP2) _ iprop(⎡P⎤)
  ihave H := h
  iexact H

/- Tests `istart` with embedding involved but an invalid BI specified. -/
/-- error: istart: ⊢ P1 is not an emp valid in PROP3 -/
#guard_msgs in
example [BI PROP1] [BI PROP2] [BI PROP3] [BiEmbed PROP1 PROP2]
  [BiEmbed PROP2 PROP3] (P1 : PROP1)
    (h : ⊢@{PROP1} P1) : ⊢@{PROP1} P1 := by
  istart PROP3

/- Tests `istart` to ensure embedding is not used unless a BI is specified. -/
/-- error: istart: currently in the Iris Proof Mode with PROP1 rather than PROP2 -/
#guard_msgs in
example [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    (P1 : PROP1) (h : ⊢@{PROP1} P1) : ⊢@{PROP1} P1 := by
  istart
  istart PROP2

end istart

section irename

/-- Tests basic hypothesis renaming with `irename`. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => H
  iexact H

/-- Tests renaming a hypothesis by its type. -/
example [BI PROP] (P Q : PROP) : □ P ∗ Q ⊢ Q := by
  iintro ⟨_HP, HQ⟩
  irename: Q => H
  iexact H

/-- Tests renaming a hypothesis twice. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => H
  irename H => HQ
  iexact HQ

/-- Tests renaming a hypothesis to itself (no-op). -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => HQ
  iexact HQ

end irename

section iclear

/-- Tests clearing an intuitionistic hypothesis with `iclear`. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ Q -∗ Q := by
  iintro #HP
  iintro HQ
  iclear HP
  iexact HQ

/-- Tests clearing a spatial affine hypothesis with `iclear`. -/
example [BI PROP] (P Q : PROP) : <affine> P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iclear HP
  iexact HQ

/-- Tests clearing all intuitionistic hypotheses with `iclear #`. -/
example [BI PROP] (P Q R : PROP) : □ P ∗ □ Q ⊢ R -∗ R := by
  iintro ⟨#HP, #HQ⟩ HR
  iclear #
  iexact HR

/-- Tests clearing all spatial hypotheses with `iclear ∗`. -/
example [BI PROP] (P Q R : PROP) : <affine> P ∗ <affine> Q ⊢ <affine> R -∗ emp := by
  iintro ⟨HP, HQ⟩ HR
  iclear ∗
  iempintro

/-- Tests clearing a Lean variable with `iclear %x`. -/
example [BI PROP] {α} (_x : α) (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iclear %_x
  iexact HQ

/-- Tests clearing all Lean pure hypotheses with `iclear %`. -/
example [BI PROP] (φ ψ : Prop) (_hφ : φ) (_hψ : ψ) (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iclear %
  iexact HQ

/-- Tests clearing proofmode and Lean contexts at the same time. -/
example [BI PROP] {α φ} (_x : α) (_hφ : φ) (P Q : PROP) : □ P ⊢ Q -∗ Q := by
  iintro #HP
  iintro HQ
  iclear HP %_x %_hφ
  iexact HQ

/-- Tests clearing `%`, `#`, and `∗` at the same time. -/
example [BI PROP] {φ} (_hφ : φ) (P Q R : PROP) : □ P ∗ <affine> Q ⊢ <affine> R -∗ emp := by
  iintro ⟨#HP, HQ⟩
  iintro HR
  iclear % # ∗
  iempintro

/-- Tests clearing dependent Lean locals when the dependency comes first. -/
example [BI PROP] {α} (x : α) (_hx : x = x) (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iclear %x %_hx
  iexact HQ

/-- Tests clearing dependent Lean locals when the dependent hypothesis comes first. -/
example [BI PROP] {α} (x : α) (_hx : x = x) (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iclear %_hx %x
  iexact HQ

/- Tests `iclear` failing. -/
/-- error: iclear: P is not affine and the goal not absorbing -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q -∗ Q := by
  iintro HP HQ
  iclear HP

/- Tests `iclear` failing with a dependent Lean variable. -/
/-- error: iclear: proofmode hypothesis HQ depends on x -/
#guard_msgs in
example [BI PROP] {α} (x : α) (Q : α → PROP) : Q x ⊢ Q x := by
  iintro HQ
  iclear %x

/- Tests `iclear` failing with a dependent Lean hypothesis. -/
/-- error: iclear: Lean hypothesis hx depends on x -/
#guard_msgs in
example [BI PROP] {α} (x : α) (hx : x = x) (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iclear %x

/- Tests `iclear` failing when the goal depends on a Lean variable. -/
/-- error: iclear: goal depends on x -/
#guard_msgs in
example [BI PROP] {α} (x : α) (Q : α → PROP) : ⊢ Q x := by
  iclear %x

end iclear

-- intro
section iintro

/-- Tests introducing a spatial hypothesis. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iexact HQ

/-- Tests introducing an intuitionistic hypothesis with the `#` pattern. -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro #HQ
  iexact HQ

/-- Tests introducing an affine persistent proposition as intuitionistic. -/
example [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ Q := by
  iintro #HQ
  iexact HQ

/-- Tests introducing a persistent implication in the spatial context. -/
example [BI PROP] (Q : PROP) : ⊢ <pers> Q → Q := by
  iintro HQ
  iexact HQ

/- Tests introducing an implication in an intuitionistic context. -/
example [BI PROP] (P : PROP) : □ P -∗ P → P := by
  iintro #HP1 HP2
  iexact HP2

/-- Tests dropping a hypothesis in an implication with the `-` pattern. -/
example [BI PROP] (P Q : PROP) : ⊢ P → Q -∗ Q := by
  iintro - HQ
  iexact HQ

/-- Tests dropping a hypothesis in an implication in a non-empty context. -/
example [BI PROP] (P Q : PROP) : Q -∗ P → Q := by
  iintro HQ -
  iexact HQ

/-- Tests introducing an universally quantified variable. -/
example [BI PROP] : ⊢@{PROP} ∀ x, ⌜x = 0⌝ → ⌜x = 0⌝ := by
  iintro %x
  iintro H
  iexact H

/-- Tests introducing and extracting a pure hypothesis in affine BI. -/
example [BI PROP] [BIAffine PROP] φ (Q : PROP) : ⌜φ⌝ -∗ Q -∗ Q := by
  iintro %Hφ HQ
  iexact HQ

/-- Tests introducing with disjunction pattern inside intuitionistic. -/
example [BI PROP] (P1 P2 Q : PROP) : □ (P1 ∨ P2) ∗ Q ⊢ Q := by
  iintro ⟨#(_HP1 | _HP2), HQ⟩ <;> iexact HQ

/-- Tests introducing multiple spatial hypotheses. -/
example [BI PROP] (P Q : PROP) : <affine> P -∗ Q -∗ Q := by
  iintro _HP HQ
  iexact HQ

/-- Tests introducing multiple intuitionistic hypotheses. -/
example [BI PROP] (P Q : PROP) : □ P -∗ □ Q -∗ Q := by
  iintro #_HP #HQ
  iexact HQ

/-- Tests introducing with complex nested patterns. -/
example [BI PROP] (P1 P2 Q : PROP) : □ (P1 ∧ P2) -∗ Q ∨ Q -∗ Q := by
  iintro #⟨_HP1, ∗_HP2⟩ (HQ | HQ) <;> iexact HQ

/-- Tests `iintro //`. -/
example [BI PROP] : ⊢@{PROP} True := by
  iintro //

/-- Tests `iintro //` not solving the goal. -/
example [BI PROP] (Q : PROP) : Q -∗ Q := by
  iintro // HQ
  iexact HQ

/-- Tests `iintro //` solving one subgoal, but not another. -/
example [BI PROP] (Q : PROP) : ((True -∗ Q) ∨ False) -∗ Q := by
  iintro ⟨HQ | %_⟩  //
  iapply HQ $$ [//]

/- Tests `iintro` failing to introduce pure hypothesis. -/
/-- error: iintro: iprop(P -∗ Q) cannot be turned into a universal quantifier or pure hypothesis -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P -∗ Q := by
  iintro %H

/- Tests `iintro` failing to introduce. -/
/-- error: iintro: Q not a wand -/
#guard_msgs in
example [BI PROP] (Q : PROP) : ⊢ Q := by
  iintro H

/- Tests `iintro` failing to introduce intuitionistically. -/
/-- error: iintro: Q not a wand -/
#guard_msgs in
example [BI PROP] (Q : PROP) : ⊢ Q := by
  iintro #H

/- Tests `iintro` failing to introduce non-intuitionistic wand as intuitionistic. -/
/-- error: iintro: P not persistent -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P -∗ Q := by
  iintro #H

/- Tests `iintro` failing to introduce non-intuitionistic implication as intuitionistic. -/
/-- error: iintro: P not persistent -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : ⊢ P → Q := by
  iintro #H

/- Tests `iintro` failing to introduce implication with non-empty spatial context. -/
/-- error: iintro: P is not persistent and spatial context is non-empty -/
#guard_msgs in
example [BI PROP] (P : PROP) : P -∗ P → P := by
  iintro HP1 HP2

/- Tests `iintro` using the introduction pattern `⟨⟩` to solve the goal. -/
example [BI PROP] (P : PROP) : False ∗ □ P ⊢@{PROP} P := by
  iintro ⟨⟨⟩, #_⟩

/- Tests `iintro` using the pure introduction pattern. -/
example [BI PROP] (P : Nat → PROP) : ∀ n, P n ⊢@{PROP} P n := by
  iintro %(a | n) HP //

@[simp]
private def def1 := 3

/- Tests `iintro` using the introduction pattern for simplification (`/=`). -/
example [BI PROP] (P Q : PROP) : ⊢@{PROP} if def1 = 3 then P -∗ P else Q := by
  iintro /= HP
  iexact HP

/- Tests `iintro` where the lack of simplification (`/=`) causes a failure. -/
/-- error: iintro: if def1 = 3 then iprop(P -∗ P) else Q not a wand -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : ⊢@{PROP} if def1 = 3 then P -∗ P else Q := by
  iintro HP

/- Tests `iintro` with the pattern for simplification and solving trivial goals (`//=`). -/
example [BI PROP] : ⊢@{PROP} if def1 = 3 then True else False := by
  iintro //=

/- Tests `iintro` with the pattern for ∀-introduction (`*`). -/
example {Val : Type} [BI PROP] (P Q : Val → PROP) :
    ⊢@{PROP} ∀ x y, P x -∗ Q y -∗ P x ∗ Q y := by
  iintro * _ _
  iframe

/-- Tests `iintro` with the pattern for repeating ∀-introduction and premise introduction (`**`). -/
example {Val : Type} {φ : Prop} [BI PROP] (P : Val → Val → PROP) (Q : Val → PROP) :
    ⊢@{PROP} ∀ x y, P x y -∗ ∀ z, (⌜φ⌝ → Q z -∗ P x y ∗ Q z ∗ ⌜φ⌝) := by
  iintro **
  iframe
  ipureintro
  assumption

/-- Tests `iintro` with the pattern for introducing a pure goal and exiting the proof mode (`!%`). -/
example [BI PROP] (n : Nat) (P Q : PROP) : ⊢ □ P -∗ □ Q -∗ ⌜n = n⌝ := by
  iintro - - !%
  rfl

/- Tests `iintro` with pure introduction failure. -/
/-- error: iintro: Q is not pure -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q := by
  iintro HP !%

/-- Tests `iintro` with introduction patterns coming after `!%`. -/
example {φ : Prop} [BI PROP] : ⊢@{PROP} ⌜⌜φ⌝ ⊢@{PROP} ⌜φ⌝⌝ := by
  iintro !% %_ !%
  assumption

/-- Tests `iintro` with an introduction pattern for clearing and framing hypotheses (`{ selPats* }`). -/
example [BI PROP] (P Q R S T : PROP) (φ : Prop) :
    ⊢ □ ⌜φ⌝ -∗ P -∗ Q -∗ <affine> R -∗ □ S -∗ □ T -∗ P ∗ Q ∗ T := by
  iintro %hφ HP HQ {$HP} HR #HS #HT {HR %hφ %φ $# #}
  iexact HQ

/-- Tests `iintro` with introduction patterns for rewriting pure equalities. -/
example [BI PROP] (m n : Nat) (a b c : Prop) :
    m = 2 → 3 = n → ⊢@{PROP} ⌜a = b⌝ -∗ ⌜b = c⌝ -∗ ⌜m.succ = n ∧ a = c⌝ := by
  iintro %rfl %rfl %rfl %rfl
  ipureintro
  and_intros <;> rfl

/-
  Tests `iintro` with an introduction pattern for rewriting but the
  hypothesis is not a pure equality
-/
/--
error: Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
  P

PROP : Type u_1
inst✝ : BI PROP
P : Prop
x✝ : P
⊢ emp ⊢ True
-/
#guard_msgs in
example [BI PROP] (P : Prop) : ⊢@{PROP} ⌜P⌝ -∗ True := by
  iintro %rfl

/-- Tests `iintro` with non-trivial `rcases` destruction patterns. -/
example [BI PROP] (a b c1 c2 c3 : Prop) (P : Prop → Prop) :
    ⊢@{PROP} □ ⌜((a = b ∧ (b ∨ (c1 ∧ c2 ∧ c3))) ∧ ∃ x, P x)⌝ -∗ ⌜a ∨ c1⌝ ∗ ⌜∃ x, P x⌝ := by
  iintro %⟨⟨rfl, ((hb : a) | ⟨hc, _, -⟩)⟩, @⟨d : Prop, hd⟩⟩ !%
  · grind
  · grind

/-- Tests `iintro` with an introduction involving substitution of an equality (`%rfl`). -/
example [BI PROP] n (P Q : Nat → PROP) : (<affine> ⌜n = 0⌝ ∗ P 0 ∗ Q n) ⊢ P n ∗ Q n := by
  iintro ⟨%rfl, Hp⟩
  iexact Hp

end iintro

section irevert

/-- Tests `irevert` order and names. -/
example [BI PROP] (P Q : PROP) : P -∗ Q -∗ P ∗ Q := by
  iintro H1 H2
  irevert %P %Q H1 H2
  iintro %P %Q H1 H2
  isplitl [H1]
  · iexact H1
  · iexact H2

/-- Tests `irevert` with a spatial proposition. -/
example [BI PROP] (P Q : PROP) (H : P -∗ Q) : P ⊢ Q := by
  iintro HP
  irevert HP
  exact H

/-- Tests `irevert` with a intuitionistic proposition. -/
example [BI PROP] (P : PROP) (H : □ P -∗ P) : □ P ⊢ P := by
  iintro #HP
  irevert HP
  exact H

/-- Tests `irevert` with a pure proposition. -/
example [BI PROP] {φ} (P : PROP) (Hφ : φ) : (<affine> ⌜φ⌝ -∗ P) -∗ P := by
  iintro H
  irevert %Hφ
  iexact H

/-- Tests `irevert` of a pure proposition in affine BI does not add `<affine>`. -/
example [BI PROP] [BIAffine PROP] {φ} (P : PROP) (Hφ : φ) : (⌜φ⌝ -∗ P) -∗ P := by
  iintro H
  irevert %Hφ
  iexact H

/-- Tests `irevert` with a forall proposition. -/
example [BI PROP] {α} (x : α) (Φ : α → PROP) : ⊢ (∀ x, Φ x) → Φ x := by
  iintro H
  irevert %x
  iexact H

/-- Tests `irevert` with multiple spatial propositions. -/
example [BI PROP] (P Q : PROP) :
    ⊢ (P -∗ <affine> Q -∗ P) -∗ P -∗ <affine> Q -∗ P := by
  iintro H HP HQ
  irevert HP HQ
  iexact H

/-- Tests `irevert` with multiple intuitionistic propositions. -/
example [BI PROP] (P Q : PROP) :
    ⊢ (□ P -∗ <affine> Q -∗ P) -∗ □ P -∗ <affine> Q -∗ P := by
  iintro H #HP HQ
  irevert HP HQ
  iexact H

/-- Tests `irevert ∗` with all spatial hypotheses. -/
example [BI PROP] (P Q : PROP) (H : P -∗ <affine> Q -∗ P) : P ∗ <affine> Q ⊢ P := by
  iintro ⟨HP, HQ⟩
  irevert ∗
  exact H

/-- Tests `irevert #` with all intuitionistic hypotheses. -/
example [BI PROP] (P Q : PROP) (H : □ P -∗ □ Q -∗ P) : □ P ∗ □ Q ⊢ P := by
  iintro ⟨#HP, #HQ⟩
  irevert #
  exact H

/-- Tests `irevert %` with all Lean pure hypotheses. -/
example [BI PROP] {φ ψ} (P : PROP) (Hφ : φ) (Hψ : ψ) : (<affine> ⌜φ⌝ -∗ <affine> ⌜ψ⌝ -∗ P) -∗ P := by
  iintro H
  irevert %
  iexact H

/-- Tests `irevert % # ∗` with Lean pure, intuitionistic, and spatial hypotheses together. -/
example {φ ψ : Prop} [BI PROP] (P Q : PROP) (Hφ : φ) (Hψ : ψ) : □ P ∗ <affine> Q ⊢ P := by
  iintro ⟨#HP, HQ⟩
  irevert % # ∗
  iintro %hφ %hψ #HP _HQ
  iexact HP

/-- Tests `irevert` with mixed Lean/proofmode hypotheses and dependencies. -/
example [BI PROP] (Φ : Bool → PROP) : ⊢ ∀ x, <affine> ⌜x = true⌝ -∗ Φ x -∗ Φ x := by
  iintro %x %hp H
  irevert %x %hp H
  iintro %x %hp H
  iexact H

/- Tests that `irevert` clears binder info (see https://github.com/leanprover-community/iris-lean/pull/393#issuecomment-4506443579). -/
/-- trace:
PROP : Type u_1
inst✝ : BI PROP
P : PROP
⊢ ⏎
  ⊢ ∀ x, P
-/
#guard_msgs (trace, drop error) in
example [BI PROP] (P : PROP) {x : Nat} : ⊢ P := by
  irevert %x
  trace_state

/- Tests `irevert` failing with dependency. -/
/-- info: Try this:
  [apply] irevert %x %hp H
---
info: Try this:
  [apply] irevert! %x
---
error: irevert: The following hypotheses depend on variables in the `generalizing` clause but are not themselves included:
• Lean hypothesis `hp` depends on `x`
• Iris hypothesis `H` depends on `x` -/
#guard_msgs in
example [BI PROP] (Φ : Bool → PROP) : ⊢ ∀ x, <affine> ⌜x = true⌝ -∗ Φ x -∗ Φ x := by
  iintro %x %hp H
  irevert %x

/-
  Tests `irevert` failing with dependency, involving an inaccessible name
-/
/-- info: Try this:
  [apply] irevert! %x H
---
error: irevert: The following hypotheses depend on variables in the `generalizing` clause but are not themselves included:
• Lean hypothesis `x` (inaccessible name) depends on `x` -/
#guard_msgs in
example [BI PROP] (Φ : Bool → PROP) : ⊢ ∀ x, <affine> ⌜x = true⌝ -∗ Φ x -∗ Φ x := by
  iintro %x %_ H
  irevert %x H

/-- Tests `irevert!` which reverts `H2` and `H3` automatically. -/
example [BI PROP] (Φ : Bool → PROP) (x y : Bool) :
    (∀ x, (Φ x -∗ Φ y) -∗ Φ x -∗ Φ y) ∗ (Φ x -∗ Φ y) ∗ Φ x ⊢ Φ y := by
  iintro ⟨H1, H2, H3⟩
  irevert! %x
  iassumption

end irevert

section iexists

/-- Tests `iexists` with a BI proposition. -/
example [BI PROP] : ⊢@{PROP} ∃ x, x := by
  iexists iprop(True)
  ipureintro
  exact True.intro

/-- Tests `iexists` with a natural number. -/
example [BI PROP] : ⊢@{PROP} ∃ (_x : Nat), True ∨ False := by
  iexists 42
  ileft
  ipureintro
  exact True.intro

/-- Tests `iexists` with Prop. -/
example [BI PROP] : ⊢@{PROP} ⌜∃ x, x ∨ False⌝ := by
  iexists True
  ipureintro
  exact Or.inl True.intro

/-- Tests `iexists` with a named metavariable. -/
example [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
  iexists ?y
  ipureintro
  rfl

/-- Tests `iexists` with anonymous metavariable. -/
example [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
  iexists _
  ipureintro
  rfl

/-- Tests `iexists` with two quantifiers. -/
example [BI PROP] : ⊢@{PROP} ∃ x y : Nat, ⌜x = y⌝ := by
  iexists _, 1
  ipureintro
  rfl

/- Tests `iexists` failing with non-quantifier. -/
/-- error: iexists: cannot turn iprop(True) into an existential quantifier -/
#guard_msgs in
example [BI PROP] : ⊢@{PROP} True := by
  iexists _

end iexists

section iexact

/-- Tests basic `iexact`. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iexact HQ

/-- Tests `iexact` with affine pers to intuitionistic. -/
example [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ □ Q := by
  iintro HQ
  iexact HQ

/-- Tests `iexact` with intuitionistic hypothesis. -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro HQ
  iexact HQ

/-- Tests `iexact` with fupd. -/
example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP]
    (E : CoPset) (P : PROP) : P ⊢ |={E}=> P := by
  iintro HP
  iexact HP

/- Tests `iexact` failing with not-affine assumption. -/
/-- error: iexact: context is not affine or goal is not absorbing -/
#guard_msgs in
example [BI PROP] (Q : PROP) : Q -∗ True -∗ Q := by
  iintro HQ _
  iexact HQ

/- Tests `iexact` failing with non-matching goal. -/
/-- error: iexact: cannot unify Q 1 and Q 2 -/
#guard_msgs in
example [BI PROP] (Q : Nat → PROP) : Q 1 -∗ Q 2 := by
  iintro HQ
  iexact HQ

end iexact

section assumption

/-- Tests `iassumption` for exact match. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro _HQ
  iassumption

/-- Tests `iassumption` with affine pers to intuitionistic. -/
example [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ □ Q := by
  iintro _HQ
  iassumption

/-- Tests `iassumption` with intuitionistic hypothesis. -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro #_HQ
  iassumption

/-- Tests `iassumption` with multiple hypotheses. -/
example [BI PROP] (P Q : PROP) : □ Q ∗ P ⊢ P := by
  iintro ⟨#_, _⟩
  iassumption

/- Tests `iassumption` failure. -/
/-- error: iassumption: no matching assumption -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : □ P ⊢ Q := by
  iintro #_HQ
  iassumption

/- Tests `iassumption` with mvar goal. -/
/-- error: iassumption: goal is a mvar, use iaccu instead -/
#guard_msgs in
example [BI PROP] (P : PROP) : P ⊢ ∃ Q, Q := by
  iintro HP
  iexists _
  iassumption

/-- Tests `iassumption` in `itrivial`. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro _HQ
  itrivial

end assumption

section iapply

/-- Tests `iapply` with exact match. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iapply HQ

/-- Tests `iapply` with wand. -/
example [BI PROP] (P Q : PROP) : P -∗ (P -∗ Q) -∗ Q := by
  iintro HP H
  iapply H $$ HP

/-- Tests `iapply` with multiple hypotheses. -/
example [BI PROP] (P Q R : PROP) : P -∗ Q -∗ (P -∗ Q -∗ R) -∗ R := by
  iintro HP HQ H
  iapply H $$ HP HQ

/-- Tests `iapply` with nested wand application. -/
example [BI PROP] (P Q R S : PROP) : (P -∗ Q) -∗ P -∗ R -∗ (Q -∗ R -∗ S) -∗ S := by
  iintro HPQ HP HR H
  iapply H $$ [HPQ HP] HR
  iapply HPQ $$ HP

/-- Tests `iapply` with intuitionistic exact. -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro #HQ
  iapply HQ

/-- Tests `iapply` with intuitionistic wand argument. -/
example [BI PROP] (P Q : PROP) : □ P -∗ (P -∗ Q) -∗ Q := by
  iintro HP H
  iapply H $$ HP

/-- Tests `iapply` with multiple intuitionistic hypotheses and subgoals. -/
example [BI PROP] (P Q R : PROP) : □ P -∗ Q -∗ □ (P -∗ Q -∗ □ R) -∗ R := by
  iintro #HP HQ #H
  iapply H $$ [] [HQ] as Q
  case Q => iexact HQ
  iexact HP

/-- Tests `iapply` with later modality. -/
example [BI PROP] (P Q : PROP) : (▷ P -∗ Q) -∗ P -∗ Q := by
  iintro H HP
  iapply H $$ HP

/-- Tests `iapply` with implication. -/
example [BI PROP] [BIAffine PROP] (P Q : PROP) : (P → Q) -∗ <pers> P -∗ Q := by
  iintro H HP
  iapply H $$ HP

/-- Tests `iapply` with later and implication. -/
example [BI PROP] [BIAffine PROP] (P Q : PROP) : (▷ P → Q) -∗ P -∗ Q := by
  iintro H HP
  iapply H $$ HP

/-- Tests `iapply` with Lean hypothesis. -/
example [BI PROP] (Q : PROP) (H : ⊢ Q) : ⊢ Q := by
  iapply H

/-- Tests `iapply` with lemma. -/
example [BI PROP] (Q : PROP) : Q ⊢ (emp ∗ Q) ∗ emp := by
  iapply (wand_intro sep_emp.mpr)
  iempintro

/-- Tests `iapply` with pure sidecondition. -/
example [BI PROP] (Q : PROP) (H : 0 = 0 → ⊢ Q) : ⊢ Q := by
  iapply H
  rfl

/-- Tests `iapply` with lemma with sidecondition. -/
example [BI PROP] : ⊢@{PROP} ⌜1 = 1⌝ := by
  istart
  iapply (pure_intro (P:=emp))
  . rfl
  iempintro

/-- Tests `iapply` with entailment as Lean hypothesis. -/
example [BI PROP] (P Q : PROP) (H : P ⊢ Q) (HP : ⊢ P) : ⊢ Q := by
  iapply H
  iapply HP

/-- Tests `iapply` with wand entailment as Lean hypothesis. -/
example [BI PROP] (P Q : PROP) (H : P -∗ Q) (HP : ⊢ P) : ⊢ Q := by
  iapply H $$ []
  iapply HP

/-- Tests `iapply` with constructed term. -/
example [BI PROP] (P Q : PROP) (H1 : P ⊢ Q) (H2 : Q ⊢ R) : P ⊢ R := by
  iintro HP
  iapply (wand_intro (emp_sep.mp.trans H2))
  . itrivial
  iapply H1 $$ HP

/-- Tests `iapply` with Lean wand entailment and subgoal. -/
example [BI PROP] (P Q R : PROP) (H : P ⊢ Q -∗ R) (HP : ⊢ P) : ⊢ Q -∗ R := by
  iintro HQ
  iapply H $$ [] HQ
  iapply HP

/-- Tests `iapply` with lemma and subgoal. -/
example [BI PROP] (P Q R : PROP) (H : P ∗ Q ⊢ R) (HP : ⊢ P) : ⊢ Q -∗ R := by
  iintro HQ
  iapply (wand_intro H) $$ [] HQ
  iapply HP

/-- Tests `iapply` with forall. -/
example [BI PROP] {α} (P : α → PROP) (a : α) (H : ⊢ ∀ x, P x) : ⊢ P a := by
  istart
  iapply H

/-- Tests `iapply` with Lean forall. -/
example [BI PROP] {α} (P : α → PROP) (a : α) (H : ∀ x, ⊢ P x) : ⊢ P a := by
  iapply H

/-- Tests `iapply` with forall specialization. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  iapply H $$ %a %b HP

/-- Tests `iapply` with forall specialization from hypothesis. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %a %b HP

/-- Tests `iapply` with tactic. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %(by exact a) %b [HP]
  iapply HP

/-- Tests `iapply` with pure hypothesis. -/
example [BI PROP] {α} (Q : α → PROP) (a b : α) : (∀ x, ∀ y, ⌜x = a⌝ -∗ Q y) ⊢ Q b := by
  iintro H
  iapply H $$ %_ %b %rfl

/-
  Tests `iapply` with an invalid attempt to specialise a wand premise using a
  subgoal intended for discharging a pure premise.
-/
/-- error: iapply: Q b is not a Lean premise -/
#guard_msgs in
example [BI PROP] {α} (P Q : α → PROP) (a b : α) :
    (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %a %b HP %_

/-
  Tests `iapply` with a specialization pattern discharging a wand premise as
  a subgoal (`⊢ P a`).
-/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) (h : ⊢ P a) :
    (∀ x, ∀ y, P x -∗ Q y) ⊢ □ P a -∗ Q b := by
  iintro H #HP
  iapply H $$ %a %b %_
  exact h

/-- Tests `iapply` using unification for foralls. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ HP

/-- Tests `iapply` using manually created metavariables. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %?_ %?_ HP

/-- Tests `iapply` using unification in two steps, instantiating metavars . -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H
  iapply HP

/-- Tests `iapply` with intuitionistic forall from Lean. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  iapply H $$ %a HP

/-- Tests `iapply` with intuitionistic forall from hypothesis. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) : (□ ∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %a %b HP

/-- Tests `iapply` with two wands and subgoals. -/
example [BI PROP] (P Q : Nat → PROP) :
  (P 1 -∗ P 2 -∗ Q 1) ⊢ □ P 1 -∗ P 2 -∗ Q 1 := by
  iintro H #HP1 HP2
  iapply H
  . iexact HP1
  . iexact HP2

/-- Tests `iapply` selecting left conjunct. -/
example [BI PROP] (P Q : Nat → PROP) :
  ((P 1 -∗ P 2) ∧ (Q 1 -∗ Q 2)) ⊢ P 1 -∗ P 2 := by
  iintro H HP1
  iapply H
  iexact HP1

/-- Tests `iapply` selecting right conjunct. -/
example [BI PROP] (P Q : Nat → PROP) :
  ((P 1 -∗ P 2) ∧ (Q 1 -∗ Q 2)) ⊢ Q 1 -∗ Q 2 := by
  iintro H HQ1
  iapply H
  iexact HQ1

/-- Tests `iapply` selecting left conjunct (exact match). -/
example [BI PROP] (P Q : Nat → PROP) :
  (P 1 ∧ Q 1) ⊢ P 1 := by
  iintro H
  iapply H

/-- Tests `iapply` selecting right conjunct (exact match). -/
example [BI PROP] (P Q : Nat → PROP) :
  (P 1 ∧ Q 1) ⊢ Q 1 := by
  iintro H
  iapply H

/- Tests `iapply` exact matching, but not affine. -/
/-- error: iapply: the context P is not affine and goal not absorbing -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : Q ⊢ P -∗ Q := by
  iintro H HP
  iapply H

/-- Tests `iapply` of a plain wand under a basic update, using `intoWand_bupd_args` to balance the
argument and the result of the wand against the goal's modality. -/
example [BI PROP] [BIUpdate PROP] (P Q : PROP) :
    (P -∗ Q) ⊢ (|==> P) -∗ |==> Q := by
  iintro Hwand HP
  iapply Hwand
  iexact HP

/-- Tests `iapply` of a plain wand under a fancy update, using `intoWand_fupd_args` to balance the
argument and the result of the wand against the goal's modality. -/
example [BI PROP] [BIFUpdate PROP] (E1 E2 : CoPset) (P Q : PROP) :
    (P -∗ Q) ⊢ (|={E1,E2}=> P) -∗ |={E1,E2}=> Q := by
  iintro Hwand HP
  iapply Hwand
  iexact HP

/-- Tests `iapply` of a plain wand under a later, using `intoWand_later_args` to balance the
argument and the result of the wand against the goal's modality. -/
example [BI PROP] (P Q : PROP) : (P -∗ Q) ⊢ (▷ P) -∗ ▷ Q := by
  iintro Hwand HP
  iapply Hwand
  iexact HP

/-- Tests `iapply` of a plain wand under `▷^[n]`, using `intoWand_laterN_args` to balance the
argument and the result of the wand against the goal's modality. -/
example [BI PROP] (n : Nat) (P Q : PROP) : (P -∗ Q) ⊢ (▷^[n] P) -∗ ▷^[n] Q := by
  iintro Hwand HP
  iapply Hwand
  iexact HP

-- `intoWand_later_args` is reached only once `R` has bottomed out: with a `▷` on
-- `R` itself, both instances match, and the `low` priority of the args instance
-- means the structure-stripping `intoWand_later` is tried first and wins.
/--
[Meta.synthInstance.instances] #[@ProofMode.intoWand_later_args, @ProofMode.intoWand_later]
[Meta.synthInstance] ✅️ apply @ProofMode.intoWand_later to ProofMode.IntoWand false false iprop(▷ (P -∗ Q))
-/
#guard_msgs (whitespace := lax, substring := true) in
example [BI PROP] (P Q : PROP) : (▷ (P -∗ Q)) ⊢ (▷ P) -∗ ▷ Q := by
  iintro Hwand HP
  (set_option trace.Meta.synthInstance true in iapply Hwand)
  iexact HP

/-- Tests `iapply` of an intuitionistic wand under an `<affine>`, using
`intoWand_affine_args` to balance the argument and the result of the wand against
the goal's modality. -/
example [BI PROP] (P Q : PROP) : □ (P -∗ Q) ⊢ (<affine> P) -∗ <affine> Q := by
  iintro #Hwand HP
  iapply Hwand
  iexact HP

/-- `intoWand_affine_args` is reached only once `R` has bottomed out: with an
`<affine>` on `R` itself, the structure-stripping `intoWand_affine` wins instead. -/
example [BI PROP] (P Q : PROP) : (<affine> (P -∗ Q)) ⊢ (<affine> P) -∗ <affine> Q := by
  iintro Hwand HP
  iapply Hwand
  iexact HP

inductive R where
  | R_Constr (n : Int) (r : R)
/-- Test `iapply` with a `match` in a hypothesis, regression test for
https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/iapply.20doesn.27t.20work.20with.20matches.3F/near/615255205 -/
example [BI PROP] (P : PROP) :
    (∀ t,
      (match t with
      | R.R_Constr _ _ => True) -∗ P) -∗
    (match t with
    | R.R_Constr _ _ => True) -∗ P := by
  iintro Hwand Ht
  iapply Hwand
  iapply Ht

/-- Test `iapply` with other match, regression test for
https://github.com/leanprover-community/iris-lean/issues/145 -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  have H: (∀ b (Q: PROP),
    (match b with
     | true => iprop(Q)
     | false => iprop(Q))
    ⊢ Q) := by rintro ⟨⟩ <;> simp
  iapply H
  case b => exact true
  itrivial

end iapply

section ihave

/-- Tests `ihave` with Lean hypothesis. -/
example [BI PROP] (Q : PROP) (H : ⊢ Q) : ⊢ Q := by
  ihave HQ := H
  iexact HQ

/-- Tests `ihave` with Lean hypothesis introducing into persistent context. -/
example [BI PROP] (Q : PROP) (H : ⊢ Q) : ⊢ Q ∗ Q := by
  ihave HQ := H
  isplitl
  · iexact HQ
  · iexact HQ

/-- Tests `ihave` with forall specialization via case. -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H
  case x => exact 1
  iapply HQ

/-- Tests `ihave` with forall specialization via named hole. -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H ?res
  case res => exact 1
  iexact HQ

/-- Tests `ihave` with two named holes. -/
example [BI PROP] (Q : Nat → Nat → PROP) (H : ∀ x y, ⊢ Q x y) : ⊢ Q 1 1 := by
  ihave HQ := H ?res ?res
  case res => exact 1
  iexact HQ

/-- Tests `ihave` creating metavars. -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H
  iexact HQ

/-- Tests `ihave` with typeclass argument (failing search). -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ (P : PROP) [Persistent P], ⊢ P) : ⊢ Q 1 := by
  ihave HQ := H
  rotate_right 1; exact iprop(□ Q 1)
  . apply inferInstance
  iexact HQ

/-- Tests `ihave` with typeclass argument (successful search). -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ (P : PROP) [Persistent P], ⊢ P) : ⊢ Q 1 := by
  ihave HQ := H iprop(□ Q _)
  rotate_right 1; exact 1
  iexact HQ

/-- Tests `ihave` from spatial hypothesis. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro H
  ihave HQ := H
  iexact HQ

/-- Tests `ihave` with Lean entailment. -/
example [BI PROP] (P Q : PROP) (H : P ⊢ Q) : P -∗ Q := by
  ihave HPQ := H
  iexact HPQ

/-- Tests `ihave` with forall specialization from Lean. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  ihave H' := H $$ %a %b
  iapply H' $$ HP

/-- Tests `ihave` with forall specialization from hypothesis. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  ihave H' := H $$ %a %b HP
  iexact H'

/-- Tests `ihave` with intuitionistic forall specialization from Lean. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  ihave H' := H $$ %a %b
  iapply H' $$ HP

/-- Tests `ihave` with intuitionistic forall specialization and subgoal. -/
example [BI PROP] {α} (P Q : α → PROP) (a b : α) : (□ ∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  ihave H' := H $$ %a %b [HP]
  . iexact HP
  iexact H'

/-- Tests `ihave` with cases pattern. -/
example [BI PROP] (P Q : PROP) : (□P ∗ Q) -∗ Q := by
  iintro H
  ihave ⟨#_, HQ⟩ := H
  iexact HQ

/-- Tests `ihave` not removing a destructed hyp. -/
example [BI PROP] [BIAffine PROP] (Q : PROP) :
  □ (Q ∗ Q) ⊢ (□ (Q ∗ Q) ∗ □ Q) ∗ □ Q := by
  iintro #HQ
  ihave ⟨HQ, HQ2⟩ := HQ
  istop
  exact .rfl

/-- Tests `ihave` assert. -/
example [BI PROP] (P Q : PROP) : P -∗ (P -∗ Q) -∗ Q := by
  iintro HP Hwand
  ihave ⟨HQ, _⟩ : (Q ∗ emp) $$ [Hwand HP]
  . isplit
    . iapply Hwand $$ HP
    . itrivial
  iexact HQ

/-- Tests `ihave` assert duplicating the context. -/
example [BI PROP] (P Q : PROP) (h : P ⊢ □ Q) : ⊢ P -∗ P ∗ Q := by
  iintro HP
  ihave #HQ : □Q $$ [HP]
  · iapply h $$ HP
  isplitl
  · iexact HP
  · iexact HQ

/--
  Tests `ihave` with the specialization pattern involving modalities.
  Despite `try_dup_context` being `true`, the context is not duplicated.
-/
example [BI PROP] [BIAffine PROP] [BIUpdate PROP] (P : PROP) [Persistent P] :
    |==> P ⊢ |==> P := by
  iintro HP
  ihave #HP : P $$ [> HP //]
  imodintro
  iexact HP

/-- Tests `ihave` with the specialization pattern involving auto-framing with modalities. -/
example [BI PROP] [BIAffine PROP] [BIUpdate PROP] (P : PROP) [Persistent P] :
    |==> P ⊢ |==> P := by
  iintro HP
  ihave #HP : P $$ [>$]
  imodintro
  iexact HP

/--
  Tests `ihave` with a destruction pattern involving a conjunction of
  intuitionistic hypotheses.
-/
example [BI PROP] (P Q1 Q2 : PROP) [Persistent Q1] [Persistent Q2] :
    ⊢ P -∗ (P -∗ □ Q1 ∗ □ Q2) -∗ P ∗ (P -∗ □ Q1 ∗ □ Q2) := by
  iintro HP HPQ
  ihave ⟨#HQ1, #HQ2⟩ : □ Q1 ∗ □ Q2 $$ [HP HPQ]
  · iapply HPQ $$ HP
  · isplitl [HP] <;> iassumption

end ihave

section iexfalso

/-- Tests false elimination via empty pattern. -/
example [BI PROP] (Q : PROP) : False ⊢ Q := by
  iintro ⟨⟩

/-- Tests `iexfalso` with false hypothesis. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ False -∗ Q := by
  iintro _HP HF
  iexfalso
  iexact HF

/-- Tests `iexfalso` with pure false from Lean. -/
example [BI PROP] (P : PROP) (HF : False) : ⊢ P := by
  istart
  iexfalso
  ipureintro
  exact HF

end iexfalso

section ipure

/-- Tests `ipure` to move pure hypothesis to Lean context. -/
example [BI PROP] {φ} (Q : PROP) : <affine> ⌜φ⌝ ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

/-- Tests `ipure` with multiple pure hypotheses. -/
example [BI PROP] {φ1 φ2} (Q : PROP) : <affine> ⌜φ1⌝ ⊢ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
  iintro Hφ1
  iintro Hφ2
  iintro HQ
  ipure Hφ1
  ipure Hφ2
  iexact HQ

/-- Tests `ipure` with conjunction containing pure. -/
example [BI PROP] (Q : PROP) : (⌜φ1⌝ ∧ <affine> ⌜φ2⌝) ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

/-- Tests `ipure` with an `rcases` destruction pattern. -/
example [BI PROP] {φ1 φ2} (Q : PROP) : (⌜φ1⌝ ∧ <affine> ⌜φ2⌝) ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ with ⟨hφ1, -⟩
  iexact HQ

/-- Tests `ipure` with implication containing pure. -/
example [BI PROP] {φ1 φ2 φ3} (Q : PROP) : <affine> (⌜φ1⌝ ∧ ⌜φ2⌝ → ⌜φ3⌝) ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

/- Tests `ipure` failure. -/
/-- error: ipure: P is not pure -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q := by
  iintro HP
  ipure HP

/- Tests `ipure` failure for non-affine. -/
/-- error: ipure: iprop(⌜φ⌝) is not affine and the goal not absorbing -/
#guard_msgs in
example [BI PROP] φ (Q : PROP) : ⌜φ⌝ ⊢ Q := by
  iintro HP
  ipure HP

end ipure

section iintuitionistic

/-- Tests `iintuitionistic` to move hypothesis to intuitionistic context. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iexact HQ

/-- Tests `iintuitionistic` with multiple hypotheses. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iintuitionistic HQ
  iexact HQ

/-- Tests `iintuitionistic` applied twice to same hypothesis. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iintuitionistic HP
  iexact HQ

/- Tests `iintuitionistic` failure for non-persistent assumption. -/
/-- error: icases: P not persistent -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q := by
  iintro HP
  iintuitionistic HP

/- Tests `iintuitionistic` failure for non-affine assumption. -/
/-- error: icases: iprop(<pers> P) not affine and the goal not absorbing -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : <pers> P ⊢ Q := by
  iintro HP
  iintuitionistic HP

end iintuitionistic

section ispatial

/-- Tests `ispatial` to move hypothesis to spatial context. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro #HP
  iintro #HQ
  ispatial HP
  iexact HQ

/-- Tests `ispatial` with multiple hypotheses. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro #HP
  iintro #HQ
  ispatial HP
  ispatial HQ
  iexact HQ

/-- Tests `ispatial` applied twice to same hypothesis. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro #HP
  iintro #HQ
  ispatial HP
  ispatial HP
  iexact HQ

end ispatial

section iempintro

/-- Tests `iempintro` for proving emp. -/
example [BI PROP] : ⊢@{PROP} emp := by
  iempintro

/-- Tests `iempintro` with affine environment. -/
example [BI PROP] (P : PROP) : <affine> P ⊢ emp := by
  iintro _HP
  iempintro

/-- Tests that `itrivial` subsumes `iempintro`. -/
example [BI PROP] (P : PROP) : <affine> P ⊢ emp := by
  iintro _HP
  itrivial

end iempintro

section ipureintro

/-- Tests `ipureintro` for True. -/
example [BI PROP] : ⊢@{PROP} ⌜True⌝ := by
  ipureintro
  exact True.intro

/-- Tests `ipureintro` for disjunction. -/
example [BI PROP] : ⊢@{PROP} True ∨ False := by
  ipureintro
  apply Or.inl True.intro

/-- Tests `ipureintro` with context. -/
example [BI PROP] (p q : Prop) (H : p → q) (P Q : PROP) : <affine> P ⊢ <pers> Q → ⌜p⌝ → ⌜q⌝ := by
  iintro _HP #_HQ
  ipureintro
  exact H

/-- Tests `ipureintro` with wand containing pure and affine lhs. -/
example [BI PROP] {φ} : ⊢@{PROP} (<affine> ⌜φ⌝ -∗ emp) := by
  ipureintro
  intro _; trivial

/-- Tests `ipureintro` with wand containing pure and absorbing rhs. -/
example [BI PROP] {φ} : ⊢@{PROP} (⌜φ⌝ -∗ <absorb> emp) := by
  ipureintro
  intro _; trivial

/- Tests `ipureintro` failure. -/
/-- error: ipureintro: P is not pure -/
#guard_msgs in
example [BI PROP] (P : PROP) : ⊢ P := by
  ipureintro

end ipureintro

section ispecialize

/-- Tests `ispecialize` with spatial wand. -/
example [BI PROP] (P Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with subgoal. -/
example [BI PROP] (P Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ [HP]
  . iexact HP
  iexact HPQ

/-- Tests `ispecialize` with subgoal and `//`. -/
example [BI PROP] (P Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ [HP //]
  iexact HPQ

-- Test `ispecialize` with failing `//`
/--
error: ispecialize: itrivial could not solve
⊢ False
-/
#guard_msgs in
example [BI PROP] (Q : PROP) : ⊢ (False -∗ Q) -∗ Q := by
  iintro HQ
  ispecialize HQ $$ [//]


/-- Tests `ispecialize` with named subgoal. -/
example [BI PROP] (P Q : PROP) : P ⊢ (⌜True⌝ -∗ P -∗ ⌜True⌝ -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ %True.intro [HP] as G %True.intro
  case G => iexact HP
  iexact HPQ

/-- Tests `ispecialize` with negated subgoal. -/
example [BI PROP] (P Q R : PROP) : P ⊢ R -∗ (P -∗ R -∗ Q) -∗ Q := by
  iintro HP HR HPQ
  ispecialize HPQ $$ [- HR] [-]
  . iexact HP
  . iexact HR
  iexact HPQ

/-- Tests `ispecialize` with framing subgoal. -/
example [BI PROP] (P Q R : PROP) : P ⊢ P -∗ R -∗ (P ∗ P -∗ R -∗ Q) -∗ Q := by
  iintro HP1 HP2 HR HPQ
  ispecialize HPQ $$ [$HP1 HP2] [-]
  . iexact HP2
  . iexact HR
  iexact HPQ

/-- Tests `ispecialize` with framing subgoal (different argument order). -/
example [BI PROP] (P Q R : PROP) : P ⊢ P -∗ R -∗ (P ∗ P -∗ R -∗ Q) -∗ Q := by
  iintro HP1 HP2 HR HPQ
  ispecialize HPQ $$ [HP1 $HP2] [-]
  . iexact HP1
  . iexact HR
  iexact HPQ

/-- Tests `ispecialize` with negated framing subgoal. -/
example [BI PROP] (P Q R : PROP) : P ⊢ P -∗ R -∗ (P ∗ P -∗ R -∗ Q) -∗ Q := by
  iintro HP1 HP2 HR HPQ
  ispecialize HPQ $$ [- $HP1 HR] [-]
  . iexact HP2
  . iexact HR
  iexact HPQ

/-- Tests `ispecialize` with negated framing subgoal (different argument order). -/
example [BI PROP] (P Q R : PROP) : P ⊢ P -∗ R -∗ (P ∗ P -∗ R -∗ Q) -∗ Q := by
  iintro HP1 HP2 HR HPQ
  ispecialize HPQ $$ [- HR $HP2] [-]
  . iexact HP1
  . iexact HR
  iexact HPQ

/- Tests `ispecialize` with autoframe. -/
example [BI PROP] (P Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ [$]
  iexact HPQ

/-- Tests `ispecialize` with more complex autoframe. -/
example [BI PROP] (P Q R : PROP) : P ⊢ P -∗ R -∗ (P ∗ P -∗ R -∗ Q) -∗ Q := by
  iintro HP1 HP2 HR HPQ
  ispecialize HPQ $$ [$] [$]
  iexact HPQ

/-- Tests `ispecialize` with even more complex autoframe. -/
example [BI PROP] (P : Nat → PROP) (Q R : PROP) :
    P 1 ⊢ □ P 1 -∗ P 2 -∗ R -∗ (∀ n, ((□ P n ∗ R ∗ P n) -∗ P 2 -∗ Q)) -∗ Q := by
  iintro HP1 #HP1' HP2 HR HPQ
  ispecialize HPQ $$ [$] [$]
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic wand. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ □ (P -∗ Q) -∗ □ Q := by
  iintro #HP #HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic wand and subgoal. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ □ (P -∗ Q) -∗ Q := by
  iintro #HP #HPQ
  ispecialize HPQ $$ []
  . iexact HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic wand requiring intuitionistic argument. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ □ (□ P -∗ Q) -∗ □ Q := by
  iintro #HP #HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic premise and spatial wand. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ (P -∗ Q) -∗ Q := by
  iintro #HP HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic premise required by spatial wand. -/
example [BI PROP] (P Q : PROP) : □ P ⊢ (□ P -∗ Q) -∗ Q := by
  iintro #HP HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with spatial premise and intuitionistic wand. -/
example [BI PROP] (P Q : PROP) : P ⊢ □ (P -∗ Q) -∗ Q := by
  iintro HP #HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with multiple spatial arguments. -/
example [BI PROP] (P1 P2 Q : PROP) : P1 -∗ P2 -∗ (P1 -∗ P2 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HPQ
  ispecialize HPQ $$ HP1 HP2
  iexact HPQ

/-- Tests `ispecialize` with multiple subgoals. -/
example [BI PROP] (P1 P2 Q : PROP) : P1 -∗ P2 -∗ (P1 -∗ P2 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HPQ
  ispecialize HPQ $$ [HP1] [HP2]
  . iexact HP1
  . iexact HP2
  iexact HPQ

/-- Tests `ispecialize` with multiple intuitionistic arguments. -/
example [BI PROP] (P1 P2 Q : PROP) :
    ⊢ □ P1 -∗ □ P2 -∗ □ (P1 -∗ □ P2 -∗ Q) -∗ □ Q := by
  iintro #HP1 #HP2 #HPQ
  ispecialize HPQ $$ HP1 HP2
  iexact HPQ

/-- Tests `ispecialize` with mixed spatial and intuitionistic arguments. -/
example [BI PROP] (P1 P2 P3 Q : PROP) :
    ⊢ P1 -∗ □ P2 -∗ P3 -∗ □ (P1 -∗ P2 -∗ P3 -∗ Q) -∗ Q := by
  iintro HP1 #HP2 HP3 HPQ
  ispecialize HPQ $$ HP1 HP2 HP3
  iexact HPQ

/-- Tests `ispecialize` with forall in spatial context. -/
example [BI PROP] (y : Nat) (Q : Nat → PROP) : (∀ x, Q x) -∗ Q (y + 1) := by
  iintro HQ
  ispecialize HQ $$ %(y + 1)
  iexact HQ

/-- Tests `ispecialize` with forall in intuitionistic context. -/
example [BI PROP] (y : Nat) (Q : Nat → PROP) : □ (∀ x, Q x) -∗ □ Q y := by
  iintro #HQ
  ispecialize HQ $$ %y
  iexact HQ

/-- Tests `ispecialize` with forall returning intuitionistic proposition. -/
example [BI PROP] (y : Nat) (Q : Nat → PROP) : (∀ x, □ Q x) -∗ □ Q y := by
  iintro HQ
  ispecialize HQ $$ %y
  iexact HQ

/-- Tests `ispecialize` with multiple forall in spatial context. -/
example [BI PROP] (x y : Nat) (Q : Nat → Nat → PROP) :
    ⊢ (∀ x, ∀ y, Q x y) -∗ Q x y := by
  iintro HQ
  ispecialize HQ $$ %x %y
  iexact HQ

/-- Tests `ispecialize` with multiple forall in intuitionistic context. -/
example [BI PROP] (x y : Nat) (Q : Nat → Nat → PROP) :
    ⊢ □ (∀ x, ∀ y, Q x y) -∗ □ Q x y := by
  iintro #HQ
  ispecialize HQ $$ %x %y
  iexact HQ

/-- Tests `ispecialize` with nested forall and intuitionistic. -/
example [BI PROP] (x y : Nat) (Q : Nat → Nat → PROP) : (∀ x, □ (∀ y, Q x y)) -∗ □ Q x y := by
  iintro HQ
  ispecialize HQ $$ %x %y
  iexact HQ

/-- Tests `ispecialize` with mixed forall and wand specialization. -/
example [BI PROP] (y : Nat) (P1 P2 : PROP) (Q : Nat → PROP) :
    ⊢ □ P1 -∗ P2 -∗ (□ P1 -∗ (∀ x, P2 -∗ Q x)) -∗ Q y := by
  iintro #HP1 HP2 HPQ
  ispecialize HPQ $$ HP1 %y HP2
  iexact HPQ

/-- Tests `ispecialize` with pure True wand using `.intro`. -/
example [BI PROP] (P : PROP) :
    ⊢ (True -∗ P) -∗ P := by
  iintro H
  ispecialize H $$ %.intro
  iexact H

/-- Tests `ispecialize` with pure wand using tactic. -/
example [BI PROP] (P : PROP) :
    ⊢ (True -∗ P) -∗ P := by
  iintro H
  ispecialize H $$ %(by grind)
  iexact H

/-- Tests `ispecialize` alternating pure and spatial arguments. -/
example [BI PROP] (P Q : PROP) :
    ⊢ (∀ x, P -∗ ⌜x = 1⌝ -∗ Q) -∗ P -∗ Q := by
  iintro H HP
  ispecialize H $$ %_ HP %rfl
  iexact H

/-- Tests `ispecialize` with pure subgoal. -/
example [BI PROP] (P Q : PROP) :
    ⊢ (∀ x, P -∗ ⌜x = 1⌝ -∗ Q) -∗ P -∗ Q := by
  iintro H HP
  ispecialize H $$ %_ HP %_
  · rfl
  iexact H

/-- Tests `ispecialize` with subgoals excluding specified hypotheses -/
example [BI PROP] (P1 P2 P3 Q : PROP) : P1 -∗ P2 -∗ P3 -∗ (P1 -∗ P2 -∗ P3 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HP3 HPQ
  ispecialize HPQ $$ [- HP2 HP3] [- HP3] [-]
  · iexact HP1
  · iexact HP2
  · iexact HP3
  iexact HPQ

/-- Tests `ispecialize` with autoframing for the intuitionistic kind -/
example [BI PROP] (P1 P2 P3 Q : PROP) :
    □ P1 -∗ <pers> P2 -∗ □ P3 -∗ (□ P1 -∗ <pers> P2 -∗ <pers> P3 -∗ Q) -∗ Q := by
  iintro #HP1 HP2 #HP3 HPQ
  ispecialize HPQ $$ [# $] [$] [# $]
  iexact HPQ

/--
  Tests `ispecialize` with autoframing with a persistent hypothesis in the
  spatial context used twice.
-/
example [BI PROP] (φ : Prop) (Q : PROP) :
    ⌜φ⌝ -∗ (⌜φ⌝ -∗ Q) -∗ (⌜φ⌝ -∗ Q) -∗ ⌜φ⌝ ∗ Q ∗ Q := by
  iintro HP1 HPQ1 HPQ2
  ispecialize HPQ1 $$ [# $]
  ispecialize HPQ2 $$ [# $]
  iframe

/- Tests `ispecialize` with autoframing, but the premise is not persistent. -/
/-- error: ispecialize: P is not persistent -/
#guard_msgs in
example [BI PROP] (φ : Prop) (P Q : PROP) :
    P -∗ (P -∗ Q) -∗ True := by
  iintro HP HPQ
  ispecialize HPQ $$ [# $]

/-- Tests `ispecialize` for a persistent premise with chosen hypotheses for the subgoal. -/
example [BI PROP] (P1 P2 P3 Q : PROP) :
    <pers> P1 -∗ <pers> P2 -∗ <pers> P3 -∗
    ((<pers> P1 ∗ <pers> P2) -∗ Q) -∗
    ((<pers> P1 ∗ <pers> P3) -∗ Q) -∗
    <pers> P1 ∗ <pers> P2 ∗ <pers> P3 ∗ Q ∗ Q := by
  iintro HP1 HP2 HP3 HPQ12 HPQ13
  ispecialize HPQ12 $$ [# $HP1]
  · iexact HP2
  ispecialize HPQ13 $$ [# $HP1 $HP3]
  iframe

/-
  Tests `ispecialize` for handling a persistent premise, except that the
  premise is not persistent.
-/
/-- error: ispecialize: P is not persistent -/
#guard_msgs in
example [BI PROP] (φ : Prop) (P Q : PROP) :
    P -∗ (P -∗ Q) -∗ True := by
  iintro HP HPQ
  ispecialize HPQ $$ [# $HP]

/- Tests `ispecialize` with hypotheses chosen to be consumed for a persistent premise. -/
/-- error: ispecialize: cannot select hypotheses for intuitionistic premise -/
#guard_msgs in
example [BI PROP] (φ : Prop) (P Q : PROP) :
    <pers> P -∗ (<pers> P -∗ Q) -∗ True := by
  iintro HP HPQ
  ispecialize HPQ $$ [# HP]

/-- Tests `ispecialize` with nested specialization patterns. -/
example [BI PROP] (P Q R S T : PROP) :
    ⊢ (P -∗ <pers> T -∗ Q) -∗ (Q -∗ <pers> T -∗ R) -∗ (R -∗ S) -∗ P -∗ <pers> T -∗ S := by
  iintro HPTQ HQTR HRS HP HT
  ispecialize HRS $$ (HQTR $$ (HPTQ $$ HP [# $HT]) [HT //])
  iassumption

/--
  Tests `ispecialize` with `.autoframe .modal` using the type class instance
  `addModal_bupd` and `addModal_fupd`.
-/
example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] (P Q R S : PROP) (E : CoPset) :
    ⊢ (P -∗ Q) -∗ (R -∗ S) -∗ (|==> P) -∗ (|={E}=> R) -∗ (|==> Q) ∗ (|={E}=> S) := by
  iintro HPQ HRS HP HR
  isplitl [HPQ HP]
  · ispecialize HPQ $$ [>$]
    imodintro
    iassumption
  · ispecialize HRS $$ [>$]
    imodintro
    iassumption

/-- Tests `ispecialize` for its use of the type class instance `add_modal_forall`,
  `add_modal_bupd` and `add_modal_later`. -/
example [BI PROP] [BIUpdate PROP]
    (P : PROP) (Q : Nat → PROP) (R S : PROP) [Timeless R] :
    ⊢ (P -∗ (∀ x, Q x)) -∗ (|==> P) -∗ (R -∗ S) -∗ (▷ R) -∗
      (∀ x, |==> Q x) ∗ (▷ S) := by
  iintro HPQ HP HRS HR
  isplitl [HPQ HP]
  · ispecialize HPQ $$ [>$]
    iintro %x
    ispecialize HPQ $$ %x
    imodintro
    iassumption
  · ispecialize HRS $$ [> HR]
    · imod HR
      iassumption
    · inext
      iassumption

/-- Tests `ispecialize` for its use of the type class instance `add_modal_fupd_wp`. -/
example {hlc : HasLC} {Expr State Obs Val : Type _} [Language Expr State Obs Val]
    {GF : BundledGFunctors} [IrisGS_gen hlc Expr GF]
    (s : Stuckness) (E : CoPset) (e : Expr) (P : IProp GF) (Φ : Val → IProp GF) :
    ⊢ (P -∗ WP e @ s ; E {{ Φ }}) -∗ (|={E}=> P) -∗ WP e @ s ; E {{ Φ }} := by
  iintro HPQ HP
  ispecialize HPQ $$ [>$]
  iassumption

/--
  Tests `ispecialize` with the handling of the modality using the type class
  instance `addModal_bupd`. The subgoal is manually solved.
-/
example [BI PROP] [BIUpdate PROP] (P Q : PROP) :
    ⊢ (P -∗ Q) -∗ (|==> P) -∗ (|==> Q) := by
  iintro HPQ HP
  ispecialize HPQ $$ [> HP]
  · iassumption
  · imodintro
    iassumption

/--
  Tests `ispecialize` with the handling of the modality, nested patterns and
  the use of the type class instance `addModal_wand`.
-/
example [BI PROP] [BIUpdate PROP] (P Q R : PROP) :
    ⊢ (P -∗ R) -∗ (Q -∗ P) -∗ (|==> Q) -∗ (|==> R) := by
  iintro HPR HQP HQ
  ispecialize HPR $$ (HQP $$ [> HQ //])
  imodintro
  iassumption

/--
  Tests `ispecialize` with the auto-framing with modality, nested patterns and
  the use of the type class instance `addModal_wand`.
-/
example [BI PROP] [BIUpdate PROP] (P Q R : PROP) :
    ⊢ (P -∗ R) -∗ (Q -∗ P) -∗ (|==> Q) -∗ (|==> R) := by
  iintro HPR HQP HQ
  ispecialize HPR $$ (HQP $$ [> $])
  imodintro
  iassumption

/- Tests `ispecialize` with an invalid specialization pattern (duplicated hypotheses). -/
/-- error: ispecialize: HP used twice for framing -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ [$HP $HP]

/- Tests `ispecialize` with an invalid specialization pattern (duplicated hypotheses). -/
/-- error: ispecialize: HP cannot be used for both the subgoal and framing -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ [HP $HP]

/- Tests `ispecialize` with an invalid hypothesis choice. -/
/-- error: ispecialize: P is not a wand -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q := by
  iintro HP
  ispecialize HP $$ [$]

/- Tests `ispecialize` with an invalid specialization pattern. -/
/-- error: ispecialize: IntoWand type class synthesis failed with P and Q -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q -∗ Q := by
  iintro HP HQ
  ispecialize HP $$ HQ

/- Tests `ispecialize` with an invalid specialization pattern using pure hypotheses. -/
/-- error: ispecialize: P is not a Lean premise -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q := by
  iintro HP
  ispecialize HP $$ %(0 : Nat)

/-- Tests `ispecialize` with a specialization pattern naming the subgoal. -/
example [BI PROP] [BIUpdate PROP] (P Q : PROP) :
    ⊢ (P -∗ Q) -∗ (|==> P) -∗ (|==> Q) := by
  iintro HPQ HP
  ispecialize HPQ $$ [> HP] as subgoal
  case subgoal => iassumption
  imodintro; iassumption

/-- Tests `ispecialize` using `AddModal` instances for `▷` and `◇`. -/
example [BI PROP] (P Q R S : PROP) :
    ⊢ (P -∗ Q) -∗ P -∗ (R -∗ ◇ S) -∗ R -∗ ▷ Q ∗ ◇ S := by
  iintro HPQ HP HRS HR
  isplitl [HPQ HP]
  -- Using `addModal_except_0_later` after `addModal_later` fails and backtrackes.
  · ispecialize HPQ $$ [> HP]
    · imodintro; iassumption
    · inext; iassumption
  -- Using `addModal_except_0` after `addModal_later_except_0` fails and backtracks
  · ispecialize HRS $$ [> HR]
    · imodintro; iassumption
    · iassumption

/-
  `Q` is not a wand, so no `IntoWand` instance applies.
  This fails immediately instead of looping with
  `into_wand_bupd_args` because the mode does not match.
-/
set_option pp.mvars false in
/-- [Meta.synthInstance] ❌️ IPM: new goal ProofMode.IntoWand false false Q ProofMode.WandMode.unknown ?_
        ?_ => ProofMode.IntoWand false false Q ProofMode.WandMode.unknown ?_ ?_
    [Meta.synthInstance.tactics] []
    [Meta.synthInstance.instances] #[]
-/
#guard_msgs (substring := true) in
example [BI PROP] [BIUpdate PROP] (P Q: PROP) : Q ⊢ P -∗ Q := by
  iintro HQ
  set_option trace.Meta.synthInstance true in
  ispecialize HQ $$ [$]

/- Tests `ispecialize` with an invalid hypothesis name in the proof mode term. -/
/-- error: ispecialize: invalid hypothesis H -/
#guard_msgs in
example [BI PROP] [BIUpdate PROP] (P Q : PROP) :
    ⊢ (P -∗ Q) -∗ (|==> P) -∗ (|==> Q) := by
  iintro HPQ HP
  ispecialize HPQ $$ H

end ispecialize

section isplit

/-- Tests `isplit` for conjunction. -/
example [BI PROP] (Q : PROP) : Q ⊢ Q ∧ Q := by
  iintro HQ
  isplit <;> iexact HQ

/-- Tests `isplitl` with explicit left hypotheses. -/
example [BI PROP] [BIAffine PROP] (P Q R : PROP) : P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro HQ
  iintro _HR
  isplitl [HP _HR]
  · iexact HP
  · iexact HQ

/-- Tests `isplitr` with explicit right hypotheses. -/
example [BI PROP] [BIAffine PROP] (P Q R : PROP) : P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro HQ
  iintro _HR
  isplitr [HQ]
  · iexact HP
  · iexact HQ

/-- Tests `isplitl` without argument. -/
example [BI PROP] [BIAffine PROP] (P Q R : PROP) : P -∗ □ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro #HQ
  iintro _HR
  isplitl
  · iexact HP
  · iexact HQ

/-- Tests `isplitr` without argument. -/
example [BI PROP] [BIAffine PROP] (P Q R : PROP) : □ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro #HP
  iintro HQ
  iintro _HR
  isplitr
  · iexact HP
  · iexact HQ

/-- Tests `isplit` for iff. -/
example [BI PROP] (Q : PROP) : ⊢ (Q ↔ Q) := by
  isplit <;> iintro HQ <;> iexact HQ

end isplit

section ileft_iright

/-- Tests `ileft`. -/
example [BI PROP] (P Q : PROP) : P ⊢ P ∨ Q := by
  iintro HP
  ileft
  iexact HP

/-- Tests `iright`. -/
example [BI PROP] (P Q : PROP) : Q ⊢ P ∨ Q := by
  iintro HQ
  iright
  iexact HQ

/-- Tests nested disjunction with left and right. -/
example [BI PROP] (P Q R : PROP) : P -∗ Q -∗ P ∗ (R ∨ Q ∨ R) := by
  iintro HP HQ
  isplitl [HP]
  · iassumption
  iright
  ileft
  iexact HQ

/- Tests `ileft` failure. -/
/-- error: ileft: Q is not a disjunction -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q := by
  iintro HP
  ileft

/- Tests `iright` failure. -/
/-- error: iright: Q is not a disjunction -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ⊢ Q := by
  iintro HP
  iright

end ileft_iright

section icases

/-- Tests `icases` for simple renaming. -/
example [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  icases HP with H
  iexact H

/-- Tests `icases` to clear hypothesis. -/
example [BI PROP] (P Q : PROP) : P -∗ <affine> Q -∗ P := by
  iintro HP
  iintro HQ
  icases HQ with -
  iexact HP

/-- Tests `icases` to frame hypothesis. -/
example [BI PROP] (P : PROP) : ⊢ P -∗ P := by
  iintro HP
  icases HP with $

/-- Tests `icases` to frame persistent hypothesis. -/
example [BI PROP] (P Q : PROP) : ⊢ □ P -∗ (P -∗ Q) -∗ P ∗ Q := by
  iintro #HP Hwand
  icases HP with $
  iapply Hwand
  iframe #

/-- Tests `icases` with complex pattern involving framing. -/
example [BI PROP] (P Q R : PROP) : ⊢ ((P ∗ □ Q ∗ (□ R ∨ R))) -∗ P ∗ Q ∗ R := by
  iintro HP
  icases HP with ⟨$, #HQ, ⟨#$ | $⟩⟩ <;> iframe #

/-- Tests `icases` with nested conjunction. -/
example [BI PROP] (P1 P2 Q : PROP) : □ (P1 ∧ P2 ∧ Q) ⊢ Q := by
  iintro #HP
  icases HP with ⟨_HP1, _HP2, HQ⟩
  iexact HQ

/-- Tests `icases` with intuitionistic conjunction. -/
example [BI PROP] (P Q : PROP) : □ P ∧ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨_HP, HQ⟩
  iexact HQ

/-- Tests `icases` on conjunction with persistent left. -/
example [BI PROP] (P Q : PROP) : <pers> Q ∧ <affine> P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨#HQ, _HP⟩
  iexact HQ

/-- Tests `icases` on conjunction with persistent right. -/
example [BI PROP] (P Q : PROP) : Q ∧ <pers> P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, _HP⟩
  iexact HQ

/- Tests `icases` on conjunction with persistent right in an affine logic. -/
/-- trace:
PROP : Type u_1
inst✝¹ : BI PROP
inst✝ : BIAffine PROP
P Q : PROP
⊢ ⏎
  ∗x✝ : P
  ∗HQ : <pers> Q
  ⊢ Q
-/
#guard_msgs (whitespace := lax, trace, drop all) in
example [BI PROP] [BIAffine PROP] (P Q : PROP) :
  P ∧ <pers> Q ⊢ Q := by
  iintro H
  icases H with ⟨_, HQ⟩
  trace_state

/-- Tests `icases` with nested separating conjunction. -/
example [BI PROP] [BIAffine PROP] (P1 P2 Q : PROP) : P1 ∗ P2 ∗ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨_HP1, _HP2, HQ⟩
  iexact HQ

/-- Tests `icases` with nested disjunction. -/
example [BI PROP] (P1 P2 P3 Q : PROP) : Q ⊢ <affine> (P1 ∨ P2 ∨ P3) -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (_HP1 | _HP2 | _HP3) <;> iexact HQ

/- Tests `icases` failure too many nested disjunction. -/
/-- error: icases: P2 is not a disjunction -/
#guard_msgs in
example [BI PROP] (P1 P2 Q : PROP) : Q ⊢ (P1 ∨ P2) -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (_HP1 | _HP2 | _HP3)

/-- Tests `icases` with complex mixed conjunction and disjunction. -/
example [BI PROP] [BIAffine PROP]
    (P11 P12 P13 P2 P31 P32 P33 Q : PROP) :
    (P11 ∨ P12 ∨ P13) ∗ P2 ∗ (P31 ∨ P32 ∨ P33) ∗ Q ⊢ Q := by
  iintro HP
  icases HP with ⟨_HP11 | _HP12 | _HP13, HP2, HP31 | HP32 | HP33, HQ⟩ <;> iexact HQ

/-- Tests `icases` moving pure to Lean context with %. -/
example [BI PROP] (Q : PROP) : <affine> ⌜⊢ Q⌝ -∗ Q := by
  iintro HQ
  icases HQ with %HQ
  istop
  exact HQ

/-- Tests `icases` moving pure to Lean context with %. -/
example [BI PROP] (Q : PROP) : <affine> ⌜⊢ Q⌝ -∗ Q := by
  iintro HQ
  icases HQ with %HQ
  istop
  exact HQ

/-- Tests `icases` moving to intuitionistic with #. -/
example [BI PROP] (Q : PROP) : □ Q -∗ Q := by
  iintro HQ
  icases HQ with #HQ
  iexact HQ

/-- Tests `icases` moving to intuitionistic with #. -/
example [BI PROP] (Q : PROP) : □ Q -∗ Q := by
  iintro HQ
  icases HQ with #HQ
  iexact HQ

/-- Tests `icases` moving to spatial with ∗. -/
example [BI PROP] (Q : PROP) : □ Q -∗ Q := by
  iintro #HQ
  icases HQ with ∗HQ
  iexact HQ

/-- Tests `icases` moving to spatial with ∗ only. -/
example [BI PROP] (Q : PROP) : □ Q -∗ Q := by
  iintro #HQ
  icases HQ with ∗HQ
  iexact HQ

/-- Tests `icases` with pure in conjunction. -/
example [BI PROP] {φ} (Q : PROP) : <affine> ⌜φ⌝ ∗ Q -∗ Q := by
  iintro HφQ
  icases HφQ with ⟨%Hφ, HQ⟩
  iexact HQ

/-- Tests `icases` with pure in disjunction. -/
example [BI PROP] {φ1 φ2} (Q : PROP) :
    ⊢ <affine> ⌜φ1⌝ ∨ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  icases Hφ with (%Hφ1 | %Hφ2) <;> iexact HQ

/-- Tests `icases` with intuitionistic in conjunction. -/
example [BI PROP] (P Q : PROP) : □ P ∗ Q -∗ Q := by
  iintro HPQ
  icases HPQ with ⟨#_HP, HQ⟩
  iexact HQ

/-- Tests `icases` with intuitionistic in disjunction. -/
example [BI PROP] (Q : PROP) : □ Q ∨ Q -∗ Q := by
  iintro HQQ
  icases HQQ with (#HQ | HQ) <;> iexact HQ

/-- Tests `icases` moving to spatial inside intuitionistic conjunction. -/
example [BI PROP] (P Q : PROP) : □ (P ∧ Q) -∗ Q := by
  iintro #HPQ
  icases HPQ with ⟨_HP, ∗HQ⟩
  iexact HQ

/-- Tests `icases` with or inside intuitionistic, moving one to spatial. -/
example [BI PROP] (Q : PROP) : □ (Q ∨ Q) -∗ Q := by
  iintro #HPQ
  icases HPQ with (HQ | ∗HQ) <;> iexact HQ

/-- Tests `icases` moving whole hypothesis to intuitionistic then destructing. -/
example [BI PROP] (P Q : PROP) : □ (P ∧ Q) -∗ Q := by
  iintro HPQ
  icases HPQ with #⟨_HP, ∗HQ⟩
  iexact HQ

/-- Tests `icases` with or, moving whole to intuitionistic. -/
example [BI PROP] (Q : PROP) : □ (Q ∨ Q) -∗ Q := by
  iintro HPQ
  icases HPQ with #(HQ | ∗HQ) <;> iexact HQ

/-- Tests `icases` clearing in conjunction. -/
example [BI PROP] [BIAffine PROP] (P Q : PROP) : Q ∗ P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

/-- Tests `icases` clearing in disjunction. -/
example [BI PROP] [BIAffine PROP] (P1 P2 Q : PROP) : Q ⊢ P1 ∨ P2 -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (- | _HP2) <;> iexact HQ

/-- Tests `icases` destructing conjunction left. -/
example [BI PROP] (P Q : PROP) : P ∧ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨-, HQ⟩
  iexact HQ

/-- Tests `icases` destructing conjunction right. -/
example [BI PROP] (P Q : PROP) : Q ∧ P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

/-- Tests `icases` destructing multiple conjunctions . -/
example [BI PROP] (P1 P2 P3 Q : PROP) : P1 ∧ P2 ∧ Q ∧ P3 ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨-, -, HQ, -⟩
  iexact HQ

/-- Tests `icases` destructing intuitionistic conjunction, clearing left. -/
example [BI PROP] (P Q : PROP) : □ (P ∧ Q) ⊢ Q := by
  iintro #HPQ
  icases HPQ with ⟨-, HQ⟩
  iexact HQ

/-- Tests `icases` destructing intuitionistic conjunction, clearing right. -/
example [BI PROP] (P Q : PROP) : □ (Q ∧ P) ⊢ Q := by
  iintro #HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

/-- Tests `icases` destructing multiple intuitionistic conjunctions. -/
example [BI PROP] (P1 P2 P3 Q : PROP) : □ (P1 ∧ P2 ∧ Q ∧ P3) ⊢ Q := by
  iintro #HPQ
  icases HPQ with ⟨-, -, HQ, -⟩
  iexact HQ

/-- Tests `icases` with existential. -/
example [BI PROP] (Q : Nat → PROP) : (∃ x, Q x) ⊢ ∃ x, Q x ∨ False := by
  iintro ⟨%x, H⟩
  iexists x
  ileft
  iexact H

/-- Tests `icases` with intuitionistic existential. -/
example [BI PROP] (Q : Nat → PROP) : □ (∃ x, Q x) ⊢ ∃ x, □ Q x ∨ False := by
  iintro ⟨%x, #H⟩
  iexists x
  ileft
  iexact H

/-- Tests `icases` with proof mode term. -/
example [BI PROP] P (Q : Nat → PROP) :
  (P -∗ ∃ x, □ Q x ∗ Q 1) ⊢ P -∗ Q 1 := by
  iintro Hwand HP
  icases Hwand $$ HP with ⟨%_, -, HQ⟩
  iexact HQ

/-- Tests `icases` with a comprehensive nested pattern combining existential, pure,
intuitionistic, spatial, disjunction, and clearing. -/
example [BI PROP] (φ : Prop) (Q : PROP) :
    □ (∃ _ : Nat, ⌜φ⌝ ∧ Q) ∗ (Q ∨ False) ⊢ Q := by
  iintro H
  icases H with ⟨#⟨%_, %_hφ, ∗HQ⟩, (HQ' | -)⟩
  · iexact HQ'
  · iexact HQ

/-- Tests `icases` with multiple mod patterns. -/
example [BI PROP] [BIUpdate PROP] (P Q : PROP) : (|==> P) ∗ (|==> Q) ⊢ |==> (P ∗ Q) := by
  iintro H
  icases H with ⟨>HP, >HQ⟩
  isplitl [HP]
  · iexact HP
  · iexact HQ

/-- Tests `icases` with a comprehensive nested fancy-update pattern combining mask changes,
existential, pure, disjunction, conjunction, clearing, and multiple mod eliminations. -/
example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP]
    (E1 E2 E3 : CoPset) (φ : Prop) (P Q : PROP) :
    (|={E1,E2}=> ∃ _ : Nat, ⌜φ⌝ ∧ P) ∗
      ((|={E2,E3}=> Q ∗ emp) ∨ (|={E2,E3}=> emp ∗ Q)) ⊢
      |={E1,E3}=> (P ∗ Q) := by
  iintro H
  icases H with ⟨>⟨%_, %_hφ, HP⟩, (>⟨HQ, -⟩ | >⟨-, HQ⟩)⟩
  all_goals
    imodintro
    isplitl [HP]
    · iexact HP
    · iexact HQ

/-- Tests `icases` duplicating the context. -/
example [BI PROP] (Q : PROP) (n : Nat) :
  □ (∀ x, Q -∗ ⌜x = n⌝) ⊢ Q -∗ False := by
  iintro #Hwand HQ
  icases Hwand $$ %1 HQ with %_
  icases Hwand $$ %2 HQ with %_
  grind

/-- Tests `icases` removing a destructed hyp. -/
example [BI PROP] [BIAffine PROP] (Q : PROP) :
  □ (Q ∗ Q) ⊢ □ Q ∗ □ Q := by
  iintro #HQ
  icases HQ with ⟨HQ, HQ2⟩
  istop
  exact .rfl

/-- Tests `icases` with False. -/
example [BI PROP] (Q : PROP) : False ⊢ Q := by
  iintro H
  icases H with ⟨⟩

/- Tests `icases` failing with empty conjunction. -/
/-- error: icases: cannot destruct Q as an empty conjunct -/
#guard_msgs in
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro H
  icases H with ⟨⟩

/- Tests `icases` failing to destruct. -/
/-- error: icases: cannot destruct Q -/
#guard_msgs in
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro H
  icases H with ⟨HA, HB⟩

/- Tests `icases` failing to destruct intuitionistic. -/
/-- error: icases: cannot destruct iprop(□ Q) -/
#guard_msgs in
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro H
  icases H with ⟨HA, HB⟩

/-- Tests `icases` with a case destruction pattern for rewriting pure equalities. -/
example [BI PROP] (m n : Nat) (a b c : Prop) :
    ⊢@{PROP} ⌜m = 2⌝ -∗ ⌜3 = n⌝ -∗ ⌜a = b⌝ -∗ ⌜b = c⌝ -∗ ⌜m.succ = n ∧ a = c⌝ := by
  iintro #H1 H2 #H3 H4
  icases H1 with %rfl
  icases H2 with %rfl
  icases H3 with %rfl
  icases H4 with %rfl
  ipureintro
  and_intros <;> rfl

/-
  Tests `icases` with a case destruction pattern for rewriting but the
  hypothesis is not a pure equality.
-/
/--
error: Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
  P

PROP : Type u_1
inst✝ : BI PROP
P : Prop
a✝ : P
⊢ emp ⊢ True
-/
#guard_msgs in
example [BI PROP] (P : Prop) : ⊢@{PROP} ⌜P⌝ -∗ True := by
  iintro HP
  icases HP with %rfl

/-
  Tests `icases` with a case destruction pattern for rewriting but the
  hypothesis is not a pure hypothesis.
-/
/-- error: icases: P is not pure -/
#guard_msgs in
example [BI PROP] (P : PROP) : ⊢@{PROP} P -∗ True := by
  iintro HP
  icases HP with %rfl

/-- Tests `icases` with non-trivial `rcases` destruction patterns. -/
example [BI PROP] (a b c1 c2 c3 : Prop) (P : Prop → Prop) :
    ⊢@{PROP} □ ⌜((a = b ∧ (b ∨ (c1 ∧ c2 ∧ c3))) ∧ ∃ x, P x)⌝ -∗ ⌜a ∨ c1⌝ ∗ ⌜∃ x, P x⌝ := by
  iintro Hpure
  icases Hpure with %⟨⟨rfl, ((hb : a) | ⟨hc, _, -⟩)⟩, @⟨d : Prop, hd⟩⟩
  · ipureintro <;> grind
  · ipureintro <;> grind

/-- Tests `icases` with a case destruction pattern involving substitution (`%rfl`). -/
example [BI PROP] n (P : Nat → PROP) : (<affine> ⌜n = 0⌝ ∗ P 0) ⊢ P n := by
  iintro H
  icases H with ⟨%rfl, Hp⟩
  iexact Hp

end icases

section imodintro

/-- Tests `imodintro` for absorbing (intuitionistic: id, spatial: id). -/
example [BI PROP] (P : PROP) : □ P ∗ P ⊢ <absorb> P := by
  iintro ⟨#HP1, HP2⟩
  imodintro
  iexact HP2

/-- Tests `iintro` for introducing modalities. -/
example [BI PROP] (P : PROP) : □ P ∗ P ⊢ <absorb> P := by
  iintro ⟨#HP1, HP2⟩ !>
  iexact HP2

/-- Tests `imodintro` for persistently (intuitionistic: id, spatial: clear). -/
example [BI PROP] (P : PROP) : □ P ∗ P ⊢ <pers> P := by
  iintro ⟨#HP1, HP2⟩
  imodintro
  iexact HP1

/-- Tests `imodintro` for affinely (intuitionistic: id, spatial: forall Affine). -/
example [BI PROP] (P : PROP) : □ P ∗ <affine> P ⊢ <affine> P := by
  iintro ⟨#HP1, HP2⟩
  imodintro
  iexact HP2

/- Tests `imodintro` for affinely (intuitionistic: id, spatial: forall Affine) failing. -/
/-- error: imodintro: hypothesis HP2: P does not satisfy Affine -/
#guard_msgs in
example [BI PROP] (P : PROP) : □ P ∗ P ⊢ <affine> P := by
  iintro ⟨#HP1, HP2⟩
  imodintro

/-- Tests `imodintro` for intuitionistically (intuitionistic: id, spatial: isEmpty). -/
example [BI PROP] (P : PROP) : □ P ∗ □ P ⊢ □ P := by
  iintro ⟨#HP1, #HP2⟩
  imodintro
  iexact HP2

/- Tests `imodintro` for intuitionistically (intuitionistic: id, spatial: isEmpty) failing. -/
/-- error: imodintro: spatial context is not empty -/
#guard_msgs in
example [BI PROP] (P : PROP) : □ P ∗ □ P ⊢ □ P := by
  iintro ⟨#HP1, HP2⟩
  imodintro

/-- Tests `imodintro` for plain (intuitionistic: .forall Plain, spatial: clear). -/
example [Sbi PROP] (P : PROP) [Plain P] : □ P ∗ P ⊢ ■ P := by
  iintro ⟨#HP1, HP2⟩
  imodintro
  iexact HP1

/-- Tests `imodintro` for bupd (intuitionistic: id, spatial: id). -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : □ P ∗ P ==∗ P := by
  iintro ⟨#HP1, HP2⟩
  imodintro
  iexact HP2

/-- Tests `imodintro` for later (both: transform). -/
example [BI PROP] (P : PROP) : □ ▷ P ∗ ▷ P ⊢ ▷ P := by
  iintro ⟨#HP1, HP2⟩
  imodintro
  iexact HP2

/-- Tests `imodintro` for later n (both: transform). -/
example [BI PROP] (n : Nat) (P : PROP) : □ ▷^[n] P ∗ ▷^[n] P ⊢ ▷^[n] P := by
  iintro ⟨#HP1, HP2⟩
  imodintro
  iexact HP2

/-- Tests `imodintro` for later n (NatCancel). -/
example [BI PROP] (P : PROP) : □ ▷^[5] P ∗ ▷^[3] P ⊢ ▷^[4] P := by
  iintro ⟨#HP1, HP2⟩
  imodintro
  iexact HP2

/-- Tests `imodintro` for complex later n (both: transform). -/
example [BI PROP] (n : Nat) (P : PROP) : □ ▷^[n] P ∗ ▷^[n] P ⊢ ▷^[n] P := by
  iintro H
  imodintro
  icases H with ⟨-, HP2⟩
  iexact HP2

/-- Tests `imodintro` with specifying the pattern. -/
example [BI PROP] (P : PROP) : □ P ∗ P ⊢ <absorb> P := by
  iintro ⟨#HP1, HP2⟩
  imodintro (<absorb> _)
  iexact HP2

/- Tests `imodintro` for no modality. -/
/-- error: imodintro: P is not a modality -/
#guard_msgs in
example [BI PROP] (P : PROP) : □ P ∗ P ⊢ P := by
  iintro ⟨#HP1, HP2⟩
  imodintro

/- Tests `imodintro` with specifying the wrong pattern. -/
set_option pp.mvars false in
/-- error: imodintro: iprop(<absorb> P) is not a modality matching iprop(□ ?_) -/
#guard_msgs in
example [BI PROP] (P : PROP) : □ P ∗ P ⊢ <absorb> P := by
  iintro ⟨#HP1, HP2⟩
  imodintro (□ _)

/-- Tests `imodintro` with nested modalities. -/
example [BI PROP] (P : PROP) : □ P ⊢ □ <pers> P := by
  iintro #HP
  imodintro
  imodintro
  iexact HP

/-- Tests `imodintro` for bupd with single hypothesis. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : P ⊢ |==> P := by
  iintro HP
  imodintro
  iexact HP

/-- Tests `imodintro` for fupd. -/
example [BI PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : P ={E}=∗ P := by
  iintro HP
  imodintro
  iexact HP

/- Tests `imodintro` for mask-changing fupd failing. -/
/-- error: Only non-mask-changing update modalities can be introduced directly.
      Use `iapply (fupd_mask_intro ...)` to introduce a mask-changing fancy update. -/
#guard_msgs in
example [BI PROP] [BIFUpdate PROP]
    (E1 E2 : CoPset) (P : PROP) : P ={E1,E2}=∗ P := by
  iintro HP
  imodintro

/-- Tests `imodintro` for bupd preserves both intuitionistic and spatial. -/
example [BI PROP] [BIUpdate PROP] (P Q : PROP) : □ P ∗ Q ⊢ |==> Q := by
  iintro ⟨#HP, HQ⟩
  imodintro
  iexact HQ

/-- Tests `imodintro` for persistently with only intuitionistic context. -/
example [BI PROP] (P : PROP) : □ P ∗ □ P ⊢ <pers> P := by
  iintro ⟨#HP1, #HP2⟩
  imodintro
  iexact HP1

/-- Tests `imodintro` for nested bupd. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : P ⊢ |==> |==> P := by
  iintro HP
  imodintro
  imodintro
  iexact HP

/-- Tests `imodintro` for later with multiple later hypotheses. -/
example [BI PROP] (P Q : PROP) : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  imodintro
  isplitl [HP]
  · iexact HP
  · iexact HQ

/-- Tests `imodintro` for later with intuitionistic later hypothesis. -/
example [BI PROP] (P : PROP) : □ ▷ P ∗ ▷ P ⊢ ▷ P := by
  iintro ⟨#HP, HQ⟩
  imodintro
  iexact HQ

/-- Tests `imodintro` followed by `imod`. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> P ⊢ |==> P := by
  iintro HP
  imod HP
  imodintro
  iexact HP

/-- Tests `imodintro` with explicit pattern for persistently. -/
example [BI PROP] (P : PROP) : □ P ⊢ <pers> P := by
  iintro #HP
  imodintro (<pers> _)
  iexact HP

/-- Tests `imodintro` for affinely with multiple spatial hypotheses. -/
example [BI PROP] (P Q : PROP) [Affine P] [Affine Q] : <affine> P ∗ <affine> Q ⊢ <affine> P := by
  iintro ⟨HP, HQ⟩
  imodintro
  iexact HP

/-- Tests `imodintro` for triple nested modalities. -/
example [BI PROP] (P : PROP) : □ P ⊢ □ <pers> <absorb> P := by
  iintro #HP
  imodintro
  imodintro
  imodintro
  iexact HP

/-- Tests `inext` as shorthand for imodintro on later goals. -/
example [BI PROP] (P : PROP) : ▷ P ⊢ ▷ P := by
  iintro HP
  inext
  iexact HP

/-- Tests `imodintro` for fupd then bupd. -/
example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : P ⊢ |={E}=> |==> P := by
  iintro HP
  imodintro
  imodintro
  iexact HP

/-- Tests `imodintro` with `intoEmbed_embed`. -/
example {PROP1 PROP2 : Type u} [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    (P Q : PROP1) : ⎡P⎤ ∗ ⎡P -∗ Q⎤ ⊢@{PROP2} ⎡Q⎤ := by
  iintro ⟨HP, HPQ⟩
  imodintro
  iapply HPQ $$ HP

/-- Tests `imodintro` with `intoEmbed_affinely` and `intoEmbed_embed`. -/
example {PROP1 PROP2 : Type u} [BI PROP1] [BI PROP2] [BIUpdate PROP1] [BIUpdate PROP2]
    [BiEmbed PROP1 PROP2] [BiEmbedBUpd PROP1 PROP2] (P : PROP1) :
    <affine> ⎡P⎤ ⊢@{PROP2} ⎡<affine> P⎤ := by
  iintro HP
  imodintro
  iassumption

/- Tests `imodintro` where `intoEmbed_embed` does not apply. -/
/-- error: imodintro: cannot transform hypothesis HQ: Q with ProofMode.IntoEmbed -/
#guard_msgs in
example {PROP1 PROP2 : Type u} [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    (P : PROP1) (Q : PROP2) : ⎡P⎤ ∗ Q ⊢@{PROP2} ⎡P⎤ := by
  iintro ⟨HP, HQ⟩
  imodintro

end imodintro

section imod

/-- Tests `imod` for bupd. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> P ⊢ |==> P := by
  iintro HP
  imod HP
  iexact HP

/-- Tests `imod` for fupd. -/
example [BI PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : (|={E}=> P) ⊢ |={E}=> P := by
  iintro HP
  imod HP
  imodintro
  iexact HP

/- Tests `imod` for fupd with mismatching masks failing. -/
/-- error: Goal and eliminated modality must have the same mask.
      Use `BIFUpdate.subset` to adjust the goal mask before using `imod`. -/
#guard_msgs in
example [BI PROP] [BIFUpdate PROP]
    (E0 E1 E2 E3 : CoPset) (P Q : PROP) : (|={E1,E2}=> P) ⊢ |={E0,E3}=> Q := by
  iintro HP
  imod HP

/-- Tests `imod` removing later before timeless propositions. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) [Timeless P] : ▷ P ⊢ ◇ P := by
  iintro HP
  imod HP
  iexact HP

/-- Tests `imod` for bupd under wand. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> P ⊢ emp -∗ |==> P := by
  iintro HP
  imod HP
  iintro _
  iexact HP

/-- Tests `imod` for fupd under wand. -/
example [BI PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : (|={E}=> P) ⊢ emp -∗ |={E}=> P := by
  iintro HP
  imod HP
  iintro _ !>
  iexact HP

/-- Tests `imod` with destructuring pattern. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> (P ∗ emp) ⊢ |==> P := by
  iintro HP
  imod HP with ⟨HP, _⟩
  iexact HP

/-- Tests `imod` with destructuring pattern for fupd. -/
example [BI PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : (|={E}=> P ∗ emp) ⊢ |={E}=> P := by
  iintro HP
  imod HP with ⟨HP, _⟩
  imodintro
  iexact HP

/-- Tests `icases` with mod pattern. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : emp ∗ |==> P ⊢ |==> P := by
  iintro HP
  icases HP with ⟨_, >HP⟩
  iexact HP

/-- Tests `icases` with mod pattern for fupd. -/
example [BI PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : emp ∗ (|={E}=> P) ⊢ |={E}=> P := by
  iintro HP
  icases HP with ⟨_, >HP⟩
  imodintro
  iexact HP

/- Tests `imod` for no modality. -/
/-- error: icases: P is not a modality -/
#guard_msgs in
example [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  imod HP

/-- Tests `imod` eliminating nested modalities. -/
example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> |==> P ⊢ |==> P := by
  iintro HP
  imod HP
  imod HP
  iexact HP

/-- Tests `imod` eliminating nested fupd modalities. -/
example [BI PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : (|={E}=> |={E}=> P) ⊢ |={E}=> P := by
  iintro HP
  imod HP
  imod HP
  imodintro
  iexact HP

/-- Tests `imod` for nested mask-changing fupd. -/
example [BI PROP] [BIFUpdate PROP]
    (E1 E2 E3 : CoPset) (P : PROP) : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P := by
  iintro HP
  imod HP
  iexact HP

/-- Tests `imod` with destructuring nested separating conjunction. -/
example [BI PROP] [BIFUpdate PROP]
    (E1 E2 : CoPset) (P Q R : PROP) :
    (|={E1,E2}=> P ∗ Q ∗ R) ⊢ |={E1,E2}=> (P ∗ Q ∗ R) := by
  iintro HP
  imod HP with ⟨HP, HQ, HR⟩
  imodintro
  isplitl [HP]
  · iexact HP
  isplitl [HQ]
  · iexact HQ
  · iexact HR

/-- Tests `imod` for later with timeless under except0 goal. -/
example [BI PROP] (P Q : PROP) [Timeless P] : ▷ P ∗ Q ⊢ ◇ (P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  imod HP
  isplitl [HP]
  · iexact HP
  · iexact HQ

/-- Tests `imod` for fupd with intuitionistic hypothesis. -/
example [BI PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : □ (|={E}=> P) ⊢ |={E}=> P := by
  iintro #HP
  imod HP
  imodintro
  iexact HP

/-- Tests `imod` without with but with proof mode term. -/
example [BI PROP] [BIUpdate PROP]
    (P : PROP) : (True -∗ |==> P) ⊢ |==> P := by
  iintro HP
  imod HP $$ [//]
  imodintro
  iexact HP

/-- Tests `imod` without with and without ident. -/
example [BI PROP] [BIUpdate PROP]
    (P : Nat → PROP) (h : ∀ x, ⊢ |==> P x) :
    ⊢ |==> P 0 := by
  imod h 0
  imodintro
  iassumption

end imod

section inext

/- Tests `inext` failing on non-later goal. -/
set_option pp.mvars false in
/-- error: imodintro: P is not a modality matching iprop(▷^[?_] ?_) -/
#guard_msgs in
example [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  inext

/-- Tests `inext`. -/
example [BI PROP] (P Q : PROP) : ⊢ ▷ P -∗ Q -∗ ▷ (P ∗ Q) := by
  iintro HP HQ
  inext
  icombine HP HQ as HPQ
  iassumption

/-- Tests `inext` where the outermost `▷?p` in `H` and `▷` in the goal are both stripped. -/
example [BI PROP] (p : Bool) (P : PROP) : ▷?p P -∗ ▷ P := by
  iintro H
  inext
  iassumption

/-- Tests `inext` with the handling of `▷?p` and other modalities. -/
example [BI PROP] (p : Bool) (P Q : PROP) :
    ⊢ □ ▷ P -∗ □ ▷?p ▷ Q -∗ ▷?p ▷ □ (P ∗ Q) := by
  iintro #HP #HQ
  inext; inext
  imodintro
  icombine HP HQ as HPQ
  iexact HPQ

/-- Tests `inext` where the two `▷` are stripped, retaining the two `▷?p`. -/
example [BI PROP] (p : Bool) (P : PROP) (h : ▷?p P -∗ ▷?p P) : ▷?p ▷ P -∗ ▷▷?p P := by
  iintro H
  inext
  iapply h $$ H

/--
  Tests `inext` where synthesis using `intoLaterN_sep_left` fails and
  uses `intoLaterN_sep_right` after backtracking.
  The later modality in `▷ Q` is stripped from `HPQ1` instead of the outermost `▷?p`.
  Analogous for `∧` and `∨`.
-/
example [BI PROP] (p : Bool) (P Q R : PROP)
    (h : ▷?p (P ∗ Q) -∗ ▷?p (P ∧ Q) -∗ ▷?p (P ∨ Q) -∗ ▷ R) :
    ▷?p (▷ P ∗ ▷ Q) ∗ ▷?p (▷ P ∧ ▷ Q) ∗ ▷?p (▷ P ∨ ▷ Q) ⊢ ▷▷ R := by
  iintro ⟨HPQ1, HPQ2, HPQ3⟩
  inext
  iapply h $$ HPQ1 HPQ2 HPQ3

variable {GF : BundledGFunctors} [InvGS GF]

/- Tests `inext` with later credits consumption. -/
example (E : CoPset) (P : IProp GF) : ⊢ £ 1 -∗ ▷ (|={E}=> P) -∗ |={E}=> P := by
  iintro Hcred HP
  -- No later credits consumed, equivalent to a no-op
  inext 0 credit: Hcred
  -- One later credit is consumed by default when the amount is not specified
  inext credit: Hcred
  iassumption

/- Tests `inext` with insufficient credits. -/
/-- error: inext: insufficient credits -/
#guard_msgs in
example (E : CoPset) (P : IProp GF) : ⊢ £ 1 -∗ ▷ (|={E}=> P) -∗ |={E}=> P := by
  iintro Hcred HP
  inext 2 credit: Hcred

/- Tests `inext` with multiple credits consumed. -/
example (E : CoPset) (P : IProp GF) :
    ⊢ £ (m + n + 6) -∗ ▷^[m + n + 6] (|={E}=> P) -∗ |={E}=> P := by
  iintro Hcred HP
  inext 3 credit: Hcred
  inext (1 + (3 - .succ 1)) credit: Hcred
  inext 1 credit: Hcred
  inext n credit: Hcred
  inext m credit: Hcred
  iassumption

/- Tests `inext` for later credits with later modalities expressed in terms of `Nat` variables. -/
example (m n p q : Nat) (E : CoPset) (P : IProp GF) :
    ⊢ £ (1 + m + n + p + q + 3) -∗ ▷^[n + m + 4 + p + q] (|={E}=> P) -∗ |={E}=> P := by
  iintro Hcred HP
  inext (m + q) credit: Hcred
  inext (p + n) credit: Hcred
  inext 4 credit: Hcred
  iassumption

/- Tests `inext` where `intoLaterN_later` should not apply and `intoLaterN_laterN_bool` applies instead -/
example (p : Bool) (P : IProp GF) (E : CoPset) :
    ⊢ £ 1 -∗ ▷?p P -∗ ▷ (|={E}=> P) -∗ |={E}=> (P ∗ P) := by
  iintro Hcred H HQ
  inext credit: Hcred
  isplitl [HQ] <;> iassumption

/- Tests `inext` for later credits with an invalid hypothesis choice. -/
/-- error: inext: Hcred is not a spatial later credit hypothesis -/
#guard_msgs in
example (E : CoPset) (P Q : IProp GF) : ⊢ Q -∗ ▷ (|={E}=> P) -∗ |={E}=> P := by
  iintro Hcred HP
  inext credit: Hcred

/- Tests `inext` for later credits with the hypothesis not in the spatial context. -/
/-- error: inext: Hcred is not in the spatial context -/
#guard_msgs in
example (E : CoPset) (P : IProp GF) : ⊢ □ £ 1 -∗ ▷ (|={E}=> P) -∗ |={E}=> P := by
  iintro #Hcred HP
  inext credit: Hcred

/- Tests `inext` with an `IProp GF` entailment where `InvGS GF` is not available. -/
/-- error: inext: requires an InvGS (HasLC) context -/
#guard_msgs in
example [InvGS_gen .hasNoLC GF] (E : CoPset) (P : IProp GF) :
    ⊢ £ 1 -∗ ▷ (|={E}=> P) -∗ |={E}=> P := by
  iintro Hcred HP
  inext credit: Hcred

variable {Expr State Obs Val} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [IrisGS_gen .hasLC Expr GF]
variable {E : CoPset} {e : Expr} {Φ : Val → IProp GF}

/- Tests `inext` for later credits with `WP`. -/
example : £ 1 ∗ ▷ WP e @ E {{ Φ }} ⊢ WP e @ E {{ Φ }} := by
  iintro ⟨Hcred, Hwp⟩
  inext credit: Hcred
  iassumption

end inext

section irewrite

variable {PROP : Type _} [Sbi PROP]
variable {A B : Type _} [OFE A] [OFE B]

/- Tests `irewrite` rewriting in goal. -/
example (a b : A) (P : A → PROP) [OFE.NonExpansive P] [Absorbing (P a)] :
    b ≡ a ∗ P a ⊢ P b := by
  iintro ⟨Heq, Ha⟩
  irewrite [Heq]
  iexact Ha

/- Tests `irewrite` rewriting in goal explicitly. -/
example (a b : A) (P : A → PROP) [OFE.NonExpansive P] [Absorbing (P a)] :
    b ≡ a ∗ P a ⊢ P b := by
  iintro ⟨Heq, Ha⟩
  irewrite [Heq] at ⊢
  iexact Ha

/- Tests `irewrite` rewriting in goal in backward direction. -/
example (a b : A) (P : A → PROP) [OFE.NonExpansive P] [Absorbing (P b)] :
    b ≡ a ∗ P b ⊢ P a := by
  iintro ⟨Heq, Hb⟩
  irewrite [← Heq]
  iexact Hb

/- Tests `irewrite` rewriting in hypothesis. -/
example (a b : A) (P Q R : A → PROP)
    [OFE.NonExpansive P] [OFE.NonExpansive Q] [OFE.NonExpansive R] [Absorbing iprop(P b ∗ Q b ∗ R b)] :
    a ≡ b ∗ (P a ∗ Q a ∗ R a) ⊢ P b ∗ Q b ∗ R b := by
  iintro ⟨Heq, H⟩
  irewrite [Heq] at H
  · refine ⟨fun _ _ _ h => ?_⟩
    refine sep_ne.ne (OFE.NonExpansive.ne h) ?_
    refine sep_ne.ne (OFE.NonExpansive.ne h) ?_
    exact (OFE.NonExpansive.ne h)
  · iexact H

/- Tests `irewrite` rewriting in same hypothesis. -/
example (a b : A) (P : A → PROP) [OFE.NonExpansive P] [Absorbing (P b)] :
    b ≡ a ⊢@{PROP} a ≡ a := by
  iintro Heq
  irewrite [Heq] at Heq
  · apply internalEq.ne_l
  iexact Heq

/- Tests `irewrite` with proof mode terms. -/
example (a b : A) (P Q : A → PROP) [OFE.NonExpansive P] [OFE.NonExpansive Q] [Absorbing (P a)] :
    (∀ c, a ≡ c) ∗ P a ∗ (P b -∗ Q b) ⊢ Q b := by
  iintro ⟨Heq, Ha, Himpl⟩
  iapply Himpl
  irewrite [← Heq $$ %b, ← Heq $$ %a]
  iexact Ha

/- Tests `irewrite` with multiple rewrites. -/
example (a b c : A) (P : A → PROP) [OFE.NonExpansive P] [Absorbing (P a)] :
    a ≡ b ∗ b ≡ c ∗ P a ⊢ P c := by
  iintro ⟨Hab, Hbc, Ha⟩
  irewrite [←Hbc, ←Hab]
  iexact Ha

/- Tests `irewrite` with manual nonexpansive proof. -/
example (f : A → B) [OFE.NonExpansive f] (a b : A) (P : B → PROP) [OFE.NonExpansive P] [Absorbing (P (f a))] :
    a ≡ b ∗ P (f a) ⊢ P (f b) := by
  iintro ⟨Heq, Ha⟩
  irewrite [←Heq]
  · exact (OFE.NonExpansive.comp (g := P) (f := f) inferInstance inferInstance)
  · iexact Ha

/- Tests `irewrite` under separating conjunction. -/
example (a b : A) (P Q R : A → PROP)
    [OFE.NonExpansive P] [OFE.NonExpansive Q] [OFE.NonExpansive R] [Absorbing (P a)] :
    a ≡ b ∗ (P a ∗ Q a ∗ R a) ⊢ P b ∗ Q b ∗ R b := by
  iintro ⟨Heq, H⟩
  irewrite [←Heq]
  · refine ⟨fun _ _ _ h => ?_⟩
    refine sep_ne.ne (OFE.NonExpansive.ne h) ?_
    refine sep_ne.ne (OFE.NonExpansive.ne h) ?_
    exact (OFE.NonExpansive.ne h)
  · iexact H

/- Tests `irewrite` under more connectives. -/
example (x y : A) P :
    ⊢@{PROP} □ (∀ z, P -∗ <affine> (z ≡ y)) -∗ (P -∗ P ∧ ((x, x) ≡ (y, x))) := by
  iintro #H1 H2
  irewrite [H1 $$ %x H2]
  · refine ⟨fun _ _ _ h => and_ne.ne .rfl ?_⟩
    refine OFE.Dist.trans ?_ ((internalEq.ne_r ⟨_, _⟩).ne (OFE.dist_prod_ext .rfl h))
    exact (internalEq.ne_l _).ne (OFE.dist_prod_ext h h)
  · isplit
    · iexact H2
    · apply internalEq.refl

/- Tests `irewrite` with Later.next. -/
example (f : A -n> A) x y :
    ⊢@{PROP} (Later.next x ≡ Later.next y) -∗ (Later.next (f x) ≡ Later.next (f y)) := by
  iintro H
  -- FIXME: inext
  iapply later_equivI_mpr
  icases later_equivI_mp $$ H with H
  inext
  irewrite [H]
  · exact ⟨fun _ _ _ h => (internalEq.ne_l _).ne (f.ne.ne h)⟩
  · apply internalEq.refl

/- Tests `irewrite` under affine and later. -/
example (P Q : PROP) :
    <affine> ▷ (Q ≡ P) -∗ <affine> ▷ Q -∗ <affine> ▷ P := by
  iintro #HPQ HQ !>
  inext
  irewrite [HPQ] at HQ
  · exact ⟨fun _ _ _ h => affinely_ne.ne h⟩
  · iexact HQ

/- Tests `irewrite` under affine and later backwards. -/
example (P Q : PROP) :
    <affine> ▷ (Q ≡ P) -∗ <affine> ▷ P -∗ <affine> ▷ Q := by
  iintro #HPQ HQ !>
  inext
  irewrite [←HPQ] at HQ
  · exact ⟨fun _ _ _ h => affinely_ne.ne h⟩
  · iexact HQ

/- Tests `irewrite` with no matching target. -/
/--
error: irewrite: Could not find ⏎
  P
in the target expression
  Q
-/
#guard_msgs in
example (P Q : PROP) :
    P ≡ Q -∗ Q := by
  iintro HPQ
  irewrite [HPQ]

end irewrite

section iframe

/- Tests basic `iframe`. -/
example [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  iframe HP

/- Tests `iframe` not closing goal with non-affine assumption. -/
/-- trace:
PROP : Type u_1
inst✝ : BI PROP
P Q : PROP
⊢ ⏎
  ∗HQ : Q
  ⊢ emp
-/
#guard_msgs (trace, drop error) in
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ P := by
  iintro ⟨HP, HQ⟩
  iframe HP
  trace_state

/- Tests `iframe` closing goal with absorbing goal. -/
example [BI PROP] (P Q : PROP) : <absorb> P ∗ Q ⊢ <absorb> P := by
  iintro ⟨HP, HQ⟩
  iframe HP

/- Tests `iframe` with pure hyp. -/
example [BI PROP] (Q : PROP) :
  1 = 1 →
  Q ⊢ ⌜1 = 1⌝ := by
  iintro %heq HQ
  iframe %heq

/- Tests `iframe` error with pure hyp mismatch. -/
/-- error: iframe: cannot frame ⌜1 = 2⌝ -/
#guard_msgs in
example [BI PROP] (Q : PROP) :
  1 = 2 →
  Q ⊢ ⌜1 = 1⌝ := by
  iintro %heq HQ
  iframe %heq

/- Tests `iframe` error with non-prop. -/
/-- error: iframe: Q is not a Prop -/
#guard_msgs in
example [BI PROP] (Q : PROP) :
  Q ⊢ ⌜1 = 1⌝ := by
  iintro HQ
  iframe %Q

/- Tests `iframe` under star. -/
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ P ∗ Q := by
  iintro ⟨HP, HQ⟩
  iframe HP HQ

/- Tests `iframe` under nested star. -/
example [BI PROP] (P Q : PROP) : P ∗ Q ∗ Q ⊢ (P ∗ Q) ∗ Q := by
  iintro ⟨HP, HQ1, HQ2⟩
  iframe HP
  iframe HQ1 HQ2

/- Tests `iframe` without explicit patterns. -/
example [BI PROP] (P Q : PROP) : P ∗ Q ∗ Q ⊢ (P ∗ Q) ∗ Q := by
  iintro ⟨HP, HQ1, HQ2⟩
  iframe

/- Tests `iframe` with persistent hyp cancelling multiple times. -/
example [BI PROP] (P Q : PROP) : P ∗ □ Q ⊢ (P ∗ Q) ∗ Q := by
  iintro ⟨HP, #HQ1⟩
  iframe HQ1
  iframe

/- Tests `iframe` under and. -/
example [BI PROP] (P : PROP) : P ⊢ (P ∧ P) := by
  iintro HP
  iframe HP

/- Tests `iframe` under and. -/
example [BI PROP] (P Q : PROP) [BIAffine PROP] : P ∗ Q ⊢ (P ∧ Q) := by
  iintro ⟨HP, HQ⟩
  iframe HP
  iframe HQ

/- Tests `iframe` under and for non-affine P failing. -/
/-- error: iframe: cannot frame P -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ (P ∧ Q) := by
  iintro ⟨HP, HQ⟩
  iframe HP

/- Tests `iframe` under and for intuitionistic hyp. -/
example [BI PROP] (P Q : PROP) [Affine Q] : □ P ∗ Q ⊢ (P ∧ Q) := by
  iintro ⟨#HP, HQ⟩
  iframe HP
  iframe HQ

/- Tests `iframe` under or. -/
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ (P ∗ Q ∨ P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  iframe HP
  iframe HQ

/- Tests `iframe` under or only left fails. -/
/-- error: iframe: cannot frame P -/
#guard_msgs in
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ (P ∗ Q ∨ Q) := by
  iintro ⟨HP, HQ⟩
  iframe HP

/- Tests `iframe` under or only left works if persistent. -/
example [BI PROP] (P Q : PROP) : □ P ∗ Q ⊢ (P ∗ Q ∨ Q) := by
  iintro ⟨#HP, HQ⟩
  iframe HP
  iframe HQ

/- Tests `iframe` under or solve left. -/
example [BI PROP] (P Q : PROP) [BIAffine PROP] : P ∗ Q ⊢ (P ∨ Q) := by
  iintro ⟨HP, HQ⟩
  iframe HP

/- Tests `iframe` under or solve right. -/
example [BI PROP] (P Q : PROP) [BIAffine PROP] : P ∗ Q ⊢ (Q ∨ P) := by
  iintro ⟨HP, HQ⟩
  iframe HP

/- Tests `iframe` under modalities. -/
example [BI PROP] (P : PROP) : □ P ⊢ <pers> <affine> <absorb> □ P := by
  iintro #HP
  iframe HP

/- Tests `iframe` under more modalities. -/
example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] (P : PROP) [BIAffine PROP] E :
  P ⊢ ▷ |==> |={E}=> P := by
  iintro HP
  iframe HP

/- Tests `iframe` under magic wand. -/
example [BI PROP] (P Q : PROP) : P ⊢ Q -∗ P ∗ Q := by
  iintro HP
  iframe HP
  iintro HQ
  iframe HQ

/- Tests `iframe` under implication. -/
example [BI PROP] (P Q : PROP) [BIAffine PROP] : P ⊢ □ Q → P ∗ Q := by
  iintro HP
  iframe HP
  iintro #HQ
  iframe HQ

/- Tests `iframe` under forall. -/
example [BI PROP] (P : PROP) : P ⊢ ∀ (x : Nat), P ∗ ⌜x = x⌝ := by
  iintro HP
  iframe HP
  itrivial

/- Tests `iframe` with mvar. -/
example [BI PROP] (P Q : PROP) : (P ∗ Q ⊢ ∃ x, P ∗ ⌜x = Q⌝ ∗ x) := by
  iintro ⟨HP, HQ⟩
  iexists _
  iframe HP
  iframe HQ
  itrivial

/- Tests `iframe` with mvar and or. -/
example [BI PROP] [BIAffine PROP] (Q : Nat → PROP) : (Q 0 ⊢ ∃ x, False ∨ Q x) := by
  iintro HQ
  iexists _
  iframe

/- Tests `iframe` with existential quantifiers. -/
example [BI PROP] {α} (a : α) {β} (b : β) (P : PROP)
    (Q : α → PROP) (R : β → PROP) (S : PROP) :
    ⊢ P -∗ Q a -∗ R b -∗ S -∗ ∃ n, Q n ∗ ∃ m, R m ∗ P ∗ S := by
  iintro HP HQ HR HS
  -- Instantiate the inner existential quantifier `m`
  iframe HR
  -- Keep the outer existential quantifier `n` around
  iframe HP
  -- Instantiate the outer existential quantifier `n`
  iframe HQ
  iassumption

/- Tests `iframe` with multiple existential quantifiers framed at once. -/
example [BI PROP] {α} (a : α) {β} (b : β) (P : PROP)
    (Q : α → PROP) (R : β → PROP) (S : PROP) :
    ⊢ P -∗ Q a -∗ R b -∗ S -∗ ∃ n, Q n ∗ ∃ m, R m ∗ P ∗ S := by
  iintro HP HQ HR HS
  iframe HS HP HR HQ

/- Tests `iframe` with multiple existential quantifiers framed at once. -/
/-- trace:
PROP : Type u_1
inst✝ : BI PROP
α : Sort u_2
P : PROP
Q : α → PROP
⊢ ⏎
  ⊢ @«exists» PROP (@toBIBase PROP inst✝) α fun {n} => Q n
-/
#guard_msgs (trace, drop error) in
set_option pp.explicit true in
example [BI PROP] {α} (P : PROP) (Q : α → PROP) :
    ⊢ P -∗ BI.exists fun {n} => iprop(Q n ∗ P) := by
  iintro HP
  iframe HP
  trace_state

/- Tests `iframe` with existential quantifers in various orders. -/
example [BI PROP] {α} (a : α) {β} (b : β) {γ} (c : γ)
    (P : α → β → PROP) (Q : β → α → γ → PROP) :
    ⊢ P a b -∗ Q b a c -∗ ∃ x, ∃ y, (P x y ∗ ∃ z, Q y x z) := by
  iintro HP HQ
  iframe

/-
  Tests `iframe` with the framing of existential quantifiers disabled.
  The tactic should succeed as `P`, which is under the existential
  quantifier, can still be framed.
-/
set_option iris.frame.instantiateExists false in
example [BI PROP] {α} (a : α) (P : PROP) (Q R : α → PROP) (S : PROP) :
    ⊢ P -∗ Q a -∗ R a -∗ S -∗ ∃ n, P ∗ Q n ∗ ∃ m, R m ∗ S := by
  iintro HP HQ HR HS
  iframe ∗
  iexists a
  iframe HQ
  iexists a
  iassumption

/-
  Tests `iframe` with the framing of existential quantifiers disabled.
  Since nothing else can be framed, the tactic should fail.
-/
/-- error: iframe: cannot frame P a -/
#guard_msgs in
set_option iris.frame.instantiateExists false in
example [BI PROP] {α} (a : α) (P : α → PROP) :
    ⊢ P a -∗ ∃ n, P n := by
  iintro HP
  iframe HP

/- Tests `iframe` with an existential quantifier under a universal quantifier. -/
example [BI PROP] (P : PROP) : P ⊢ ∀ (x : Nat), ∃ n, ⌜n = x⌝ ∗ P := by
  iintro HP
  iframe HP
  iintro %x
  iexists x
  ipureintro; rfl

/- Tests `iframe` with an existentially quantified binder instantiated with a metavariable. -/
example [BI PROP] (P Q : Nat → PROP) (m : Nat) :
    ⊢ P m -∗ ∃ n, Q n -∗ ∃ x y, P x ∗ Q y ∗ ⌜y = 3⌝ := by
  iintro HP
  iexists ?w
  iintro HQ
  -- The existentially quantified binder `y` instantiated with `?w`
  iframe HQ
  iframe HP
  ipureintro
  rfl

/-
  Tests `iframe` with an existentially quantified binder instantiated with
  a value that involves a metavariable.
-/
example [BI PROP] (P : Option Nat → PROP) :
    ⊢ (∀ n, P (some n)) -∗ ∃ x, P x := by
  iintro HP
  ispecialize HP $$ %(?n)
  -- The existentially quantified binder `x` instantiated with `some ?n`
  iframe HP
  exact 0

variable {hlc : outParam HasLC} {Expr State Obs Val} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {e : Expr} {v : Val} {Φ : Val → IProp GF}

/- Tests `iframe` with the `Frame` type class instance `frameWp`. -/
example [inst : Language.IntoVal e v] (P : IProp GF) :
    P ∗ Φ v ⊢ WP e @ s ; E {{ w, P ∗ Φ w }} := by
  iintro ⟨HP, HΦ⟩
  iframe HP
  iapply wp_value $$ HΦ
  exact inst

end iframe

section icombine
open ProofMode

/-- Tests `icombine` for combining propositions with the separating conjunction,
    where the combined proposition is introduced into the spatial context. -/
example [BI PROP] {P1 P2 Q : PROP} :
    ⊢ <absorb> P1 -∗ <absorb> P2 -∗ <absorb> <affine> P3 -∗ <absorb> <affine> P4 -∗
      (<absorb> (P1 ∗ P2 ∗ <affine> (P3 ∗ P4)) -∗ Q) -∗ Q := by
  iintro HP1 HP2 HP3 HP4 H
  icombine HP1 HP2 HP3 HP4 as HNew
  iapply H
  iexact HNew

/-- Tests `icombine` with zero/one hypothesis argument(s). -/
example [BI PROP] {P : PROP} : ⊢ P -∗ P ∗ emp ∗ True ∗ True := by
  iintro HP
  -- Tests `icombine … as …` with no arguments: introduces `emp`
  icombine as H1
  -- Tests `icombine … gives …` with no arguments: introduces `True`
  icombine gives H2
  -- Tests `icombine … gives …` with one argument: introduces `True`
  icombine HP gives H3
  -- Tests `icombine … as …` with one argument: renames the hypothesis
  icombine HP as HNew
  isplitl
  · iexact HNew
  · isplitl
    · iexact H1
    · isplitl
      · iexact H2
      · iexact H3

/-- Tests `icombine` for the proposition with three propositions with `□`. -/
example [BI PROP] {P1 P2 P3 Q : PROP} :
    ⊢ □ P1 -∗ □ P2 -∗ □ P3 -∗ (□ (P1 ∗ P2 ∗ P3) -∗ Q) -∗ Q := by
  iintro HP1 HP2 HP3 H
  icombine HP1 HP2 HP3 as HNew
  iapply H
  iexact HNew

/-- Tests `icombine` for the proposition with three propositions, where the
    first two propositions have `□`. Note that `□ P2` and `P3` first get
    combined into `P2 ∗ P3`, which is then combined with `□ P1` to get
    `□ P1 ∗ □ P2 ∗ P3`. -/
example [BI PROP] {P1 P2 P3 Q : PROP} :
    ⊢ □ P1 -∗ □ P2 -∗ P3 -∗ (□ P1 ∗ □ P2 ∗ P3 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HP3 H
  icombine HP1 HP2 HP3 as HNew
  iapply H
  iexact HNew

/-- Tests `icombine` for the proposition with three propositions,
    where the last two propositions have `□`. Note that `□ P2` and `□ P3`
    are first combined into `□ (P2 ∗ P3)`, which is then combined with
    `P1` to get `P1 ∗ □ (P2 ∗ P3)`. -/
example [BI PROP] {P1 P2 P3 Q : PROP} :
    ⊢ P1 -∗ □ P2 -∗ □ P3 -∗ (P1 ∗ □ (P2 ∗ P3) -∗ Q) -∗ Q := by
  iintro HP1 HP2 HP3 H
  icombine HP1 HP2 HP3 as HNew
  iapply H
  iexact HNew

/- Tests `icombine` failure: using a non-existent hypothesis as an argument. -/
/-- error: unknown hypothesis HP2 -/
#guard_msgs in
example [BI PROP] {P : PROP} : ⊢ P -∗ P ∗ P := by
  iintro HP1
  icombine HP1 HP2 as HNew

/- Tests `icombine` failure: combining a proposition in the spatial context twice. -/
/-- error: icombine: propositions in the spatial context cannot be used as arguments multiple times -/
#guard_msgs in
example [BI PROP] {P Q R : PROP} : ⊢ P -∗ Q -∗ R -∗ P ∗ Q ∗ R ∗ P := by
  iintro HP HQ HR
  icombine HP HQ HR HP as HNew

/-- Tests `icombine` for combining propositions in the intuitionistic context.
    The combined proposition stays within the intuitionistic context. -/
example [BI PROP] {P Q R : PROP} : ⊢ □ P -∗ □ Q -∗ □ R -∗ □ (P ∗ Q ∗ R) := by
  iintro #HP #HQ #HR
  -- The proposition P ∗ Q ∗ R exists in the intuitionistic context
  icombine HP HQ HR as HNew
  iexact HNew

/-- Tests `icombine` for using a proposition in the intuitionistic context
    multiple times, where the combined proposition remains in the
    intuitionistic context. -/
example [BI PROP] {P : PROP} : ⊢ □ P -∗ □ (P ∗ P ∗ P) := by
  iintro #HP
  -- The proposition P ∗ P ∗ P exists in the intuitionistic context
  icombine HP HP HP as HNew
  iexact HNew

/-- Tests `icombine` for using a proposition in the intuitionistic context
    multiple times, where the combined proposition is introduced into the
    the spatial context. -/
example [BI PROP] {P Q R : PROP} : ⊢ P -∗ Q -∗ □ R -∗ R ∗ Q ∗ P ∗ R := by
  iintro HP HQ #HR
  -- The proposition R ∗ Q ∗ P ∗ R exists in the spatial context
  icombine HR HQ HP HR as HNew
  iexact HNew

/-- Tests `icombine` with `gives` and two hypotheses (with a selection pattern)
    that can be combined using the type class `CombineSepGives`. -/
example [BI PROP] {P Q R : PROP} [CombineSepGives P Q R] :
    ⊢ <absorb> <affine> P -∗ <absorb> <affine> Q -∗ <pers> R := by
  iintro HP HQ
  icombine ∗ gives HNew
  iexact HNew

/-- Tests `icombine` with `gives` using three propositions. -/
example [BI PROP] [BIAffine PROP] {P1 P2 P3 P4 P5 P6 : PROP}
    [CombineSepAs P2 P3 P4] [CombineSepGives P2 P3 P5] [CombineSepGives P1 P4 P6] :
    ⊢ P1 -∗ P2 -∗ P3 -∗ □ (P5 ∧ P6) := by
  iintro HP1 HP2 HP3
  icombine HP1 HP2 HP3 gives Hnew
  iexact Hnew

/- Tests `icombine` with `gives` using three propositions, with type class
    instance synthesis possible only in the first step. -/
/-- error: icombine: no type class instance to combine propositions -/
#guard_msgs in
example [BI PROP] [BIAffine PROP] {P1 P2 P3 P4 P5 P6 : PROP}
    [CombineSepAs P2 P3 P4] [CombineSepGives P2 P3 P5] :
    ⊢ P1 -∗ P2 -∗ P3 -∗ □ (P5 ∧ P6) := by
  iintro HP1 HP2 HP3
  -- Combining `HP2 : P2` and `HP3 : P3` gives `Hnew : P5`
  icombine HP2 HP3 gives Hnew
  -- The entire tactic below fails as `HP1 : P1` cannot be combined with `P5`
  icombine HP1 HP2 HP3 gives Hnew
  iexact Hnew

/-- Tests `icombine` with `as` and `gives` using propositions with `<absorb>` and `<affine>` modalities. -/
example [BI PROP] {P Q R : PROP} [CombineSepGives P Q R] :
    ⊢ <absorb> <affine> P -∗ <absorb> <affine> Q -∗ <absorb> <affine> (P ∗ Q) ∗ <pers> R := by
  iintro HP HQ
  icombine HP HQ as HNew1 gives HNew2
  isplitl
  · iexact HNew1
  · iexact HNew2

/-- Tests `icombine` with `as` and `gives` for propositions with later modalities. -/
example [BI PROP] {n : Nat} {P Q R : PROP} [CombineSepGives P Q R] :
    ⊢ ▷^[n] ◇ P -∗ ▷^[n] ◇ Q -∗ ▷^[n] ◇ (P ∗ Q) ∗ <pers> ▷^[n] ◇ R := by
  iintro HP HQ
  icombine HP HQ as HNew1 gives HNew2
  isplitl
  · iexact HNew1
  · iexact HNew2

/-- Tests `icombine` with `as` and `gives` using three propositions and destruction patterns. -/
example [BI PROP] {P1 P2 P3 P4 P5 P6 : PROP}
    [CombineSepAs P2 P3 P4] [CombineSepGives P2 P3 P5] [CombineSepGives P1 P4 P6] :
    ⊢ P1 -∗ P2 -∗ P3 -∗ P1 ∗ P4 ∗ □ P5 ∗ □ P6 := by
  iintro HP1 HP2 HP3
  icombine HP1 HP2 HP3 as ⟨HP1, HP4⟩ gives ⟨HP5, HP6⟩
  isplitl [HP1]
  · iexact HP1
  · isplitl [HP4]
    · iexact HP4
    · isplitl
      · iexact HP5
      · iexact HP6

/- Tests `icombine` with an invalid selection pattern. -/
/-- error: unknown local declaration `a` -/
#guard_msgs in
example [BI PROP] {P Q R : PROP} : ⊢ P -∗ Q -∗ □ R -∗ R ∗ P ∗ Q := by
  iintro HP HQ #HR
  icombine %a as HNew1

/-- Tests `icombine` for combining propositions involving `iOwn`, where
    `a2` and `a3` can be combined as `b` instead of `a2 • a3` as
    the former takes higher precedence. Likewise, `a1` and `b` is merged
    as `c` instead of `a1 • b`. -/
example {F GF} [RFunctorContractive F] [ElemG GF F] {γ}
    {a1 a2 a3 b c : F.ap (IProp GF)} [IsOp .merge b a2 a3] [IsOp .merge c a1 b] :
    ⊢ iOwn γ a1 -∗ iOwn γ a2 -∗ iOwn γ a3 -∗
      iOwn γ c ∗ ✓ (a2 • a3) ∗ ✓ (a1 • b) := by
  iintro H1 H2 H3
  icombine H1 H2 H3 as Hnew1 gives ⟨Hnew2, Hnew3⟩
  isplitl
  · iexact Hnew1
  · isplit
    · iexact Hnew2  -- `IsOp` is irrelevant to the `gives` syntax
    · iexact Hnew3

/-- Tests `icombine` for combining propositions involving `iOwn` and `IsOp`
    instances for `DFrac` and `Frac`. -/
example {GF} [ElemG GF (constOF DFrac)]
    [ElemG GF (constOF Qp)] {γ}
    {a1 a2 a3 b c : Qp} [IsOp .merge b a2 a3] [IsOp .merge c a1 b] :
    ⊢@{IProp GF}
      iOwn (F := constOF DFrac) γ (own a1) -∗
      iOwn (F := constOF DFrac) γ (own a2) -∗
      iOwn (F := constOF DFrac) γ (own a3) -∗
      iOwn (F := constOF Qp) γ a1 -∗
      iOwn (F := constOF Qp) γ a2 -∗
      iOwn (F := constOF Qp) γ a3 -∗
      iOwn (F := constOF DFrac) γ (own c) ∗ iOwn (F := constOF Qp) γ c := by
  iintro H1 H2 H3 H4 H5 H6
  icombine H1 H2 H3 as Hnew1
  icombine H4 H5 H6 as Hnew2
  isplitl [Hnew1]
  · iexact Hnew1
  · iexact Hnew2

/-- Tests `icombine` for combining propositions involving `iOwn` and `IsOp`
    instances for the authoritative CMRA. -/
example {GF A} [UCMRA A] [ElemG GF (constOF (Auth A))] {γ}
    {a1 a2 a3 b c : A} {q1 q2 : Qp} {dq'' dq3 dq4 : DFrac}
    [IsOp .merge b a2 a3] [IsOp .merge c a1 b]
    [IsOp .merge dq'' dq3 dq4] :
    ⊢@{IProp GF}
      iOwn (F := constOF (Auth A)) γ (◯ a1) -∗
      iOwn (F := constOF (Auth A)) γ (◯ a2) -∗
      iOwn (F := constOF (Auth A)) γ (◯ a3) -∗
      iOwn (F := constOF (Auth A)) γ (●{own q1} a1) -∗
      iOwn (F := constOF (Auth A)) γ (●{own q2} a1) -∗
      iOwn (F := constOF (Auth A)) γ (●{dq3} a1) -∗
      iOwn (F := constOF (Auth A)) γ (●{dq4} a1) -∗
      iOwn (F := constOF (Auth A)) γ ((◯ c) • ●{(own $ q1 + q2) • dq''} a1) := by
  iintro H1 H2 H3 H4 H5 H6 H7
  icombine H1 H2 H3 as HNew1
  icombine H4 H5 as HNew2
  icombine H6 H7 as HNew3
  icombine HNew1 HNew2 HNew3 as HNew
  iexact HNew

/-- Tests `icombine` with the `IsOp` instances stipulating the
    merging of `a1`, `a2` and `a3` using `+` instead of `•`, as well as
    to eliminate splits (`IsHalfFraction`). -/
example {GF}
    [ElemG GF (constOF Qp)] {γ} {a1 a2 a3 : Qp} :
    ⊢@{IProp GF}
      iOwn (F := constOF Qp) γ a1 -∗
      iOwn (F := constOF Qp) γ a2 -∗
      iOwn (F := constOF Qp) γ (a3.half) -∗
      iOwn (F := constOF Qp) γ (a3.half) -∗
      iOwn (F := constOF Qp) γ (a1.half + (a1.half + (a2 + a3))) := by
  iintro H1 H2 H3a H3b
  icases H1 with ⟨H1a, H1b⟩
  icombine H1a H1b H2 H3a H3b as Hnew
  iexact Hnew

/-- Tests `icombine` for combining propositions involving later credits. -/
example {GF m n} [LcGS .hasLC GF] :
    ⊢@{IProp GF} £ n -∗ £ 1 -∗ £ m -∗ £ 1 -∗ £ n + (1 + (m + 1)) := by
  iintro H1 H2 H3 H4
  icombine H1 H2 H3 H4 as Hnew
  iexact Hnew

/-- Tests `icombine` for combining two tokens. -/
example {GF} [TokenG GF] {γ} :
    ⊢@{IProp GF} token γ -∗ token γ -∗ False := by
  iintro H1 H2
  icombine H1 H2 gives H
  iexact H

/- Tests `icombine` with an invalid destruction pattern. -/
/-- error: icombine: cannot destruct iprop(<absorb> <affine> (P ∗ Q)) -/
#guard_msgs in
example [BI PROP] {P Q R : PROP} [CombineSepGives P Q R] :
    ⊢ <absorb> <affine> P -∗ <absorb> <affine> Q -∗ <absorb> <affine> (P ∗ Q) ∗ <pers> R := by
  iintro HP HQ
  icombine HP HQ as ⟨HNew1, _⟩ gives HNew2

end icombine

section iloeb

variable {PROP : Type u} [ι₁ : BI PROP] [ι₂ : BILoeb PROP]

/- Tests `iloeb` basic. -/
/-- trace:
PROP : Type u
ι₁ : BI PROP
ι₂ : BILoeb PROP
P Q : PROP
⊢ ⏎
  □IH : ▷ (P -∗ Q)
  ⊢ P -∗ Q
-/
#guard_msgs (trace, drop error) in
example (P Q : PROP) :
    P ⊢ Q := by
  iloeb as IH
  trace_state

/- Tests `iloeb` automatically generalizing spatial context. -/
/-- trace:
PROP : Type u
ι₁ : BI PROP
ι₂ : BILoeb PROP
P Q : PROP
⊢ ⏎
  □IH : ▷ (P -∗ Q)
  ∗HP : P
  ⊢ Q
-/
#guard_msgs (trace, drop error) in
example (P Q : PROP) :
    P ⊢ Q := by
  iintro HP
  iloeb as IH
  trace_state

/- Tests `iloeb` not automatically generalizing persistent context. -/
/-- trace:
PROP : Type u
ι₁ : BI PROP
ι₂ : BILoeb PROP
P₁ P₂ Q : PROP
⊢ ⏎
  □HP1 : P₁
  □IH : ▷ (P₂ -∗ Q)
  ∗HP2 : P₂
  ⊢ Q
-/
#guard_msgs (trace, drop error) in
example (P₁ P₂ Q : PROP) :
    ⊢ □ P₁ -∗ P₂ -∗ Q := by
  iintro #HP1 HP2
  iloeb as IH
  trace_state

/- Tests reordering spatial hypothesis in `iloeb`. -/
/-- trace:
PROP : Type u
ι₁ : BI PROP
ι₂ : BILoeb PROP
P₁ P₂ P₃ Q : PROP
⊢ ⏎
  □HP1 : P₁
  □IH : ▷ (P₃ -∗ P₂ -∗ Q)
  ∗HP3 : P₃
  ∗HP2 : P₂
  ⊢ Q
-/
#guard_msgs (trace, drop error) in
example (P₁ P₂ P₃ Q : PROP) :
    ⊢ □ P₁ -∗ P₂ -∗ P₃ -∗ Q := by
  iintro #HP1 HP2 HP3
  iloeb as IH generalizing HP3
  trace_state

/- Tests `iloeb` with pure hypothesis. -/
/-- trace:
PROP : Type u
ι₁ : BI PROP
ι₂ : BILoeb PROP
H₁ : Nat → Prop
P Q : Nat → PROP
n : Nat
h1 : H₁ n
⊢ ⏎
  □IH : ▷ ∀ n, <affine> ⌜H₁ n⌝ -∗ P n -∗ Q n
  ∗p : P n
  ⊢ Q n
-/
#guard_msgs (trace, drop error) in
example (n : Nat) (H₁ : Nat → Prop) (P Q : Nat → PROP) :
    H₁ n → ⊢ P n -∗ Q n := by
  iintro %h1 p
  iloeb as IH generalizing %n %h1
  trace_state

/- Tests `iloeb` with pure hypothesis in affine logic. -/
/-- trace:
PROP : Type u
ι₁ : BI PROP
ι₂ : BILoeb PROP
i : BIAffine PROP
H₁ : Nat → Prop
P Q : Nat → PROP
n : Nat
h1 : H₁ n
⊢ ⏎
  □IH : ▷ ∀ n, ⌜H₁ n⌝ -∗ P n -∗ Q n
  ∗p : P n
  ⊢ Q n
-/
#guard_msgs (trace, drop error) in
example [i : BIAffine PROP] (n : Nat) (H₁ : Nat → Prop) (P Q : Nat → PROP) :
    H₁ n → ⊢ P n -∗ Q n := by
  iintro %h1 p
  iloeb as IH generalizing %n %h1
  trace_state

variable {PROP : Type u} [ι₁ : BI PROP] in
/- Tests `iloeb` failing without `BILoeb`. -/
/-- error: iloeb: no `BILoeb PROP` instance found -/
#guard_msgs in
example (P Q : PROP) :
    ⊢ P -∗ Q := by
  iloeb as IH

/- Tests `iloeb` where the `generalizing` clause has dependency. -/
/--
info: Try this:
  [apply] iloeb as IH generalizing %n %h1 %U HT
---
info: Try this:
  [apply] iloeb as IH generalizing! %n
---
error: iloeb: The following hypotheses depend on variables in the `generalizing` clause but are not themselves included:
• Lean hypothesis `h1` depends on `n`
• Lean hypothesis `U` depends on `n`
• Iris hypothesis `HT` depends on `n`
-/
#guard_msgs in
example {n : Nat} {P T : Nat → PROP} {Q : Nat → Prop} {h1 : Q n} {U : (Q n) → Prop} :
    ⊢ □ T n -∗ □ P n := by
  iintro #HT
  iloeb as IH generalizing %n

/- Same test as above, involving inaccessible names. -/
/--
info: Try this:
  [apply] iloeb as IH generalizing! %n
---
error: iloeb: The following hypotheses depend on variables in the `generalizing` clause but are not themselves included:
• Lean hypothesis `h1` depends on `n`
• Lean hypothesis `x` (inaccessible name) depends on `n`
• Iris hypothesis `x` (inaccessible name) depends on `n`
-/
#guard_msgs in
example {n : Nat} {P T : Nat → PROP} {Q : Nat → Prop} {h1 : Q n} {_ : (Q n) → Prop} :
    ⊢ □ T n -∗ □ P n := by
  iintro #_
  iloeb as IH generalizing %n

/- Same test as above, except `generalizing!` is used. -/
/-- trace:
PROP : Type u
ι₁ : BI PROP
ι₂ : BILoeb PROP
P T : Nat → PROP
Q : Nat → Prop
n : Nat
h1 : Q n
x✝ : Q n → Prop
⊢ ⏎
  □IH : ▷ ∀ n, <affine> ⌜Q n⌝ -∗ ∀ x, □ T n -∗ □ P n
  □x✝ : T n
  ⊢ □ P n
-/
#guard_msgs (trace, drop error) in
example {n : Nat} {P T : Nat → PROP} {Q : Nat → Prop} {h1 : Q n} {_ : (Q n) → Prop} :
    ⊢ □ T n -∗ □ P n := by
  iintro #_
  iloeb as IH generalizing! %n
  trace_state

end iloeb

section iinv

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] {N : Namespace}

/--
  Tests `iinv` with `elimInv_acc_without_close`, `elimAcc_fupd` and
  `intoAcc_inv` where the side condition is trivial.
-/
example {P : IProp GF} : inv N iprop(<pers> P) ={⊤}=∗ ▷ P := by
  iintro #Hinv
  iinv Hinv with #H
  imodintro
  isplit
  · iexact H
  · imodintro
    inext
    iexact H

/-- Tests `iinv` with a concrete namespace whose closure is expensive to unfold.
Regression test for https://github.com/leanprover-community/iris-lean/issues/557 -/
example {P : IProp GF} : inv `long_name iprop(<pers> P) ={⊤}=∗ ▷ P := by
  iintro #Hinv
  iinv Hinv with #H
  imodintro
  isplit
  · iexact H
  · imodintro
    inext
    iexact H

/--
  Tests `iinv` with `elimInv_acc_with_close`, `elimModal_fupd_fupd` and
  `intoAcc_inv` where the side condition is trivial.
-/
example {P : IProp GF} : inv N iprop(<pers> P) ={⊤}=∗ ▷ P := by
  iintro #Hinv
  iinv Hinv with #H Hclose
  imod Hclose $$ H
  imodintro
  inext
  iexact H

/--
  Tests `iinv` with `elimInv_acc_without_close`, `elimAcc_fupd` and
  `intoAcc_inv`, relying on the side condition `↑N ⊆ E`.
-/
example {E} {P : IProp GF} {h : ↑N ⊆ E} : inv N iprop(<pers> P) ={E}=∗ ▷ P := by
  iintro #Hinv
  iinv Hinv with #H
  imodintro
  isplit
  · iexact H
  · imodintro
    inext
    iexact H

/- Tests `iinv` with an invalid invariant. -/
/-- error: iinv: invalid invariant P (ElimInv type class synthesis failed) -/
#guard_msgs in
example {E : CoPset} {P : IProp GF} : □ P ={E}=∗ ▷ P := by
  iintro #HP
  iinv HP with #H

/-- Tests `iinv` with `elimInv_acc_without_close`, `elimAcc_fupd` and `intoAcc_cinv`. -/
example [CInvG GF]  {γ : GName} {p : Qp} :
    cinv N γ iprop(<pers> P) ∗ own γ p ⊢@{IProp GF} |={⊤}=> own γ p ∗ ▷ P := by
  iintro ⟨#Hinv, H⟩
  iinv Hinv with ⟨#HP, Hown⟩
  imodintro
  isplit
  iexact HP
  iframe
  imodintro
  inext
  iexact HP

/-- Tests `iinv` with `elimInv_acc_with_close`, `elimModal_fupd_fupd` and `intoAcc_cinv`. -/
example [CInvG GF] {γ : GName} {p : Qp} :
    cinv N γ iprop(<pers> P) ∗ own γ p ⊢@{IProp GF} |={⊤}=> own γ p ∗ ▷ P := by
  iintro ⟨#Hinv, H⟩
  iinv Hinv with ⟨#HP, Hown⟩ Hclose
  imod Hclose $$ HP
  imodintro
  iframe
  inext
  iexact HP

/--
  Tests `iinv` with `elimInv_acc_without_close`, `elimAcc_fupd`,
  `intoAcc_cinv` and a specialization pattern. -/
example [CInvG GF] {γ : GName} {p1 p2 : Qp} {P : IProp GF} :
    cinv N γ iprop(<pers> P) ∗ own γ p1 ∗ own γ p2
    ⊢@{IProp GF} |={⊤}=> own γ p1 ∗ own γ p2 ∗ ▷ P := by
  iintro ⟨#Hinv, Hown1, Hown2⟩
  iinv Hinv $$ [Hown2 //] with ⟨#HP, Hown2⟩
  imodintro
  iframe HP ∗
  imodintro
  inext
  iexact HP

/-- Tests `iinv` with `elimInv_acc_with_close`, `elimModal_fupd_fupd` and `intoAcc_na`. -/
example {t : NaInvPoolName} [NaInvG GF] {E1 E2 : CoPset} {P : IProp GF} (h : ↑N ⊆ E1) :
    NonAtomicInvariant.inv t N iprop(<pers> P) ∗ own t E1 ∗ own t E2
    ={⊤}=∗ own t E1 ∗ own t E2 ∗ ▷ P := by
  iintro ⟨#Hinv, Hown1, Hown2⟩
  iinv Hinv $$ [Hown1 //] with ⟨#HP, Hown1⟩ Hclose
  imod Hclose $$ [HP Hown1]
  · iframe
    iexact HP
  · iframe
    imodintro
    inext
    iexact HP

/-- Tests the robustness of `iinv` in presence of other invariants. -/
example {t : NaInvPoolName} [NaInvG GF] {N1 N2 N3 : Namespace} {E1 E2 : CoPset}
    {P : IProp GF} (h : ↑N3 ⊆ E1) :
    inv N1 P ∗ NonAtomicInvariant.inv t N3 iprop(<pers> P) ∗ inv N2 P ∗ own t E1 ∗ own t E2
    ={⊤}=∗ own t E1 ∗ own t E2 ∗ ▷ P := by
  iintro ⟨#_, #Hinv, #_, Hown1, Hown2⟩
  iinv Hinv $$ Hown1 with ⟨#HP, Hown1⟩
  imodintro
  isplitl [Hown1]
  · iframe HP ∗
  · iintro Hown1
    iframe
    imodintro
    inext
    iexact HP

/--
  Tests `iinv` with two invariant hypotheses using the same `Namespace` value.
  The last hypothesis in the context with this `Namespace` value gets chosen.
-/
example {t : NaInvPoolName} [NaInvG GF] {N : Namespace} {E1 E2 : CoPset}
    {P Q : IProp GF} (h : ↑N ⊆ E1) :
    NonAtomicInvariant.inv t N iprop(<pers> Q) ∗
    NonAtomicInvariant.inv t N iprop(<pers> P) ∗
    own t E1 ∗ own t E2 ={⊤}=∗ own t E1 ∗ own t E2 ∗ ▷ P := by
  iintro ⟨#_, #_, Hown1, Hown2⟩
  iinv N $$ Hown1 with ⟨#HP, Hown1⟩
  imodintro
  isplitl [Hown1]
  · iframe HP ∗
  · iintro Hown1
    iframe
    imodintro
    inext
    iexact HP

/-
  Tests `iinv` with a valid `Namespace` value that does not correspond to
  any invariant hypothesis in the context.
-/
/-- error: iinv: invariant hypothesis with the namespace N3 not found -/
#guard_msgs in
example {t : NaInvPoolName} [NaInvG GF] {N1 N2 N3 : Namespace} {E1 E2 : CoPset}
    {P Q : IProp GF} (h : ↑N1 ⊆ E1) :
    NonAtomicInvariant.inv t N1 iprop(<pers> Q) ∗
    NonAtomicInvariant.inv t N2 iprop(<pers> P) ∗
    own t E1 ∗ own t E2 ={⊤}=∗ own t E1 ∗ own t E2 ∗ ▷ P := by
  iintro ⟨#_, #_, Hown1, Hown2⟩
  iinv N3 $$ Hown1 with ⟨#HP, Hown1⟩

/- Variables to test `iinv` with `WP`. -/
variable {hlc : outParam HasLC} {Expr State Obs Val} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {e : Expr} {v : Val} {Φ : Val → IProp GF} {P : IProp GF}

/-- Tests `iinv` with `elimInv_acc_without_close`, `intoAcc_inv` and `elimAcc_wp_atomic`. -/
example [Language.Atomic ↑s e] (h : ↑N ⊆ E) :
    ⊢ inv N P -∗ (▷ P -∗ WP e @ s ; (E \ ↑N) {{ v, |={E \ ↑N}=> ▷ P ∗ Φ v }}) -∗ WP e @ s ; E {{ Φ }} := by
  iintro #Hinv Hwp
  iinv Hinv with H
  iapply Hwp
  iexact H

end iinv

section ieval

/-- Tests `ieval` and `isimp` to simplify the goal and specific Iris hypotheses. -/
example [BI PROP] {u v w x y z : Nat} :
    ⌜(x + y) + 3 = 4⌝ ∗ ⌜(w + z) + 1 = Nat.succ 2⌝ ∗ ⌜(u + v) = v⌝
    ⊢@{PROP} ⌜Nat.succ (x + y) = 2⌝ ∗ ⌜w + z = 2⌝ ∗ ⌜u = 0⌝ := by
  iintro ⟨H1, H2, H3⟩
  -- Simplify `(x + y) + 3 = 4` as `x + y = 1`
  isimp at H1
  isplitl [H1]
  -- Simplify `(x + y).succ = 2` as `x + y = 1`
  · isimp
    iexact H1
  -- Simplify the goal `w + z + 1 = Nat.succ 2` as `w + z = 2` and `u + v = v` as `u = 0`
  · ieval (simp) at H2 H3
    iframe

/- Tests `isimp` with a pure hypothesis in the selection pattern. -/
/-- error: ieval: pure hypotheses in the selection pattern is not supported -/
#guard_msgs in
example [BI PROP] {x y : Nat} :
    ⌜(x + y) + 3 = 4⌝ ⊢@{PROP} ⌜Nat.succ (x + y) = 2⌝ := by
  iintro #H
  isimp at %x H

/- Tests `isimp` with the simplification failing. -/
/-- error: `simp` made no progress -/
#guard_msgs in
example [BI PROP] {x y : Nat} : ⌜x = 0⌝ ⊢@{PROP} ⌜x = 0⌝ := by
  iintro #H
  isimp at H

/-- Tests `isimp` with variants of `simp`. -/
example [BI PROP] {m n p q : Nat} (h1 : m = n + 1) (h2 : r = t) (h3 : s = t) :
    ⌜p + q = q + p⌝ ⊢@{PROP} ⌜m - 1 = n⌝ ∗ ⌜r = s⌝ ∗ ⌜q + p = p + q⌝ := by
  iintro H
  isplitr
  -- Simplification with a hypothesis
  · isimp [h1]
    itrivial
  · isplitr
    -- Simplification with all rules annotated with `[simp]` and all hypotheses
    · isimp [*]
      itrivial
    -- Simplification only with specific rules
    · isimp only [Nat.add_comm] at H
      isimp only [Nat.add_comm]
      iexact H

private def def3 := 10
private def def4 := def3

/-- Tests `iunfold` to unfold definitions in an Iris hypothesis and a proof goal. -/
example [BI PROP] : ⌜def4 = 10⌝ ⊢@{PROP} ⌜10 = 10⌝ ∗ ⌜def4 = 10⌝ := by
  iintro #H
  -- Unfold definitions in an Iris hypothesis
  iunfold def4, def3 at H
  iframe H
  -- Unfold definitions in the proof goal
  iunfold def4, def3
  ipureintro
  rfl

/- Tests `ieval` where the supplied tactic solves the goal completely. -/
/-- error: ieval: the supplied tactic does not produce exactly one subgoal -/
#guard_msgs in
example [BI PROP] {x y : Nat} (_ : False) :
    ⌜(x + y) + 3 = 4⌝ ⊢@{PROP} ⌜Nat.succ (x + y) = 2⌝ := by
  iintro H
  ieval (contradiction) at H

/- Tests `ieval` where the supplied tactic produces more than one subgoal. -/
/-- error: ieval: the supplied tactic does not produce exactly one subgoal -/
#guard_msgs in
example [BI PROP] {x y : Nat} (h : False) :
    ⌜(x + y) + 3 = 4⌝ ⊢@{PROP} ⌜Nat.succ (x + y) = 2⌝ := by
  iintro H
  ieval (cases x) at H

/- Tests `ieval` where the given tactic breaks the Iris entailment. -/
/-- error: ieval: the goal is not Iris entailment upon applying the supplied tactic -/
#guard_msgs in
example [BI PROP] {x y : Nat} :
    ⌜(x + y) + 3 = 4⌝ ⊢@{PROP} ⌜Nat.succ (x + y) = 2⌝ := by
  iintro H
  ieval (exfalso) at H

end ieval

section iaccu

/-- Tests `iaccu` with spatial hypotheses `HQ`, `HR1`, `HR2` and `HT`. -/
example [BI PROP] (P Q R1 R2 S T : PROP) :
    (□ P -∗ Q -∗ (R1 ∗ R2) -∗ □ S -∗ T -∗ ∃ U, U ∧ ⌜U = iprop(Q ∗ R1 ∗ R2 ∗ T)⌝) := by
  iintro #HP HQ ⟨HR1, HR2⟩ #HS HT
  iexists ?_
  isplit
  · iaccu
  · ipureintro <;> rfl

/-- Tests `iaccu` where there is no spatial hypothesis in the context. -/
example [BI PROP] (P Q R : PROP) :
    (□ P -∗ □ Q -∗ □ R -∗ ∃ S, S ∧ ⌜S = iprop(emp)⌝) := by
  iintro #HP #HQ #HR
  iexists ?_
  isplit
  · iaccu
  · ipureintro <;> rfl

/- Tests `iaccu` where the proof goal is not a metavariable. -/
/-- error: iaccu: R is not a metavariable -/
#guard_msgs in
example [BI PROP] (P Q R : PROP) :
    □ P -∗ Q -∗ R := by
  iintro #HP HQ
  iaccu

end iaccu

section iinduction

/-- Inductively defined binary tree data structure. -/
inductive Tree (α : Type u) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Repr

/--
  Tests `iinduction` with simple induction on binary trees.
  All propositions involved are in the intuitionistic context in this example.
  Tests the use of a hole (`_`) for leaving a variable unnamed.
-/
example [BI PROP] {α} {t : Tree α} {P : Tree α → PROP} :
    □ P .leaf -∗ □ (∀ l x r, P l -∗ P r -∗ P (.node l x r)) -∗ P t := by
  iintro #H1 #H2
  iinduction t with
  | leaf => iexact H1
  | node l _ r IH1 IH2 =>
    iapply H2
    · iexact IH1
    · iexact IH2

/-- A simple function on the inductive structure `Tree`. -/
def Tree.mirror {α} : Tree α → Tree α
  | .leaf => .leaf
  | .node l x r => .node (.mirror r) x (.mirror l)

/--
  Tests `iinduction` with a pure hypothesis that involves `Tree.mirror`.
-/
example [BI PROP] {α} {t : Tree α} :
  ⊢@{PROP} ⌜.mirror (.mirror t) = t⌝ := by
  iinduction t with simp [Tree.mirror]
  | leaf =>
    itrivial
  | node l x r ihl ihr =>
    isplit
    · iexact ihl
    · iexact ihr

/-- An inductively defined predicate on `Tree`. -/
def Tree.pred [BI PROP] {α} (P : α → PROP) : Tree α → PROP
  | .leaf => emp
  | .node l x r => iprop(Tree.pred P l ∗ (P x ∗ Tree.pred P r))

/--
  Tests `iinduction` with spatial hypotheses that involve `Tree.mirror` and `Tree.pred`.
-/
example [BI PROP] {α} {t : Tree α} {P : α → PROP} :
    Tree.pred P t -∗ Tree.pred P (.mirror t) := by
  iintro H
  iinduction t with simp [Tree.mirror, Tree.pred]
  | leaf => itrivial
  | node l x r ihl ihr =>
    icases H with ⟨Hl, Hx, Hr⟩
    iframe
    isplitl [Hr]
    · iapply ihr $$ Hr
    · iapply ihl $$ Hl

/--
  Definition of n-tree and its induction principle from:
  https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/.E2.9C.94.20Induction.20principle.20for.20nested.20inductive.20types/near/437905021
-/
inductive NTree (α : Type)
| leaf
| node : α → List (NTree α) → NTree α

@[induction_eliminator]
theorem NTree.induction_principle {α} (p : NTree α → Prop) (h_leaf : p leaf)
  (h_node : (x : α) → (ts : List (NTree α)) → (ih : ∀ t ∈ ts, p t) → p (node x ts)) :
  ∀ t : NTree α, p t :=
  @NTree.rec α p (λ ts => ∀ t ∈ ts, p t) h_leaf h_node (List.forall_mem_nil p)
    (λ _ _ h_head h_tail => List.forall_mem_cons.mpr (And.intro h_head h_tail))

def NTree.id : NTree α → NTree α
  | .leaf => .leaf
  | .node x ts => .node x (ts.map .id)

/-- Tests `iinduction` with the mutual induction principle. -/
example [BI PROP] {α} {t : NTree α} : ⊢@{PROP} ⌜t.id = t⌝ := by
  iinduction t with simp [NTree.id]
  | h_leaf => itrivial
  | h_node x ts IH1 =>
    iinduction ts with simp
    | nil => itrivial
    | cons t ts IH2 =>
      isplit
      · iapply IH1
        itrivial
      · iapply IH2
        iintro !> %x H
        iapply IH1
        imodintro
        iright
        iexact H

def NTree.childCount {α} : NTree α → Nat
  | .leaf => 0
  | .node _ ts => ts.length

/-- An binary relation defined using nested induction. -/
inductive NTree.Rel {α β} (R : α → β → Prop) : NTree α → NTree β → Prop
  | leaf : Rel R .leaf .leaf
  | node : ∀ a b ts₁ ts₂, R a b → List.Forall₂ (Rel R) ts₁ ts₂ → Rel R (.node a ts₁) (.node b ts₂)

@[induction_eliminator]
theorem NTree.Rel.induction_principle {α β} {R : α → β → Prop}
    (p : ∀ {t1 : NTree α} {t2 : NTree β}, NTree.Rel R t1 t2 → Prop)
    (h_base : p .leaf)
    (h_step : ∀ a b ts1 ts2 ra f2,
      List.Forall₂ (fun t1 t2 => ∀ h : NTree.Rel R t1 t2, p h) ts1 ts2 →
      p (.node a b ts1 ts2 ra f2)) :
    ∀ t1 t2 (h : NTree.Rel R t1 t2), p h :=
  @NTree.Rel.rec α β R
    (fun _ _ h => p h)
    (fun a b _ => List.Forall₂ (fun t1 t2 => ∀ h : NTree.Rel R t1 t2, p h) a b)
    h_base h_step .nil
    (fun _ _ ih_h ih_hs => .cons (fun _ => ih_h) ih_hs)

/-- Tests `iinduction` with induction that uses the type class instance `intoIH_listForall₂`. -/
example [BI PROP] {α β} {R : α → β → Prop}
    {t₁ : NTree α} {t₂ : NTree β} (H : NTree.Rel R t₁ t₂) :
    ⊢@{PROP} ⌜NTree.childCount t₁ = NTree.childCount t₂⌝ := by
  iinduction H with
  | h_base =>
    ipureintro
    apply rfl
  | h_step x1 x2 t1 t2 r IH1 IH2 =>
    ipureintro
    simp only [NTree.childCount]
    induction IH1 with simp_all

/--
  Tests `iinduction` with simple induction on natural numbers.
  Tries `iframe` to solve induction subgoals before splitting into cases.
  Tests the `using` clause for custom recursor name.
  Tests the use of a synthetic hole (`?_`) for delaying the induction subgoal.
-/
example [BI PROP] {n : Nat} {P : Nat → PROP} :
    □ (∀ k, P k -∗ P (k + 1)) -∗ P 0 -∗ P n := by
  iintro #H1 H2
  iinduction n using Nat.rec with iframe
  | succ n IH => ?_
  iapply H1
  iapply IH
  iexact H2

/--
  Tests `iinduction` with induction on lists where it is necessary to
  generalise some variables.
  Tests the use of the wildcard (`_`) for remaining cases.
-/
example [BI PROP] {α} {xs : List α} {acc : List α} {P : List α → List α → PROP} :
    □ (∀ acc, P [] acc) -∗
    □ (∀ x xs acc, P xs (x :: acc) -∗ P (x :: xs) acc) -∗
    P xs acc := by
  iintro #Hnil #Hcons
  iinduction xs generalizing %acc with
  | cons x xs IH =>
    iapply Hcons
    iexact IH
  | _ =>
    iapply Hnil

/- Tests `iinduction` with a non-inductive datatype. -/
/-- error: iinduction: unable to determine inductive type -/
#guard_msgs in
example [BI PROP] {P : PROP} : ⊢ P := by
  iinduction P

/-
  Tests `iinduction` with induction on natural numbers with invalid, duplicate
  and missing user-supplied alternative names.
-/
/-- error: iinduction: invalid alternative name `invalidA`
---
error: iinduction: invalid alternative name `invalidB`
---
error: iinduction: duplicate alternative name `zero`
---
error: iinduction: alternative `succ` has not been provided -/
#guard_msgs in
example [BI PROP] {n : Nat} :
    ⊢@{PROP} ⌜n + 0 = n⌝ := by
  iinduction n with
  | invalidA  => done
  | zero      => itrivial
  | invalidB  => done
  | zero      => itrivial

/- Tests `iinduction` with extra arguments supplied by the user. -/
/-- error: iinduction: too many variable names provided at alternative `succ`: 4 provided, but 2 expected -/
#guard_msgs in
example [BI PROP] {n : Nat} :
    ⊢@{PROP} ⌜n + 0 = n⌝ := by
  iinduction n with
  | zero => itrivial
  | succ n IH extra1 extra2 => itrivial

/--
  Tests `iinduction` using a custom recursor name (strong induction).
  Tests induction on an expression `n + m`, which requires generalisation.
  Tests the use of the same tactic sequences for multiple alternative names.
  Note that `P` and `S` are reverted and thus included as wand premises
  in the induction hypothesis.
  Meanwhile, `T (n + m)` is also reverted because it involves the induction
  target `n + m`.
  The proposition `Q m` is reverted manually using the `generalizing` clause.
  On the contrary, `R` is not reverted.
-/
example [BI PROP] {P R S : PROP} {Q T : Nat → PROP} {m n : Nat} :
    ⊢ P -∗ □ Q m -∗ □ R -∗ S -∗ □ T (n + m) -∗ ⌜n + m + 0 = n + m⌝ := by
  iintro HP #HQ #HR HS #HT
  iinduction n + m using Nat.caseStrongRecOn generalizing %m HQ HT with
  | zero | ind _ _ => itrivial

/-
  Tests `iinduction` with invalid use of the wildcard. The wildcard
  should always be the last case.
-/
/-- error: iinduction: invalid occurrence of the wildcard alternative `| _ => ...`: It must be the last alternative -/
#guard_msgs in
example [BI PROP] {n : Nat} :
    ⊢@{PROP} ⌜n + 0 = n⌝ := by
  iinduction n with
  | zero => itrivial
  | _ => _
  | succ n IH => itrivial

/-
  Tests `iinduction` with redundant use of the wildcard. The wildcard
  is not required when all cases have already been handled.
-/
/-- error: iinduction: wildcard alternative is not needed -/
#guard_msgs in
example [BI PROP] {n : Nat} :
    ⊢@{PROP} ⌜n + 0 = n⌝ := by
  iinduction n with
  | zero => itrivial
  | succ n IH => itrivial
  | _ => _

/-
  Tests `iinduction` with the tactic after `with` syntax.
  One of the alternative names (`zero`) becomes redundant and therefore should
  be detected by the tactic.
-/
/-- error: iinduction: alternative `zero` is not needed -/
#guard_msgs in
example [BI PROP] {P Q R S T : PROP} {n : Nat} :
    ⊢ P -∗ □ Q -∗ □ R -∗ S -∗ □ T -∗ ⌜0 + 0 = 0⌝ -∗ ⌜n + 0 = n⌝ := by
  iintro HP #HQ #HR HS #HT #H
  iinduction n with (try iexact H)
  | zero => itrivial  -- Redundant case
  | succ n IH => itrivial

/-
  Tests `iinduction` with a tactic after `with` syntax.
  One of the alternative names (`zero`) is redundant and therefore not required.
  The tactic should not complain about any missing alternative names.
-/
example [BI PROP] {P Q R S T : PROP} {n : Nat} :
    ⊢ P -∗ □ Q -∗ □ R -∗ S -∗ □ T -∗ ⌜0 + 0 = 0⌝ -∗ ⌜n + 0 = n⌝ := by
  iintro HP #HQ #HR HS #HT #H
  iinduction n with (try iexact H)
  -- No complaints about missing `zero` case
  | succ n IH => itrivial

/-
  Tests `iinduction` on `n` generalising `m`, where:
  - *regular hypotheses* `h1 : T m` and `U1 : (T m) → Prop` depend on `m`;
  - *regular hypotheses* `h2 : U1 h1` and `U2 : (U1 h1) → PROP` depends on `h1`,
    which in turn depends on `m`;
  - *Iris hypotheses* `□HQ : Q m` and `□HR : R m` depend on `m`;
  - *Iris hypothesis* `□HS : S n` depends on the induction target `n`;
  - *Iris hypothesis* `□HU2 : U2 h2` depends on `h2` and `U2`, which depends
    depend on `h1`, which in turn depends on `m`.
  This requires manual resolution.
-/
/-- info: Try this:
  [apply] iinduction n generalizing %m %h1 %U1 %h2 %U2 HQ HR HS HU2 with
  | zero
  | succ n IH => itrivial
---
info: Try this:
  [apply] iinduction n generalizing! %m with
  | zero
  | succ n IH => itrivial
---
error: iinduction: The following hypotheses depend on variables in the `generalizing` clause but are not themselves included:
• Lean hypothesis `h1` depends on `m`
• Lean hypothesis `U1` depends on `m`
• Lean hypothesis `h2` depends on `m`
• Lean hypothesis `U2` depends on `m`
• Iris hypothesis `HQ` depends on `m`
• Iris hypothesis `HR` depends on `m`
• Iris hypothesis `HS` depends on `n`
• Iris hypothesis `HU2` depends on `h2` -/
#guard_msgs in
example [BI PROP] {P : PROP} {m n : Nat} {Q R S : Nat → PROP} {T : Nat → Prop}
    {h1 : T m} {U1 : (T m) → Prop} {h2 : U1 h1} {U2 : (U1 h1) → PROP} :
    ⊢ P -∗ □ Q m -∗ □ R m -∗ □ S n -∗ □ U2 h2 -∗ ⌜n + 0 = n⌝ := by
  iintro HP #HQ #HR #HS #HU2
  iinduction n generalizing %m with
  | zero
  | succ n IH => itrivial

/--
  The same example with `generalizing!` clause does not require any manual
  resolution of dependencies.
-/
example [BI PROP] {P : PROP} {m n : Nat} {Q R S : Nat → PROP} {T : Nat → Prop}
    {h1 : T m} {U1 : (T m) → Prop} {h2 : U1 h1} {U2 : (U1 h1) → PROP} :
    ⊢ P -∗ □ Q m -∗ □ R m -∗ □ S n -∗ □ U2 h2 -∗ ⌜n + 0 = n⌝ := by
  iintro HP #HQ #HR #HS #HU2
  iinduction n generalizing! %m with
  | zero
  | succ n IH => itrivial

/- Similar test as above, except that some hypotheses have inaccessible names. -/
/-- info: Try this:
  [apply] iinduction n generalizing! %m with
  | zero
  | succ n IH => itrivial
---
error: iinduction: The following hypotheses depend on variables in the `generalizing` clause but are not themselves included:
• Lean hypothesis `h1` depends on `m`
• Lean hypothesis `U1` depends on `m`
• Lean hypothesis `h2` depends on `m`
• Lean hypothesis `U2` depends on `m`
• Lean hypothesis `x` (inaccessible name) depends on `n`
• Iris hypothesis `x` (inaccessible name) depends on `h2` -/
#guard_msgs in
example [BI PROP] {P : PROP} {m n : Nat} {T : Nat → Prop}
    {h1 : T m} {_ : T n} {U1 : (T m) → Prop}
    {h2 : U1 h1} {U2 : (U1 h1) → PROP} :
    ⊢ P -∗ □ U2 h2 -∗ ⌜n + 0 = n⌝ := by
  iintro HP #_
  iinduction n generalizing %m with
  | zero
  | succ n IH => itrivial

end iinduction
