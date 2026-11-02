/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProofMode.Lib.Fixpoint

@[expose] public section
open Iris BI OFE

namespace IrisTest.Fixpoint

section
variable [BI PROP]

ifix zero : PROP := zero
monotone_by imono

-- `.pre` takes the fixed parameters, then the recursive function, then the varying parameters.
example (p : PROP) : zero.pre p = p := rfl
example : zero (PROP := PROP) = zero.pre zero := zero.unfold

-- The reopened recursive variable keeps dependencies on fixed parameters intact.
ifix indexed (n : Nat) [OFE (Fin n)] (i : Fin n) : PROP :=
  let next := indexed n
  next i

example (n : Nat) [OFE (Fin n)] (Φ : Fin n → PROP) (i : Fin n) :
    indexed.pre n Φ i = Φ i := rfl
example (n : Nat) [OFE (Fin n)] (i : Fin n) :
    indexed (PROP := PROP) n i = indexed.pre n (indexed n) i := indexed.unfold n i

-- No recursive occurrence is required either.
icofix constant (p : PROP) : PROP := p

example (p Φ : PROP) : constant.pre p Φ = p := rfl
end

section
variable [BI PROP] [OFE α]

-- An unchanged explicit argument is fixed: the remaining domain is Unit.
icofix unchanged (x : α) : PROP := unchanged x
monotone_by imono

example (x : α) (Φ : PROP) : unchanged.pre x Φ = Φ := rfl

-- A bare recursive reference keeps its missing argument varying.
ifix passed (x : α) : PROP :=
  let next := passed
  next x

example (Φ : α → PROP) (x : α) : passed.pre Φ x = Φ x := rfl

-- Qualified recursive references use the same local declaration as unqualified references.
ifix qualified (x : α) : PROP :=
  let next := IrisTest.Fixpoint.qualified
  next x

example (Φ : α → PROP) (x : α) : qualified.pre Φ x = Φ x := rfl

-- One product-valued argument must remain a single argument when unpacked.
ifix passedPair (p : α × α) : PROP :=
  let next := passedPair
  next p
monotone_by imono

example (Φ : α × α → PROP) (p : α × α) : passedPair.pre Φ p = Φ p := rfl

-- A later call can disqualify arguments that the first call passes unchanged.
ifix both (x y : α) : PROP := iprop(both x y ∗ both y x)
monotone_by imono

example (Φ : α → α → PROP) (x y : α) :
    both.pre Φ x y = iprop(Φ x y ∗ Φ y x) := rfl


-- Implicit arguments are elaborated before their values are compared.
ifix implicitSwap {x y : α} : PROP := implicitSwap (x := y) (y := x)
monotone_by imono

example (x y : α) :
    implicitSwap (PROP := PROP) (x := x) (y := y) = implicitSwap (x := y) (y := x) := by
  rw [implicitSwap.unfold]

-- The recursive function is passed partially applied; the fixed parameter is not a prefix.
icofix partialSwap (x : α) (setting : Bool) (y : α) : PROP :=
  let next := partialSwap y setting
  next x
monotone_by imono

example (setting : Bool) (Φ : α → α → PROP) (x y : α) :
    partialSwap.pre setting Φ x y = Φ y x := rfl
example (setting : Bool) (x y : α) :
    partialSwap (PROP := PROP) x setting y =
      partialSwap.pre setting (fun x y => partialSwap x setting y) x y :=
  partialSwap.unfold x setting y
end

section
variable [BI PROP] (sameName : PROP)

-- ERROR: Lean rejects a definition named like a section variable.
-- Intended: the recursive reference is identified by its variable, and
-- `IrisTest.Fixpoint.sameName.pre sameName Φ = Φ` holds by `rfl`.
/-- invalid declaration name `sameName` -/
#guard_msgs (error, substring := true) in
ifix sameName : PROP := sameName
monotone_by imono
end

section
universe u v w
variable (PROP : Type u) [BI PROP] (α : Type v) [OFE α]

-- Explicit section parameters and independent universes survive closing and reopening the body.
ifix sectionRec (x : α) : PROP :=
  let next := sectionRec
  next x

example (Φ : α → PROP) (x : α) : sectionRec.pre PROP α Φ x = Φ x := rfl
example (x : α) : sectionRec PROP α x = sectionRec.pre PROP α (sectionRec PROP α) x :=
  sectionRec.unfold PROP α x

-- This universe appears in the body, but not the declared result or argument types.
ifix lifted (x : α) : PROP :=
  let next := lifted
  let y : ULift.{w} α := ⟨x⟩
  next y.down

example (Φ : α → PROP) (x : α) : lifted.pre PROP α Φ x = Φ x := rfl
end

-- Auto-bound type parameters are inferred from the signature without a surrounding section.
ifix inferredSwap [BI PROP] [OFE α] (x y : α) : PROP := inferredSwap y x
monotone_by imono

example [BI PROP] [OFE α] (Φ : α → α → PROP) (x y : α) :
    inferredSwap.pre Φ x y = Φ y x := rfl

/-! Using the generated (co)induction principles. -/
section
variable [BI PROP]

ifix even (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ even m)

-- Induction with one varying parameter.
theorem even_mod (n : Nat) : even (PROP := PROP) n ⊢ ⌜n % 2 = 0⌝ := by
  iintro H
  iapply (even.iter (fun n => iprop(⌜n % 2 = 0⌝))) $$ [] %n H
  iintro !> %p Hp
  unfold even.pre
  icases Hp with (%h | ⟨%m, %h, %hm⟩)
  · ipureintro; omega
  · ipureintro; omega

-- Strong induction: the hypothesis also knows that the fixpoint holds.
example (n : Nat) : even (PROP := PROP) n ⊢ ⌜n % 2 = 0⌝ := by
  iintro H
  iapply (even.ind (fun n => iprop(⌜n % 2 = 0⌝))) $$ [] %n H
  iintro !> %p Hp
  dsimp only [even.pre]
  icases Hp with (%h | ⟨%m, H⟩)
  · ipureintro; omega
  · icases H with ⟨Hh, H⟩
    icases Hh with %h
    icases H with ⟨%hm, -⟩
    ipureintro; omega

-- Persistence follows from closure conditions on the body, found by instance search.
example (n : Nat) : Persistent (even (PROP := PROP) n) := inferInstance

icofix stream (P : PROP) : PROP := iprop(P ∗ ▷ stream P)

-- Coinduction with no varying parameters: no quantifier.
theorem stream_of_box (P : PROP) : □ P ⊢ stream iprop(□ P) := by
  iintro #HP
  iapply (stream.coiter iprop(□ P) iprop(□ P)) $$ [] HP
  iintro !> #H
  unfold stream.pre
  isplit
  · iexact H
  · inext; iexact H

-- Strong coinduction: the hypothesis may also conclude the fixpoint itself.
example (P : PROP) : □ P ⊢ stream iprop(□ P) := by
  iintro #HP
  iapply (stream.coind iprop(□ P) iprop(□ P)) $$ [] HP
  iintro !> #H
  unfold stream.pre
  isplit
  · iexact H
  · inext; ileft; iexact H

ifix parity (b : Bool) (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ parity (!b) m)

-- Two varying parameters are quantified separately, and a fixpoint can be `Φ`.
example : ⊢ (□ ∀ b n, parity.pre (fun b n => parity (PROP := PROP) b n) b n -∗ parity b n) -∗
    ∀ b n, parity b n -∗ parity b n :=
  parity.iter _
end

/-! The rest of the generated lemmas. -/
section
variable [BI PROP]

ifix nat (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ nat m)
ifix nat' (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ nat' m)

example (n : Nat) : nat (PROP := PROP) n ⊢ nat.pre nat n := nat.unfold_mp n
example (n : Nat) : nat.pre nat n ⊢ nat (PROP := PROP) n := nat.unfold_mpr n

-- Well-founded induction, with `nat` itself as the prefixpoint.
example (Φ : Nat → PROP) : ⊢ (□ ∀ n, nat.pre nat n -∗ Φ n) -∗ ∀ n, nat n -∗ Φ n :=
  nat.ind_wf Φ nat fun n => and_elim_r.trans (nat.unfold_mpr n)

-- Monotonicity in the body compares two fixpoints.
example (n : Nat) : nat (PROP := PROP) n ⊢ nat' n := by
  iintro H
  iapply (nat.strong_mono nat'.pre nat' nat'.unfold_mpr) $$ [] %n H
  iintro !> %Φ %m HΦ
  iexact HΦ

example (n : Nat) : Absorbing (nat (PROP := PROP) n) := inferInstance

example [BIAffine PROP] (n : Nat) : Affine (nat (PROP := PROP) n) := inferInstance

example (n : Nat) : Persistent (nat (PROP := PROP) n) := inferInstance

-- `eq_lfp` relates `nat` to the library's least fixpoint.
open MonotoneFixpoint in
example : ∃ h, nat (PROP := PROP) = lfp nat.pre h := ⟨_, nat.eq_lfp⟩

-- Parameterized coinduction, with `stream` itself as the postfixpoint.
example (P Φ : PROP) : ⊢ □ (Φ -∗ stream.pre P (stream P)) -∗ Φ -∗ stream P :=
  stream.paco P Φ (stream P) ((stream.unfold_mp P).trans or_intro_r)

-- Varying parameters whose types depend on each other are packed into a dependent tuple.
ifix vec (n : Nat) (v : Fin n → Nat) : PROP :=
  iprop(⌜∀ i, v i = 0⌝ ∨ ∃ m, ∃ w : Fin m → Nat, ⌜n = m + 1⌝ ∗ vec m w)

example (Φ : (n : Nat) → (Fin n → Nat) → PROP) :
    ⊢ (□ ∀ n v, vec.pre Φ n v -∗ Φ n v) -∗ ∀ n v, vec n v -∗ Φ n v :=
  vec.iter Φ
end

-- `ne` is generated when the varying parameters have OFEs.
section
variable [BI PROP]

ifix swapNe [OFE α] (x y : α) : PROP := iprop(▷ swapNe y x)

example [OFE α] (n : Nat) (x y x' y' : α) (h : x ≡{n}≡ x' ∧ y ≡{n}≡ y') :
    swapNe (PROP := PROP) x y ≡{n}≡ swapNe x' y' := by
  refine swapNe.ne (fun Φ hΦ n x y x' y' h => ?_) n x y x' y' h
  exact later_ne.ne (hΦ n y x y' x' ⟨h.2, h.1⟩)
end

run_cmd do
  let info ← Lean.getConstInfo `IrisTest.Fixpoint.lifted.pre
  unless info.levelParams.contains `w do
    throwError "lost universe parameter appearing only in the body"

-- The environment used to elaborate recursion must not contribute axioms or sorry proofs.
run_cmd do
  for decl in #[`zero, `indexed, `constant, `unchanged, `passed, `qualified, `passedPair, `both,
      `implicitSwap, `partialSwap, `sectionRec, `lifted, `inferredSwap, `even, `stream, `parity,
      `nat, `nat', `vec, `swapNe] do
    for suffix in #[Lean.Name.anonymous, `pre, `pre_mono, `unfold, `unfold_mp, `unfold_mpr,
        `eq_lfp, `eq_gfp, `iter, `ind, `ind_wf, `coiter, `coind, `paco, `strong_mono, `affine,
        `absorbing, `persistent_affine, `persistent_absorbing, `ne] do
      let name := `IrisTest.Fixpoint ++ decl ++ suffix
      unless (← Lean.getEnv).contains name do continue
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unexpected axiom {axiomName} in {name}"

end IrisTest.Fixpoint
