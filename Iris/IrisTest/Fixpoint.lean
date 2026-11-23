/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.ProofMode.Lib.Fixpoint

@[expose] public section
open Iris BI OFE

namespace IrisTest.Fixpoint

/-! ## Fixed and varying parameters -/

section
variable [BI PROP] [OFE α]

ifix zero : PROP := zero

example (p : PROP) : zero.pre p = p := rfl

-- A parameter passed unchanged is fixed.
icofix unchanged (x : α) : PROP := unchanged x

example (x : α) (Φ : PROP) : unchanged.pre x Φ = Φ := rfl

-- A bare recursive reference keeps its argument varying.
ifix passed (x : α) : PROP :=
  let next := passed
  next x

example (Φ : α → PROP) (x : α) : passed.pre Φ x = Φ x := rfl

-- A later call can make varying a parameter that the first call passes unchanged.
ifix both (x y : α) : PROP := iprop(both x y ∗ both y x)

example (Φ : α → α → PROP) (x y : α) : both.pre Φ x y = iprop(Φ x y ∗ Φ y x) := rfl

-- The fixed parameter need not come first.
icofix partialSwap (x : α) (setting : Bool) (y : α) : PROP :=
  let next := partialSwap y setting
  next x

example (setting : Bool) (Φ : α → α → PROP) (x y : α) :
    partialSwap.pre setting Φ x y = Φ y x := rfl

ifix implicitSwap {x y : α} : PROP := implicitSwap (x := y) (y := x)

example (x y : α) :
    implicitSwap (PROP := PROP) (x := x) (y := y) = implicitSwap (x := y) (y := x) := by
  rw [implicitSwap.unfold]

-- A fixed parameter that a later one depends on, and an instance between them.
ifix indexed (n : Nat) [OFE (Fin n)] (i : Fin n) : PROP := indexed n i

-- A product-valued parameter stays one parameter, and so does a `PSigma`-valued one.
ifix passedPair (p : α × α) : PROP := passedPair p
ifix psig (s : (n : Nat) ×' Fin (n + 1)) (b : Bool) : PROP := iprop(▷ psig ⟨s.1 + 1, 0⟩ (!b))

example (Φ : (n : Nat) ×' Fin (n + 1) → Bool → PROP) :
    ⊢ (□ ∀ s b, psig.pre Φ s b -∗ Φ s b) -∗ ∀ s b, psig s b -∗ Φ s b := psig.iter Φ

-- A non-recursive body.
icofix constant (p : PROP) : PROP := p

example (p Φ : PROP) : constant.pre p Φ = p := rfl

-- A non-recursive body of function type: the parameters of the type vary.
def base (n : Nat) (b : Bool) : PROP := iprop(⌜n = 0 ∧ b⌝)
ifix nonRecFn (n : Nat) : Bool → PROP := base n

example (n : Nat) (Φ : Bool → PROP) :
    ⊢ (□ ∀ b, nonRecFn.pre n Φ b -∗ Φ b) -∗ ∀ b, nonRecFn n b -∗ Φ b := nonRecFn.iter n Φ
end

section
variable [BI PROP] (sameName : PROP)

-- ERROR: Lean rejects a definition named like a section variable.
-- Intended: `sameName.pre sameName Φ = Φ` by `rfl`.
/-- invalid declaration name `sameName` -/
#guard_msgs (error, substring := true) in
ifix sameName : PROP := sameName
end

section
universe u v w
variable (PROP : Type u) [BI PROP] (α : Type v) [OFE α]

-- Explicit section variables, and a universe that only the body mentions.
ifix lifted (x : α) : PROP :=
  let next := lifted
  let y : ULift.{w} α := ⟨x⟩
  next y.down

example (Φ : α → PROP) (x : α) : lifted.pre PROP α Φ x = Φ x := rfl

run_cmd do
  unless (← Lean.getConstInfo `IrisTest.Fixpoint.lifted.pre).levelParams.contains `w do
    throwError "lost universe parameter appearing only in the body"
end

-- Auto-bound implicits.
ifix inferredSwap [BI PROP] [OFE α] (x y : α) : PROP := inferredSwap y x

/-! ## The generated lemmas -/

section
variable [BI PROP]

ifix even (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ even m)

example (n : Nat) : even (PROP := PROP) n ⊢ ⌜n % 2 = 0⌝ := by
  iintro H
  iapply (even.iter (fun n => iprop(⌜n % 2 = 0⌝))) $$ [] %n H
  iintro !> %p Hp
  unfold even.pre
  icases Hp with (%h | ⟨%m, %h, %hm⟩) <;> ipureintro <;> omega

example (n : Nat) : Persistent (even (PROP := PROP) n) := inferInstance

icofix stream (P : PROP) : PROP := iprop(P ∗ ▷ stream P)

example (P : PROP) : □ P ⊢ stream iprop(□ P) := by
  iintro #HP
  iapply (stream.coiter iprop(□ P) iprop(□ P)) $$ [] HP
  iintro !> #H
  unfold stream.pre
  isplit
  · iexact H
  · inext; iexact H

example (P Φ : PROP) : ⊢ □ (Φ -∗ stream.pre P (stream P)) -∗ Φ -∗ stream P :=
  stream.paco P Φ (stream P) ((stream.unfold_mp P).trans or_intro_r)

ifix nat (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ nat m)
ifix nat' (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ nat' m)

example (Φ : Nat → PROP) : ⊢ (□ ∀ n, nat.pre nat n -∗ Φ n) -∗ ∀ n, nat n -∗ Φ n :=
  nat.ind_wf Φ nat fun n => and_elim_r.trans (nat.unfold_mpr n)

example (n : Nat) : nat (PROP := PROP) n ⊢ nat' n := by
  iintro H
  iapply (nat.strong_mono nat'.pre nat' nat'.unfold_mpr) $$ [] %n H
  iintro !> %Φ %m HΦ
  iexact HΦ

example [BIAffine PROP] (n : Nat) : Affine (nat (PROP := PROP) n) := inferInstance

open MonotoneFixpoint in
example : ∃ h, nat (PROP := PROP) = lfp nat.pre h := ⟨_, nat.eq_lfp⟩

-- Two varying parameters, which may depend on each other.
ifix vec (n : Nat) (v : Fin n → Nat) : PROP :=
  iprop(⌜∀ i, v i = 0⌝ ∨ ∃ m, ∃ w : Fin m → Nat, ⌜n = m + 1⌝ ∗ vec m w)

example (Φ : (n : Nat) → (Fin n → Nat) → PROP) :
    ⊢ (□ ∀ n v, vec.pre Φ n v -∗ Φ n v) -∗ ∀ n v, vec n v -∗ Φ n v := vec.iter Φ

-- `ne`, when the varying parameters have OFEs.
ifix swapNe [OFE α] (x y : α) : PROP := iprop(▷ swapNe y x)

example [OFE α] (n : Nat) (x y x' y' : α) (h : x ≡{n}≡ x' ∧ y ≡{n}≡ y') :
    swapNe (PROP := PROP) x y ≡{n}≡ swapNe x' y' :=
  swapNe.ne (fun _ hΦ n x y x' y' h => later_ne.ne (hΦ n y x y' x' ⟨h.2, h.1⟩)) n x y x' y' h
end

/-! ## Default tactics and `imono` -/

section
variable [BI PROP]

elab "logged_imono" : tactic => do
  Lean.logInfo "monotone_by ran"
  Lean.Elab.Tactic.evalTactic (← `(tactic| imono))

/-- info: monotone_by ran -/
#guard_msgs in
ifix once (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ once (n + 1))
monotone_by logged_imono

/--
error: ifix: `ifix_monotone_default` did not prove monotonicity. Provide a proof with `monotone_by`, or extend `ifix_monotone_default` with `macro_rules`.
-/
#guard_msgs (error, substring := true) in
ifix bad (n : Nat) : PROP := iprop(bad n -∗ False)

-- A failing rule falls back to older ones, here `imono`.
section
local macro_rules | `(tactic| ifix_monotone_default) => `(tactic| exact nonsense)

ifix fallsBack (n : Nat) : PROP := fallsBack n
end

set_option iris.fixpoint.monotoneDefault false in
/--
error: icofix: the default tactic for monotonicity is off. Provide a proof with `monotone_by`, or turn `iris.fixpoint.monotoneDefault` back on.
-/
#guard_msgs in
icofix noDefault (n : Nat) : PROP := noDefault n

-- `imono` unfolds a definition each time it occurs, a recursive one only once.
def later' (X : PROP) : PROP := iprop(▷ X)
def twice (Φ : Nat → PROP) (n : Nat) : PROP := later' (later' (Φ n))

example : BIMono (PROP := PROP) twice := by imono

def bigSep (Φ : List Nat → PROP) : List Nat → PROP
  | [] => iprop(emp)
  | _ :: xs => iprop(Φ xs ∗ bigSep Φ xs)

/-- error: imono: no rule for IrisTest.Fixpoint.bigSep, after unfolding it once -/
#guard_msgs (error, substring := true) in
example : BIMono (fun (Φ : List Nat → PROP) l => bigSep Φ l) := by imono

example : BIMono (fun (Φ : Nat → PROP) n => if n = 0 then iprop(emp) else Φ (n - 1)) := by imono

/-- error: imono: expected a monotonicity goal -/
#guard_msgs (error, substring := true) in
example : True := by imono
end

/-! ## Names and attributes -/

namespace Names
local notation "PROP" => IProp BundledGFunctors.default

ifix self (self : Nat) : PROP := iprop(⌜self = 0⌝)

protected ifix prot (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ▷ Names.prot (n + 1))

example (n : Nat) : Names.prot n = Names.prot.pre Names.prot n := Names.prot.unfold n

-- A constant `Names.Names.clash` is not the new `Names.clash`.
set_option linter.iris.dupNamespace false in
def Names.clash : Nat := 0

ifix clash (n : Nat) : PROP := iprop(▷ clash (n + 1))

example (n : Nat) : clash n = clash.pre clash n := clash.unfold n

ifix _root_.rootedFix (n : Nat) : PROP := iprop(▷ rootedFix (n + 1))

example (n : Nat) : rootedFix n = rootedFix.pre rootedFix n := rootedFix.unfold n

-- A `local` attribute outlives the command's own section; reducibility is set when declaring.
@[local simp] ifix localSimp (n : Nat) : PROP := iprop(⌜n = 0⌝)

example : localSimp 0 = iprop(⌜0 = 0⌝) := by simp

@[semireducible] ifix semireducibleFix (n : Nat) : PROP := iprop(▷ semireducibleFix (n + 1))
end Names

-- No `sorry` or unexpected axioms.
run_cmd do
  for decl in #[`zero, `passed, `both, `partialSwap, `implicitSwap, `indexed, `psig, `nonRecFn,
      `lifted, `even, `stream, `nat, `vec, `swapNe] do
    for suffix in #[Lean.Name.anonymous, `pre, `pre_mono, `unfold, `unfold_mp, `unfold_mpr,
        `eq_lfp, `eq_gfp, `iter, `ind, `ind_wf, `coiter, `coind, `paco, `strong_mono, `affine,
        `absorbing, `persistent_affine, `persistent_absorbing, `ne] do
      let name := `IrisTest.Fixpoint ++ decl ++ suffix
      unless (← Lean.getEnv).contains name do continue
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unexpected axiom {axiomName} in {name}"

end IrisTest.Fixpoint
