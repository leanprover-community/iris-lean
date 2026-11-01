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
monotone_by monotone
nonexp_by
  intros Φ _
  constructor
  intros n a _ _
  exact OFE.Dist.rfl

-- `.pre` is curried; only `.pre'` uses the Unit adapter for zero varying arguments.
example (p : PROP) : zero.pre p = p := rfl
example (Φ : Unit → PROP) : zero.pre' Φ () = Φ () := rfl
example : zero (PROP := PROP) = zero.pre' (fun _ => zero) () := zero.unfold

-- The reopened recursive variable keeps dependencies on fixed parameters intact.
ifix indexed (n : Nat) [OFE (Fin n)] (i : Fin n) : PROP :=
  let next := indexed n
  next i
nonexp_by intros; assumption

example (n : Nat) [OFE (Fin n)] (Φ : Fin n → PROP) (i : Fin n) :
    indexed.pre' n Φ i = Φ i := rfl
example (n : Nat) [OFE (Fin n)] (i : Fin n) :
    indexed (PROP := PROP) n i = indexed.pre' n (indexed n) i := indexed.unfold n i

-- No recursive occurrence is required either.
icofix constant (p : PROP) : PROP := p
monotone_by monotone; infer_instance
nonexp_by
  intros Φ _
  constructor
  intros n a _ _
  exact OFE.Dist.rfl

example (p : PROP) (Φ : Unit → PROP) : constant.pre' p Φ () = p := rfl
end

section
variable [BI PROP] [OFE α]

-- An unchanged explicit argument is fixed: the remaining domain is Unit.
icofix unchanged (x : α) : PROP := unchanged x
monotone_by monotone
nonexp_by
  intros Φ _
  constructor
  intros n a _ _
  exact OFE.Dist.rfl

example (x : α) (Φ : Unit → PROP) : unchanged.pre' x Φ () = Φ () := rfl

-- A bare recursive reference keeps its missing argument varying.
ifix passed (x : α) : PROP :=
  let next := passed
  next x
nonexp_by intros; assumption

example (Φ : α → PROP) (x : α) : passed.pre' Φ x = Φ x := rfl

-- Qualified recursive references use the same local declaration as unqualified references.
ifix qualified (x : α) : PROP :=
  let next := IrisTest.Fixpoint.qualified
  next x
nonexp_by intros; assumption

example (Φ : α → PROP) (x : α) : qualified.pre' Φ x = Φ x := rfl

-- One product-valued argument must remain a single argument when unpacked.
ifix passedPair (p : α × α) : PROP :=
  let next := passedPair
  next p
monotone_by monotone; infer_instance
nonexp_by intros; assumption

example (Φ : α × α → PROP) (p : α × α) : passedPair.pre' Φ p = Φ p := rfl

-- A later call can disqualify arguments that the first call passes unchanged.
ifix both (x y : α) : PROP := iprop(both x y ∗ both y x)
monotone_by monotone
nonexp_by
  intros Φ _
  constructor
  intros n a b h
  exact sep_ne.ne (NonExpansive.ne (f := Φ) h) (NonExpansive.ne (f := Φ) ⟨h.2, h.1⟩)

example (Φ : α → α → PROP) (x y : α) :
    both.pre Φ x y = iprop(Φ x y ∗ Φ y x) := rfl

example (Φ : α × α → PROP) (x y : α) :
    both.pre' Φ (x, y) = iprop(Φ (x, y) ∗ Φ (y, x)) := rfl

-- Implicit arguments are elaborated before their values are compared.
ifix implicitSwap {x y : α} : PROP := implicitSwap (x := y) (y := x)
monotone_by monotone
nonexp_by
  intros Φ _
  constructor
  intros n a b h
  exact NonExpansive.ne (f := Φ) ⟨h.2, h.1⟩

example (Φ : α × α → PROP) (x y : α) : implicitSwap.pre' Φ (x, y) = Φ (y, x) := rfl
example (x y : α) :
    implicitSwap (PROP := PROP) (x := x) (y := y) =
      implicitSwap.pre' (fun p => implicitSwap (x := p.1) (y := p.2)) (x, y) :=
  implicitSwap.unfold

-- The recursive function is passed partially applied; the fixed parameter is not a prefix.
icofix partialSwap (x : α) (setting : Bool) (y : α) : PROP :=
  let next := partialSwap y setting
  next x
monotone_by monotone; infer_instance
nonexp_by
  intros Φ _
  constructor
  intros n a b h
  exact NonExpansive.ne (f := Φ) ⟨h.2, h.1⟩

example (setting : Bool) (Φ : α × α → PROP) (x y : α) :
    partialSwap.pre' setting Φ (x, y) = Φ (y, x) := rfl
example (setting : Bool) (x y : α) :
    partialSwap (PROP := PROP) x setting y =
      partialSwap.pre' setting (fun p => partialSwap p.1 setting p.2) (x, y) :=
  partialSwap.unfold x setting y
end

section
variable [BI PROP] (sameName : PROP)

-- The recursive reference is identified by its variable, even if a section variable shares its name.
ifix sameName : PROP := sameName
monotone_by monotone
nonexp_by
  intros Φ _
  constructor
  intros n a _ _
  exact OFE.Dist.rfl

example (Φ : Unit → PROP) : IrisTest.Fixpoint.sameName.pre' sameName Φ () = Φ () := rfl
end

section
universe u v w
variable (PROP : Type u) [BI PROP] (α : Type v) [OFE α]

-- Explicit section parameters and independent universes survive closing and reopening the body.
ifix sectionRec (x : α) : PROP :=
  let next := sectionRec
  next x
nonexp_by intros; assumption

example (Φ : α → PROP) (x : α) : sectionRec.pre' PROP α Φ x = Φ x := rfl
example (x : α) : sectionRec PROP α x = sectionRec.pre' PROP α (sectionRec PROP α) x :=
  sectionRec.unfold PROP α x

-- This universe appears in the body, but not the declared result or argument types.
ifix lifted (x : α) : PROP :=
  let next := lifted
  let y : ULift.{w} α := ⟨x⟩
  next y.down
nonexp_by intros; assumption

example (Φ : α → PROP) (x : α) : lifted.pre' PROP α Φ x = Φ x := rfl
end

-- Auto-bound type parameters are inferred from the signature without a surrounding section.
ifix inferredSwap [BI PROP] [OFE α] (x y : α) : PROP := inferredSwap y x
monotone_by monotone
nonexp_by
  intros Φ _
  constructor
  intros n a b h
  exact NonExpansive.ne (f := Φ) ⟨h.2, h.1⟩

example [BI PROP] [OFE α] (Φ : α × α → PROP) (x y : α) :
    inferredSwap.pre' Φ (x, y) = Φ (y, x) := rfl

run_cmd do
  let info ← Lean.getConstInfo `IrisTest.Fixpoint.lifted.pre
  unless info.levelParams.contains `w do
    throwError "lost universe parameter appearing only in the body"

-- The environment used to elaborate recursion must not contribute axioms or sorry proofs.
run_cmd do
  for decl in #[`zero, `indexed, `constant, `unchanged, `passed, `qualified, `passedPair, `both,
      `implicitSwap, `partialSwap, `sameName, `sectionRec, `lifted, `inferredSwap] do
    for suffix in #[Lean.Name.anonymous, `pre, `pre', `pre_mono, `unfold] do
      let name := `IrisTest.Fixpoint ++ decl ++ suffix
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unexpected axiom {axiomName} in {name}"

end IrisTest.Fixpoint
