/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Algebra.DFrac
import Iris.Algebra.Agree

/-!
# The DFrac Agree Camera

The product of the discardable fraction camera and the agree camera, bundled with
convenience definitions and lemmas.
-/

namespace Iris

open OFE CMRA DFrac

/-- The DFrac-Agree camera: a product of `DFrac F` and `Agree A`. -/
abbrev DFracAgreeR (F : Type _) [UFraction F] (A : Type _) [OFE A] := DFrac F × Agree A
-- Rocq: dfrac_agreeR

/-- Construct a DFrac-Agree element from a fraction and a value. -/
def toDFracAgree [UFraction F] [OFE A] (d : DFrac F) (a : A) : DFracAgreeR F A := (d, toAgree a)
-- Rocq: to_dfrac_agree

/-- Construct a DFrac-Agree element from an owned fraction and a value. -/
def toFracAgree [UFraction F] [OFE A] (q : F) (a : A) : DFracAgreeR F A := toDFracAgree (.own q) a
-- Rocq: to_frac_agree

section lemmas

variable {F : Type _} [UFraction F] {A : Type _} [OFE A]

instance toDFracAgree.ne {d : DFrac F} : NonExpansive (toDFracAgree d : A → DFracAgreeR F A) where
  ne _ _ _ h := ⟨OFE.Dist.rfl, OFE.NonExpansive.ne (f := toAgree) h⟩
-- Rocq: to_dfrac_agree_ne

-- Rocq: to_dfrac_agree_proper (follows from NonExpansive)

instance toDFracAgree.exclusive {a : A} : CMRA.Exclusive (toDFracAgree (.own (1 : F)) a) :=
  DFrac.one_exclusive_left
-- Rocq: to_dfrac_agree_exclusive

instance toDFracAgree.discrete {d : DFrac F} {a : A} [OFE.DiscreteE a] :
    OFE.DiscreteE (toDFracAgree d a) :=
  ⟨fun h => ⟨is_discrete.discrete h.1, (Agree.toAgree.is_discrete ‹_›).discrete h.2⟩⟩
-- Rocq: to_dfrac_agree_discrete

theorem toDFracAgree.injN {d₁ d₂ : DFrac F} {a₁ a₂ : A}
    (h : toDFracAgree d₁ a₁ ≡{n}≡ toDFracAgree d₂ a₂) : d₁ ≡{n}≡ d₂ ∧ a₁ ≡{n}≡ a₂ :=
  ⟨h.1, toAgree.inj h.2⟩
-- Rocq: to_dfrac_agree_injN

theorem toDFracAgree.inj {d₁ d₂ : DFrac F} {a₁ a₂ : A}
    (h : toDFracAgree d₁ a₁ ≡ toDFracAgree d₂ a₂) : d₁ ≡ d₂ ∧ a₁ ≡ a₂ :=
  ⟨h.1, Agree.toAgree_inj h.2⟩
-- Rocq: to_dfrac_agree_inj

theorem dfrac_agree_op {d₁ d₂ : DFrac F} {a : A} :
    toDFracAgree (d₁ • d₂) a ≡ toDFracAgree d₁ a • toDFracAgree d₂ a :=
  ⟨OFE.Equiv.rfl, Agree.idemp.symm⟩
-- Rocq: dfrac_agree_op

theorem frac_agree_op {q₁ q₂ : F} {a : A} :
    toFracAgree (q₁ + q₂) a ≡ toFracAgree q₁ a • toFracAgree q₂ a :=
  dfrac_agree_op (d₁ := .own q₁) (d₂ := .own q₂)
-- Rocq: frac_agree_op

theorem dfrac_agree_op_valid {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    ✓ (toDFracAgree d₁ a₁ • toDFracAgree d₂ a₂) ↔ ✓ (d₁ • d₂) ∧ a₁ ≡ a₂ := by
  simp only [CMRA.Valid, Prod.Valid, Prod.op, CMRA.op, toDFracAgree]
  exact and_congr_right fun _ => Agree.toAgree_op_valid_iff_equiv
-- Rocq: dfrac_agree_op_valid

theorem dfrac_agree_op_valid_L [OFE.Leibniz A] {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    ✓ (toDFracAgree d₁ a₁ • toDFracAgree d₂ a₂) ↔ ✓ (d₁ • d₂) ∧ a₁ = a₂ := by
  rw [dfrac_agree_op_valid]
  exact and_congr_right fun _ => OFE.Leibniz.leibniz
-- Rocq: dfrac_agree_op_valid_L

theorem dfrac_agree_op_validN {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    ✓{n} (toDFracAgree d₁ a₁ • toDFracAgree d₂ a₂) ↔ ✓ (d₁ • d₂) ∧ a₁ ≡{n}≡ a₂ := by
  show Prod.ValidN n (Prod.op (toDFracAgree d₁ a₁) (toDFracAgree d₂ a₂)) ↔ _
  simp only [Prod.ValidN, toDFracAgree]
  rw [Agree.toAgree_op_validN_iff_dist]
  exact and_congr_left' (CMRA.valid_iff_validN' (α := DFrac F) n)
-- Rocq: dfrac_agree_op_validN

theorem frac_agree_op_valid {q₁ q₂ : F} {a₁ a₂ : A} :
    ✓ (toFracAgree q₁ a₁ • toFracAgree q₂ a₂) ↔ Fraction.Proper (q₁ + q₂) ∧ a₁ ≡ a₂ :=
  dfrac_agree_op_valid
-- Rocq: frac_agree_op_valid

theorem frac_agree_op_valid_L [OFE.Leibniz A] {q₁ q₂ : F} {a₁ a₂ : A} :
    ✓ (toFracAgree q₁ a₁ • toFracAgree q₂ a₂) ↔ Fraction.Proper (q₁ + q₂) ∧ a₁ = a₂ :=
  dfrac_agree_op_valid_L
-- Rocq: frac_agree_op_valid_L

theorem frac_agree_op_validN {q₁ q₂ : F} {a₁ a₂ : A} :
    ✓{n} (toFracAgree q₁ a₁ • toFracAgree q₂ a₂) ↔ Fraction.Proper (q₁ + q₂) ∧ a₁ ≡{n}≡ a₂ :=
  dfrac_agree_op_validN
-- Rocq: frac_agree_op_validN

theorem dfrac_agree_included {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    toDFracAgree d₁ a₁ ≼ toDFracAgree d₂ a₂ ↔ (d₁ ≼ d₂) ∧ a₁ ≡ a₂ := by
  simp only [toDFracAgree, CMRA.Included]
  constructor
  · rintro ⟨⟨zd, za⟩, hd, ha⟩
    exact ⟨⟨zd, hd⟩, Agree.toAgree_included.mp ⟨za, ha⟩⟩
  · rintro ⟨⟨zd, hd⟩, ha⟩
    refine ⟨(zd, toAgree a₁), hd, ?_⟩
    show toAgree a₂ ≡ toAgree a₁ • toAgree a₁
    exact (OFE.NonExpansive.eqv ha.symm).trans Agree.idemp.symm
-- Rocq: dfrac_agree_included

theorem dfrac_agree_included_L [OFE.Leibniz A] {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    toDFracAgree d₁ a₁ ≼ toDFracAgree d₂ a₂ ↔ (d₁ ≼ d₂) ∧ a₁ = a₂ := by
  rw [dfrac_agree_included]
  exact and_congr_right fun _ => OFE.Leibniz.leibniz
-- Rocq: dfrac_agree_included_L

theorem dfrac_agree_includedN {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    toDFracAgree d₁ a₁ ≼{n} toDFracAgree d₂ a₂ ↔ (d₁ ≼ d₂) ∧ a₁ ≡{n}≡ a₂ := by
  simp only [toDFracAgree, CMRA.IncludedN]
  constructor
  · rintro ⟨⟨zd, za⟩, hd, ha⟩
    exact ⟨(CMRA.inc_iff_incN (α := DFrac F) n).mpr ⟨zd, hd⟩, Agree.toAgree_includedN.mp ⟨za, ha⟩⟩
  · rintro ⟨hdinc, ha⟩
    obtain ⟨zd, hd⟩ := (CMRA.inc_iff_incN (α := DFrac F) n).mp hdinc
    exact ⟨(zd, toAgree a₁), hd,
      (OFE.NonExpansive.ne ha.symm).trans (OFE.Equiv.dist Agree.idemp.symm)⟩
-- Rocq: dfrac_agree_includedN

theorem frac_agree_included {q₁ q₂ : F} {a₁ a₂ : A} :
    toFracAgree q₁ a₁ ≼ toFracAgree q₂ a₂ ↔ (DFrac.own q₁ ≼ DFrac.own q₂) ∧ a₁ ≡ a₂ :=
  dfrac_agree_included
-- Rocq: frac_agree_included

theorem frac_agree_included_L [OFE.Leibniz A] {q₁ q₂ : F} {a₁ a₂ : A} :
    toFracAgree q₁ a₁ ≼ toFracAgree q₂ a₂ ↔ (DFrac.own q₁ ≼ DFrac.own q₂) ∧ a₁ = a₂ :=
  dfrac_agree_included_L
-- Rocq: frac_agree_included_L

theorem frac_agree_includedN {q₁ q₂ : F} {a₁ a₂ : A} :
    toFracAgree q₁ a₁ ≼{n} toFracAgree q₂ a₂ ↔ (DFrac.own q₁ ≼ DFrac.own q₂) ∧ a₁ ≡{n}≡ a₂ :=
  dfrac_agree_includedN
-- Rocq: frac_agree_includedN

/-- While `Update.exclusive` takes care of most updates, it is not sufficient
for this one since there is no abstraction-preserving way to rewrite
`toDFracAgree d₁ v₁ • toDFracAgree d₂ v₂` into something simpler. -/
theorem dfrac_agree_update_2 {d₁ d₂ : DFrac F} {a₁ a₂ a' : A}
    (hd : d₁ • d₂ = .own 1) :
    toDFracAgree d₁ a₁ • toDFracAgree d₂ a₂ ~~> toDFracAgree d₁ a' • toDFracAgree d₂ a' := by
  have : toDFracAgree d₁ a₁ • toDFracAgree d₂ a₂ ≡
      (DFrac.own (1 : F), toAgree a₁ • toAgree a₂) :=
    ⟨hd ▸ OFE.Equiv.rfl, OFE.Equiv.rfl⟩
  calc
    _ ≡ (DFrac.own (1 : F), toAgree a₁ • toAgree a₂) := this
    _ ~~> toDFracAgree d₁ a' • toDFracAgree d₂ a' :=
      @Update.exclusive _ _ _ _ DFrac.one_exclusive_left
        (dfrac_agree_op_valid.mpr ⟨hd ▸ valid_own_one, OFE.Equiv.rfl⟩)
-- Rocq: dfrac_agree_update_2

theorem frac_agree_update_2 {q₁ q₂ : F} {a₁ a₂ a' : A}
    (hq : q₁ + q₂ = 1) :
    toFracAgree q₁ a₁ • toFracAgree q₂ a₂ ~~> toFracAgree q₁ a' • toFracAgree q₂ a' :=
  dfrac_agree_update_2 (show DFrac.own q₁ • DFrac.own q₂ = .own 1 from congrArg _ hq)
-- Rocq: frac_agree_update_2

theorem dfrac_agree_persist {d : DFrac F} {a : A} :
    toDFracAgree d a ~~> toDFracAgree .discard a := by
  intro n mz hv
  simp only [toDFracAgree, CMRA.op?] at hv ⊢
  rcases mz with _ | ⟨mz₁, mz₂⟩
  · exact ⟨(DFrac.update_discard n none hv.1), hv.2⟩
  · exact ⟨(DFrac.update_discard n (some mz₁) hv.1), hv.2⟩
-- Rocq: dfrac_agree_persist

theorem dfrac_agree_unpersist [IsSplitFraction F] {a : A} :
    toDFracAgree (.discard : DFrac F) a ~~>: fun k => ∃ q, k = toDFracAgree (.own q) a := by
  intro n mz hv
  simp only [toDFracAgree, CMRA.op?] at hv ⊢
  rcases mz with _ | ⟨mz₁, mz₂⟩
  · obtain ⟨d', ⟨q, rfl⟩, hv'⟩ := DFrac.update_acquire n none hv.1
    exact ⟨(.own q, toAgree a), ⟨q, rfl⟩, hv', hv.2⟩
  · obtain ⟨d', ⟨q, rfl⟩, hv'⟩ := DFrac.update_acquire n (some mz₁) hv.1
    exact ⟨(.own q, toAgree a), ⟨q, rfl⟩, hv', hv.2⟩
-- Rocq: dfrac_agree_unpersist

end lemmas

end Iris
