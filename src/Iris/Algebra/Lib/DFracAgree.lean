/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

import Iris.Algebra.DFrac
import Iris.Algebra.Agree
meta import Iris.Std.RocqPorting

/-!
# The DFrac Agree Camera

The product of the discardable fraction camera and the agree camera, bundled with
convenience definitions and lemmas.
-/

namespace Iris

open OFE CMRA DFrac

namespace DFracAgree

@[rocq_alias dfrac_agreeR]
abbrev DFracAgreeR (F : Type _) [UFraction F] (A : Type _) [OFE A] := DFrac F × Agree A

@[rocq_alias to_dfrac_agree]
def mk [UFraction F] [OFE A] (d : DFrac F) (a : A) : DFracAgreeR F A := (d, toAgree a)

variable {F : Type _} [UFraction F] {A : Type _} [OFE A]

@[rocq_alias to_dfrac_agree_ne]
instance mk_ne {d : DFrac F} : NonExpansive (mk d : A → DFracAgreeR F A) where
  ne _ _ _ h := ⟨.rfl, NonExpansive.ne (f := toAgree) h⟩

@[rocq_alias to_dfrac_agree_exclusive]
instance mk_exclusive {a : A} : Exclusive (mk (.own (1 : F)) a) := one_exclusive_left

@[rocq_alias to_dfrac_agree_discrete]
instance mk_discrete {d : DFrac F} {a : A} [DiscreteE a] : DiscreteE (mk d a) :=
  ⟨fun h => ⟨is_discrete.discrete h.1, (Agree.toAgree.is_discrete ‹_›).discrete h.2⟩⟩

@[rocq_alias to_dfrac_agree_injN]
theorem mk_injN {d₁ d₂ : DFrac F} {a₁ a₂ : A} (h : mk d₁ a₁ ≡{n}≡ mk d₂ a₂) : d₁ ≡{n}≡ d₂ ∧ a₁ ≡{n}≡ a₂ :=
  ⟨h.1, toAgree.inj h.2⟩

@[rocq_alias to_dfrac_agree_inj]
theorem mk_inj {d₁ d₂ : DFrac F} {a₁ a₂ : A} (h : mk d₁ a₁ ≡ mk d₂ a₂) : d₁ ≡ d₂ ∧ a₁ ≡ a₂ :=
  ⟨h.1, Agree.toAgree_inj h.2⟩

@[rocq_alias dfrac_agree_op]
theorem mk_op {d₁ d₂ : DFrac F} {a : A} : mk (d₁ • d₂) a ≡ mk d₁ a • mk d₂ a :=
  ⟨Equiv.rfl, Agree.idemp.symm⟩

@[rocq_alias dfrac_agree_op_valid]
theorem op_valid {d₁ d₂ : DFrac F} {a₁ a₂ : A} : ✓ (mk d₁ a₁ • mk d₂ a₂) ↔ ✓ (d₁ • d₂) ∧ a₁ ≡ a₂ := by
  simp only [Valid, Prod.Valid, Prod.op, CMRA.op, mk]
  exact and_congr_right fun _ => Agree.toAgree_op_valid_iff_equiv

@[rocq_alias dfrac_agree_op_valid_L]
theorem op_valid_L [Leibniz A] {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    ✓ (mk d₁ a₁ • mk d₂ a₂) ↔ ✓ (d₁ • d₂) ∧ a₁ = a₂ := by
  rw [op_valid]
  exact and_congr_right fun _ => Leibniz.leibniz

@[rocq_alias dfrac_agree_op_validN]
theorem op_validN {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    ✓{n} (mk d₁ a₁ • mk d₂ a₂) ↔ ✓ (d₁ • d₂) ∧ a₁ ≡{n}≡ a₂ := by
  show Prod.ValidN n (Prod.op (mk d₁ a₁) (mk d₂ a₂)) ↔ _
  simp only [Prod.ValidN, mk]
  rw [Agree.toAgree_op_validN_iff_dist]
  exact and_congr_left' (valid_iff_validN' (α := DFrac F) n)

@[rocq_alias dfrac_agree_included]
theorem included {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    mk d₁ a₁ ≼ mk d₂ a₂ ↔ (d₁ ≼ d₂) ∧ a₁ ≡ a₂ := by
  simp only [mk, Included]
  constructor
  · rintro ⟨⟨zd, za⟩, hd, ha⟩
    exact ⟨⟨zd, hd⟩, Agree.toAgree_included.mp ⟨za, ha⟩⟩
  · rintro ⟨⟨zd, hd⟩, ha⟩
    refine ⟨(zd, toAgree a₁), hd, ?_⟩
    show toAgree a₂ ≡ toAgree a₁ • toAgree a₁
    exact (NonExpansive.eqv ha.symm).trans Agree.idemp.symm

@[rocq_alias dfrac_agree_included_L]
theorem included_L [Leibniz A] {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    mk d₁ a₁ ≼ mk d₂ a₂ ↔ (d₁ ≼ d₂) ∧ a₁ = a₂ := by
  rw [included]
  exact and_congr_right fun _ => Leibniz.leibniz

@[rocq_alias dfrac_agree_includedN]
theorem includedN {d₁ d₂ : DFrac F} {a₁ a₂ : A} :
    mk d₁ a₁ ≼{n} mk d₂ a₂ ↔ (d₁ ≼ d₂) ∧ a₁ ≡{n}≡ a₂ := by
  simp only [mk, IncludedN]
  constructor
  · rintro ⟨⟨zd, za⟩, hd, ha⟩
    exact ⟨(inc_iff_incN (α := DFrac F) n).mpr ⟨zd, hd⟩, Agree.toAgree_includedN.mp ⟨za, ha⟩⟩
  · rintro ⟨hdinc, ha⟩
    obtain ⟨zd, hd⟩ := (inc_iff_incN (α := DFrac F) n).mp hdinc
    exact ⟨(zd, toAgree a₁), hd, (NonExpansive.ne ha.symm).trans (Equiv.dist Agree.idemp.symm)⟩

@[rocq_alias dfrac_agree_update_2]
theorem update₂ {d₁ d₂ : DFrac F} {a₁ a₂ a' : A} (hd : d₁ • d₂ = .own 1) :
    mk d₁ a₁ • mk d₂ a₂ ~~> mk d₁ a' • mk d₂ a' := by
  have : mk d₁ a₁ • mk d₂ a₂ ≡ (own (1 : F), toAgree a₁ • toAgree a₂) :=
    ⟨hd ▸ Equiv.rfl, Equiv.rfl⟩
  calc
    _ ≡ (own (1 : F), toAgree a₁ • toAgree a₂) := this
    _ ~~> mk d₁ a' • mk d₂ a' :=
      @Update.exclusive _ _ _ _ one_exclusive_left
        (op_valid.mpr ⟨hd ▸ valid_own_one, .rfl⟩)

@[rocq_alias dfrac_agree_persist]
theorem persist {d : DFrac F} {a : A} : mk d a ~~> mk .discard a := by
  intro n mz hv
  simp only [mk, op?] at hv ⊢
  rcases mz with _ | ⟨mz₁, mz₂⟩
  · exact ⟨DFrac.update_discard n none hv.1, hv.2⟩
  · exact ⟨DFrac.update_discard n (some mz₁) hv.1, hv.2⟩

@[rocq_alias dfrac_agree_unpersist]
theorem unpersist [IsSplitFraction F] {a : A} :
    mk (.discard : DFrac F) a ~~>: fun k => ∃ q, k = mk (.own q) a := by
  intro n mz hv
  simp only [mk, op?] at hv ⊢
  rcases mz with _ | ⟨mz₁, mz₂⟩
  · obtain ⟨d', ⟨q, rfl⟩, hv'⟩ := DFrac.update_acquire n none hv.1
    exact ⟨(.own q, toAgree a), ⟨q, rfl⟩, hv', hv.2⟩
  · obtain ⟨d', ⟨q, rfl⟩, hv'⟩ := DFrac.update_acquire n (some mz₁) hv.1
    exact ⟨(.own q, toAgree a), ⟨q, rfl⟩, hv', hv.2⟩

/-! ## Frac variants -/

namespace Frac

@[rocq_alias to_frac_agree]
def mk [UFraction F] [OFE A] (q : F) (a : A) : DFracAgreeR F A := DFracAgree.mk (.own q) a

variable {F : Type _} [UFraction F] {A : Type _} [OFE A]

@[rocq_alias frac_agree_op]
theorem mk_op {q₁ q₂ : F} {a : A} : mk (q₁ + q₂) a ≡ mk q₁ a • mk q₂ a :=
  DFracAgree.mk_op (d₁ := .own q₁) (d₂ := .own q₂)

@[rocq_alias frac_agree_op_valid]
theorem op_valid {q₁ q₂ : F} {a₁ a₂ : A} :
    ✓ (mk q₁ a₁ • mk q₂ a₂) ↔ Fraction.Proper (q₁ + q₂) ∧ a₁ ≡ a₂ := DFracAgree.op_valid

@[rocq_alias frac_agree_op_valid_L]
theorem op_valid_L [Leibniz A] {q₁ q₂ : F} {a₁ a₂ : A} :
    ✓ (mk q₁ a₁ • mk q₂ a₂) ↔ Fraction.Proper (q₁ + q₂) ∧ a₁ = a₂ := DFracAgree.op_valid_L

@[rocq_alias frac_agree_op_validN]
theorem op_validN {q₁ q₂ : F} {a₁ a₂ : A} :
    ✓{n} (mk q₁ a₁ • mk q₂ a₂) ↔ Fraction.Proper (q₁ + q₂) ∧ a₁ ≡{n}≡ a₂ :=
  DFracAgree.op_validN

@[rocq_alias frac_agree_included]
theorem included {q₁ q₂ : F} {a₁ a₂ : A} :
    mk q₁ a₁ ≼ mk q₂ a₂ ↔ (own q₁ ≼ own q₂) ∧ a₁ ≡ a₂ := DFracAgree.included

@[rocq_alias frac_agree_included_L]
theorem included_L [Leibniz A] {q₁ q₂ : F} {a₁ a₂ : A} :
    mk q₁ a₁ ≼ mk q₂ a₂ ↔ (own q₁ ≼ own q₂) ∧ a₁ = a₂ := DFracAgree.included_L

@[rocq_alias frac_agree_includedN]
theorem includedN {q₁ q₂ : F} {a₁ a₂ : A} :
    mk q₁ a₁ ≼{n} mk q₂ a₂ ↔ (own q₁ ≼ own q₂) ∧ a₁ ≡{n}≡ a₂ := DFracAgree.includedN

@[rocq_alias frac_agree_update_2]
theorem update₂ {q₁ q₂ : F} {a₁ a₂ a' : A} (hq : q₁ + q₂ = 1) :
    mk q₁ a₁ • mk q₂ a₂ ~~> mk q₁ a' • mk q₂ a' :=
  DFracAgree.update₂ (show own q₁ • own q₂ = .own 1 from congrArg _ hq)

end Frac

/-! ## Functors -/

@[rocq_alias dfrac_agreeRF]
abbrev DFracAgreeRF [UFraction F] (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  ProdOF (COFE.constOF (DFrac F)) (AgreeRF T)

end DFracAgree

end Iris
