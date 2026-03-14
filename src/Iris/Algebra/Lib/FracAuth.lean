/-
Copyright (c) 2025 Iris contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Algebra.Auth
import Iris.Algebra.LocalUpdates

/-!
# Fractional Authoritative Camera

The fractional authoritative camera has elements `●F{dq} a` (authoritative with discardable
fraction) and `◯F{q} a` (fragment with fraction). Splitting works differently for the two parts:
- `●F{dq1 • dq2} a ≡ ●F{dq1} a • ●F{dq2} a` (duplicates knowledge)
- `◯F{q1 + q2} (a1 • a2) ≡ ◯F{q1} a1 • ◯F{q2} a2` (splits the lower bound)
-/

open Iris

open OFE CMRA UCMRA Auth Option

namespace FracAuth

variable [UFraction F] [CMRA A]

/-! ## Definitions -/

abbrev R := Auth F (Option (Frac F × A))
@[deprecated FracAuth.R (since := "2026-03-14")]
abbrev frac_authR := @R -- Rocq: frac_authR
@[deprecated FracAuth.R (since := "2026-03-14")]
abbrev frac_authUR := @R -- Rocq: frac_authUR

abbrev auth (dq : DFrac F) (a : A) : R (F := F) (A := A) :=
  Auth.auth dq (some (⟨One.one⟩, a))
@[deprecated FracAuth.auth (since := "2026-03-14")]
abbrev frac_auth_auth := @auth -- Rocq: frac_auth_auth

abbrev frag (q : Frac F) (a : A) : R (F := F) (A := A) :=
  Auth.frag (some (q, a))
@[deprecated FracAuth.frag (since := "2026-03-14")]
abbrev frac_auth_frag := @frag -- Rocq: frac_auth_frag

abbrev fragFull (a : A) : R (F := F) (A := A) := frag ⟨One.one⟩ a

notation "●F{" dq "} " a => auth dq a
notation "●F " a => auth (DFrac.own One.one) a
notation "◯F{" q "} " a => frag q a
notation "◯F " a => fragFull a

/-! ## Helpers -/

private theorem frac_one_proper : Fraction.Proper (⟨One.one⟩ : Frac F).car :=
  UFraction.one_whole.1

private def fracOne : Frac F := ⟨One.one⟩

private instance frac_one_exclusive (b : A) :
    CMRA.Exclusive (fracOne (F := F), b) where
  exclusive0_l y h := absurd h.1 (not_exists.mp UFraction.one_whole.2 y.1.1)

private theorem pair_discreteE {a : A} (ha : DiscreteE a) :
    DiscreteE ((⟨One.one⟩ : Frac F), a) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, ha.discrete h2⟩⟩

/-! ## NonExpansive instances -/

instance auth_ne {dq : DFrac F} : NonExpansive (auth dq : A → R) where
  ne _ _ _ h := Auth.auth_ne.ne ⟨.rfl, h⟩
@[deprecated FracAuth.auth_ne (since := "2026-03-14")]
abbrev frac_auth_auth_ne := @auth_ne -- Rocq: frac_auth_auth_ne

instance frag_ne {q : Frac F} : NonExpansive (frag q : A → R) where
  ne _ _ _ h := Auth.frag_ne.ne ⟨.rfl, h⟩
@[deprecated FracAuth.frag_ne (since := "2026-03-14")]
abbrev frac_auth_frag_ne := @frag_ne -- Rocq: frac_auth_frag_ne

/-! ## Discrete instances -/

theorem auth_discrete {dq : DFrac F} {a : A} (ha : DiscreteE a) :
    DiscreteE (●F{dq} a : R) :=
  Auth.auth_discrete (some_is_discrete (pair_discreteE ha)) none_is_discrete
@[deprecated FracAuth.auth_discrete (since := "2026-03-14")]
abbrev frac_auth_auth_discrete := @auth_discrete -- Rocq: frac_auth_auth_discrete

theorem frag_discrete {q : Frac F} {a : A} (ha : DiscreteE a) :
    DiscreteE (◯F{q} a : R (F := F)) :=
  Auth.frag_discrete (some_is_discrete ⟨fun ⟨h1, h2⟩ => ⟨h1, ha.discrete h2⟩⟩)
@[deprecated FracAuth.frag_discrete (since := "2026-03-14")]
abbrev frac_auth_frag_discrete := @frag_discrete -- Rocq: frac_auth_frag_discrete

/-! ## Validity -/

theorem dfrac_validN {dq : DFrac F} {n : Nat} {a : A} (hdq : ✓ dq) (ha : ✓{n} a) :
    ✓{n} ((●F{dq} a : R) • ◯F a) := by
  rw [Auth.both_dfrac_validN]
  exact ⟨hdq, ⟨none, .rfl⟩, frac_one_proper, ha⟩
@[deprecated FracAuth.dfrac_validN (since := "2026-03-14")]
abbrev frac_auth_dfrac_validN := @dfrac_validN -- Rocq: frac_auth_dfrac_validN

theorem validN {n : Nat} {a : A} (ha : ✓{n} a) :
    ✓{n} ((●F a : R (F := F)) • ◯F a) :=
  dfrac_validN DFrac.valid_own_one ha
@[deprecated FracAuth.validN (since := "2026-03-14")]
abbrev frac_auth_validN := @validN -- Rocq: frac_auth_validN

theorem dfrac_valid {dq : DFrac F} {a : A} (hdq : ✓ dq) (ha : ✓ a) :
    ✓ ((●F{dq} a : R) • ◯F a) :=
  Auth.auth_both_dfrac_valid_2 hdq
    ⟨valid_iff_validN.mpr fun _ => frac_one_proper, ha⟩
    ⟨none, .rfl⟩
@[deprecated FracAuth.dfrac_valid (since := "2026-03-14")]
abbrev frac_auth_dfrac_valid := @dfrac_valid -- Rocq: frac_auth_dfrac_valid

theorem valid {a : A} (ha : ✓ a) : ✓ ((●F a : R (F := F)) • ◯F a) :=
  dfrac_valid DFrac.valid_own_one ha
@[deprecated FracAuth.valid (since := "2026-03-14")]
abbrev frac_auth_valid := @valid -- Rocq: frac_auth_valid

/-! ## Agreement -/

theorem agreeN {n : Nat} {dq : DFrac F} {a b : A}
    (h : ✓{n} ((●F{dq} a : R) • ◯F b)) : a ≡{n}≡ b := by
  rw [Auth.both_dfrac_validN] at h
  obtain ⟨_, hinc, hv⟩ := h
  exact (@dist_of_inc_exclusive _ Prod.cmraProd _ _ (frac_one_exclusive b) _ hinc hv).2.symm
@[deprecated FracAuth.agreeN (since := "2026-03-14")]
abbrev frac_auth_agreeN := @agreeN -- Rocq: frac_auth_agreeN

theorem agree {dq : DFrac F} {a b : A}
    (h : ✓ ((●F{dq} a : R) • ◯F b)) : a ≡ b :=
  equiv_dist.mpr fun n => agreeN (valid_iff_validN.mp h n)
@[deprecated FracAuth.agree (since := "2026-03-14")]
abbrev frac_auth_agree := @agree -- Rocq: frac_auth_agree

theorem agree_L [OFE.Leibniz A] {dq : DFrac F} {a b : A}
    (h : ✓ ((●F{dq} a : R) • ◯F b)) : a = b :=
  OFE.Leibniz.eq_of_eqv (agree h)
@[deprecated FracAuth.agree_L (since := "2026-03-14")]
abbrev frac_auth_agree_L := @agree_L -- Rocq: frac_auth_agree_L

/-! ## Inclusion -/

theorem includedN {n : Nat} {dq : DFrac F} {q : Frac F} {a b : A}
    (h : ✓{n} ((●F{dq} a : R) • ◯F{q} b)) : some b ≼{n} some a := by
  rw [Auth.both_dfrac_validN] at h
  obtain ⟨_, ⟨mc, hmc⟩, hv⟩ := h
  match mc with
  | none => exact ⟨none, hmc.2⟩
  | some (_, cr) => exact ⟨some cr, hmc.2⟩
@[deprecated FracAuth.includedN (since := "2026-03-14")]
abbrev frac_auth_includedN := @includedN -- Rocq: frac_auth_includedN

theorem included [CMRA.Discrete A] {dq : DFrac F} {q : Frac F} {a b : A}
    (h : ✓ ((●F{dq} a : R) • ◯F{q} b)) : some b ≼ some a := by
  rw [Auth.both_dfrac_valid_discrete] at h
  obtain ⟨_, ⟨mc, hmc⟩, hv⟩ := h
  match mc with
  | none => exact ⟨none, hmc.2⟩
  | some (_, cr) => exact ⟨some cr, hmc.2⟩
@[deprecated FracAuth.included (since := "2026-03-14")]
abbrev frac_auth_included := @included -- Rocq: frac_auth_included

theorem includedN_total [CMRA.IsTotal A] {n : Nat} {dq : DFrac F} {q : Frac F} {a b : A}
    (h : ✓{n} ((●F{dq} a : R) • ◯F{q} b)) : b ≼{n} a :=
  some_incN_some_iff_isTotal.mp (includedN h)
@[deprecated FracAuth.includedN_total (since := "2026-03-14")]
abbrev frac_auth_includedN_total := @includedN_total -- Rocq: frac_auth_includedN_total

theorem included_total [CMRA.Discrete A] [CMRA.IsTotal A] {dq : DFrac F} {q : Frac F} {a b : A}
    (h : ✓ ((●F{dq} a : R) • ◯F{q} b)) : b ≼ a :=
  inc_of_some_inc_some (included h)
@[deprecated FracAuth.included_total (since := "2026-03-14")]
abbrev frac_auth_included_total := @included_total -- Rocq: frac_auth_included_total

/-! ## Auth-only validity -/

theorem auth_dfrac_validN {n : Nat} {dq : DFrac F} {a : A} :
    (✓{n} (●F{dq} a : R)) ↔ ✓ dq ∧ ✓{n} a := by
  rw [Auth.auth_dfrac_validN]
  exact ⟨fun ⟨hdq, ha⟩ => ⟨hdq, ha.2⟩, fun ⟨hdq, ha⟩ => ⟨hdq, frac_one_proper, ha⟩⟩
@[deprecated FracAuth.auth_dfrac_validN (since := "2026-03-14")]
abbrev frac_auth_auth_dfrac_validN := @auth_dfrac_validN -- Rocq: frac_auth_auth_dfrac_validN

theorem auth_validN {n : Nat} {a : A} :
    (✓{n} (●F a : R (F := F))) ↔ ✓{n} a := by
  rw [auth_dfrac_validN]
  exact ⟨(·.2), (⟨DFrac.valid_own_one, ·⟩)⟩
@[deprecated FracAuth.auth_validN (since := "2026-03-14")]
abbrev frac_auth_auth_validN := @auth_validN -- Rocq: frac_auth_auth_validN

theorem auth_dfrac_valid {dq : DFrac F} {a : A} :
    (✓ (●F{dq} a : R)) ↔ ✓ dq ∧ ✓ a := by
  rw [Auth.auth_dfrac_valid]
  constructor
  · intro ⟨hdq, hva⟩
    exact ⟨hdq, valid_iff_validN.mpr fun n => (valid_iff_validN.mp hva n).2⟩
  · intro ⟨hdq, hva⟩
    exact ⟨hdq, valid_iff_validN.mpr fun n => ⟨frac_one_proper, valid_iff_validN.mp hva n⟩⟩
@[deprecated FracAuth.auth_dfrac_valid (since := "2026-03-14")]
abbrev frac_auth_auth_dfrac_valid := @auth_dfrac_valid -- Rocq: frac_auth_auth_dfrac_valid

theorem auth_valid {a : A} :
    (✓ (●F a : R (F := F))) ↔ ✓ a := by
  rw [auth_dfrac_valid]
  exact ⟨(·.2), (⟨DFrac.valid_own_one, ·⟩)⟩
@[deprecated FracAuth.auth_valid (since := "2026-03-14")]
abbrev frac_auth_auth_valid := @auth_valid -- Rocq: frac_auth_auth_valid

/-! ## Fragment-only validity -/

theorem frag_validN {n : Nat} {q : Frac F} {a : A} :
    (✓{n} (◯F{q} a : R)) ↔ Fraction.Proper q.car ∧ ✓{n} a := by
  rw [Auth.frag_validN]
  rfl
@[deprecated FracAuth.frag_validN (since := "2026-03-14")]
abbrev frac_auth_frag_validN := @frag_validN -- Rocq: frac_auth_frag_validN

theorem frag_valid {q : Frac F} {a : A} :
    (✓ (◯F{q} a : R)) ↔ Fraction.Proper q.car ∧ ✓ a := by
  constructor
  · intro h
    refine ⟨(frag_validN.mp (valid_iff_validN.mp h 0)).1,
           valid_iff_validN.mpr fun n => (frag_validN.mp (valid_iff_validN.mp h n)).2⟩
  · intro ⟨hq, ha⟩
    exact valid_iff_validN.mpr fun n => frag_validN.mpr ⟨hq, valid_iff_validN.mp ha n⟩
@[deprecated FracAuth.frag_valid (since := "2026-03-14")]
abbrev frac_auth_frag_valid := @frag_valid -- Rocq: frac_auth_frag_valid

/-! ## Operations -/

theorem auth_dfrac_op {dq1 dq2 : DFrac F} {a : A} :
    (●F{dq1 • dq2} a : R) ≡ (●F{dq1} a : R) • ●F{dq2} a :=
  Auth.auth_dfrac_op
@[deprecated FracAuth.auth_dfrac_op (since := "2026-03-14")]
abbrev frac_auth_auth_dfrac_op := @auth_dfrac_op -- Rocq: frac_auth_auth_dfrac_op

theorem frag_op {q1 q2 : Frac F} {a1 a2 : A} :
    (◯F{q1 + q2} (a1 • a2) : R (F := F)) ≡ (◯F{q1} a1 : R) • ◯F{q2} a2 := .rfl
@[deprecated FracAuth.frag_op (since := "2026-03-14")]
abbrev frac_auth_frag_op := @frag_op -- Rocq: frac_auth_frag_op

/-! ## Auth-auth op validity -/

theorem auth_dfrac_op_validN {n : Nat} {dq1 dq2 : DFrac F} {a b : A}
    (h : ✓{n} ((●F{dq1} a : R) • ●F{dq2} b)) : ✓ (dq1 • dq2) ∧ a ≡{n}≡ b := by
  rw [Auth.auth_dfrac_op_validN] at h
  exact ⟨h.1, h.2.1.2⟩
@[deprecated FracAuth.auth_dfrac_op_validN (since := "2026-03-14")]
abbrev frac_auth_auth_dfrac_op_validN := @auth_dfrac_op_validN
  -- Rocq: frac_auth_auth_dfrac_op_validN

theorem auth_op_validN {n : Nat} {a b : A}
    (h : ✓{n} ((●F a : R (F := F)) • ●F b)) : False :=
  Auth.auth_op_validN.mp h
@[deprecated FracAuth.auth_op_validN (since := "2026-03-14")]
abbrev frac_auth_auth_op_validN := @auth_op_validN -- Rocq: frac_auth_auth_op_validN

theorem auth_dfrac_op_valid {dq1 dq2 : DFrac F} {a b : A}
    (h : ✓ ((●F{dq1} a : R) • ●F{dq2} b)) : ✓ (dq1 • dq2) ∧ a ≡ b := by
  rw [Auth.auth_dfrac_op_valid] at h
  exact ⟨h.1, h.2.1.2⟩
@[deprecated FracAuth.auth_dfrac_op_valid (since := "2026-03-14")]
abbrev frac_auth_auth_dfrac_op_valid := @auth_dfrac_op_valid
  -- Rocq: frac_auth_auth_dfrac_op_valid

theorem auth_op_valid {a b : A}
    (h : ✓ ((●F a : R (F := F)) • ●F b)) : False :=
  Auth.auth_op_valid.mp h
@[deprecated FracAuth.auth_op_valid (since := "2026-03-14")]
abbrev frac_auth_auth_op_valid := @auth_op_valid -- Rocq: frac_auth_auth_op_valid

/-! ## Fragment-fragment op validity -/

theorem frag_op_validN {n : Nat} {q1 q2 : Frac F} {a b : A} :
    (✓{n} ((◯F{q1} a : R) • ◯F{q2} b)) ↔ Fraction.Proper (q1 + q2).car ∧ ✓{n} (a • b) := by
  show (✓{n} (◯F{q1 + q2} (a • b) : R)) ↔ _
  exact frag_validN
@[deprecated FracAuth.frag_op_validN (since := "2026-03-14")]
abbrev frac_auth_frag_op_validN := @frag_op_validN -- Rocq: frac_auth_frag_op_validN

theorem frag_op_valid {q1 q2 : Frac F} {a b : A} :
    (✓ ((◯F{q1} a : R) • ◯F{q2} b)) ↔ Fraction.Proper (q1 + q2).car ∧ ✓ (a • b) := by
  show (✓ (◯F{q1 + q2} (a • b) : R)) ↔ _
  exact frag_valid
@[deprecated FracAuth.frag_op_valid (since := "2026-03-14")]
abbrev frac_auth_frag_op_valid := @frag_op_valid -- Rocq: frac_auth_frag_op_valid

/-! ## Updates -/

theorem update {q : Frac F} {a b a' b' : A}
    (h : (a, b) ~l~> (a', b')) :
    ((●F a : R (F := F)) • ◯F{q} b) ~~> (●F a') • ◯F{q} b' :=
  Auth.auth_update
    (LocalUpdate.option (LocalUpdate.prod_2 (fracOne (F := F)) q h))
@[deprecated FracAuth.update (since := "2026-03-14")]
abbrev frac_auth_update := @update -- Rocq: frac_auth_update

theorem update_1 {a b a' : A}
    (ha' : ✓ a') :
    ((●F a : R (F := F)) • ◯F b) ~~> (●F a') • ◯F a' :=
  Auth.auth_update
    (LocalUpdate.option
      (@LocalUpdate.exclusive _ _ _ (frac_one_exclusive b)
        _ (fracOne (F := F), a') (show ✓ (fracOne (F := F), a') from ⟨frac_one_proper, ha'⟩)))
@[deprecated FracAuth.update_1 (since := "2026-03-14")]
abbrev frac_auth_update_1 := @update_1 -- Rocq: frac_auth_update_1

theorem update_auth_persist {dq : DFrac F} {a : A} :
    (●F{dq} a : R (F := F)) ~~> ●F{DFrac.discard} a :=
  Auth.auth_update_auth_persist
@[deprecated FracAuth.update_auth_persist (since := "2026-03-14")]
abbrev frac_auth_update_auth_persist := @update_auth_persist
  -- Rocq: frac_auth_update_auth_persist

theorem updateP_auth_unpersist [IsSplitFraction F] {a : A} :
    (●F{DFrac.discard} a : R (F := F)) ~~>: fun k => ∃ q, k = ●F{DFrac.own q} a :=
  Auth.auth_updateP_auth_unpersist
@[deprecated FracAuth.updateP_auth_unpersist (since := "2026-03-14")]
abbrev frac_auth_updateP_auth_unpersist := @updateP_auth_unpersist
  -- Rocq: frac_auth_updateP_auth_unpersist

theorem updateP_both_unpersist [IsSplitFraction F] {q : Frac F} {a b : A} :
    ((●F{DFrac.discard} a : R (F := F)) • ◯F{q} b) ~~>:
      fun k => ∃ q', k = ((●F{DFrac.own q'} a : R) • ◯F{q} b) :=
  Auth.auth_updateP_both_unpersist
@[deprecated FracAuth.updateP_both_unpersist (since := "2026-03-14")]
abbrev frac_auth_updateP_both_unpersist := @updateP_both_unpersist
  -- Rocq: frac_auth_updateP_both_unpersist

/-! ## Functors -/

abbrev FracAuthURF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  Auth.AuthURF (F := F) (OptionOF (ProdOF (COFE.constOF (Frac F)) T))
@[deprecated FracAuth.FracAuthURF (since := "2026-03-14")]
abbrev frac_authURF := @FracAuthURF -- Rocq: frac_authURF

instance instURFunctorContractiveURF {T : COFE.OFunctorPre} [RFunctorContractive T] :
    URFunctorContractive (FracAuthURF (F := F) T) :=
  inferInstance
@[deprecated FracAuth.instURFunctorContractiveURF (since := "2026-03-14")]
abbrev frac_authURF_contractive := @instURFunctorContractiveURF
  -- Rocq: frac_authURF_contractive

abbrev FracAuthRF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  Auth.AuthRF (F := F) (OptionOF (ProdOF (COFE.constOF (Frac F)) T))
@[deprecated FracAuth.FracAuthRF (since := "2026-03-14")]
abbrev frac_authRF := @FracAuthRF -- Rocq: frac_authRF

instance instRFunctorContractiveRF {T : COFE.OFunctorPre} [RFunctorContractive T] :
    RFunctorContractive (FracAuthRF (F := F) T) :=
  inferInstance
@[deprecated FracAuth.instRFunctorContractiveRF (since := "2026-03-14")]
abbrev frac_authRF_contractive := @instRFunctorContractiveRF
  -- Rocq: frac_authRF_contractive

end FracAuth
