/-
Copyright (c) 2025 Iris contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Auth
import Iris.Algebra.LocalUpdates
meta import Iris.Std.RocqAlias

/-!
# Fractional Authoritative Camera

The fractional authoritative camera has elements `●F{dq} a` (authoritative with discardable
fraction) and `◯F{q} a` (fragment with fraction). Splitting works differently for the two parts:
- `●F{dq1 • dq2} a ≡ ●F{dq1} a • ●F{dq2} a` (duplicates knowledge)
- `◯F{q1 + q2} (a1 • a2) ≡ ◯F{q1} a1 • ◯F{q2} a2` (splits the lower bound)
-/

open Iris OFE CMRA UCMRA Auth Option


/-! ## Definitions -/

@[rocq_alias frac_authR]
public abbrev FracAuth [UFraction F] [CMRA A] := Auth F (Option (Frac F × A))

namespace FracAuth

variable [UFraction F] [CMRA A]

@[rocq_alias frac_auth_auth]
public abbrev auth (dq : DFrac F) (a : A) : FracAuth (F := F) (A := A) := Auth.auth dq (some (⟨One.one⟩, a))

@[rocq_alias frac_auth_frag]
public abbrev frag (q : Frac F) (a : A) : FracAuth (F := F) (A := A) := Auth.frag (some (q, a))

public abbrev fragFull (a : A) : FracAuth (F := F) (A := A) := frag ⟨One.one⟩ a

notation "●F{" dq "} " a => auth dq a
notation "●F " a => auth (DFrac.own One.one) a
notation "◯F{" q "} " a => frag q a
notation "◯F " a => fragFull a

abbrev fracOne : Frac F := ⟨One.one⟩

instance frac_one_exclusive (b : A) : Exclusive (fracOne (F := F), b) where
  exclusive0_l y h := absurd h.1 (not_exists.mp UFraction.one_whole.2 y.1.1)

/-! ## NonExpansive instances -/

@[rocq_alias frac_auth_auth_ne]
instance auth_ne {dq : DFrac F} : NonExpansive (auth dq : A → FracAuth) where
  ne _ _ _ h := Auth.auth_ne.ne ⟨.rfl, h⟩

@[rocq_alias frac_auth_frag_ne]
instance frag_ne {q : Frac F} : NonExpansive (frag q : A → FracAuth) where
  ne _ _ _ h := Auth.frag_ne.ne ⟨.rfl, h⟩

/-! ## Discrete instances -/

@[rocq_alias frac_auth_auth_discrete]
theorem auth_discrete {dq : DFrac F} {a : A} (ha : DiscreteE a) : DiscreteE (●F{dq} a : FracAuth) :=
  Auth.auth_discrete (some_is_discrete (prod.is_discrete ⟨discrete_0⟩ ha)) none_is_discrete

@[rocq_alias frac_auth_frag_discrete]
theorem frag_discrete {q : Frac F} {a : A} (ha : DiscreteE a) : DiscreteE (◯F{q} a : FracAuth) :=
  Auth.frag_discrete (some_is_discrete (prod.is_discrete ⟨discrete_0⟩ ha))

/-! ## Validity -/

@[rocq_alias frac_auth_dfrac_validN]
theorem dfrac_validN {dq : DFrac F} {n : Nat} {a : A} (hdq : ✓ dq) (ha : ✓{n} a) :
    ✓{n} (●F{dq} a) • ◯F a := by
  simpa only [both_dfrac_validN] using ⟨hdq, ⟨none, .rfl⟩, UFraction.one_whole.1, ha⟩

@[rocq_alias frac_auth_validN]
theorem validN {n : Nat} {a : A} (ha : ✓{n} a) : ✓{n} (●F a : FracAuth (F := F)) • ◯F a :=
  dfrac_validN DFrac.valid_own_one ha

@[rocq_alias frac_auth_dfrac_valid]
theorem dfrac_valid {dq : DFrac F} {a : A} (hdq : ✓ dq) (ha : ✓ a) : ✓ (●F{dq} a) • ◯F a :=
  auth_both_dfrac_valid_2 hdq ⟨valid_iff_validN.mpr fun _ => UFraction.one_whole.1, ha⟩ ⟨none, .rfl⟩

@[rocq_alias frac_auth_valid]
theorem valid {a : A} (ha : ✓ a) : ✓ (●F a : FracAuth (F := F)) • ◯F a :=
  dfrac_valid DFrac.valid_own_one ha

/-! ## Agreement -/

@[rocq_alias frac_auth_agreeN]
theorem agreeN {dq : DFrac F} {a b : A} (h : ✓{n} (●F{dq} a) • ◯F b) : a ≡{n}≡ b := by
  rw [both_dfrac_validN] at h
  exact (dist_of_inc_exclusive h.2.1 h.2.2).2.symm

@[rocq_alias frac_auth_agree]
theorem agree {dq : DFrac F} {a b : A} (h : ✓ (●F{dq} a) • ◯F b) : a ≡ b :=
  equiv_dist.mpr fun n => agreeN (valid_iff_validN.mp h n)

@[rocq_alias frac_auth_agree_L]
theorem agree_L [OFE.Leibniz A] {dq : DFrac F} {a b : A} (h : ✓ (●F{dq} a) • ◯F b) : a = b :=
  eq_of_eqv (agree h)

/-! ## Inclusion -/

@[rocq_alias frac_auth_includedN]
theorem includedN {n : Nat} {dq : DFrac F} {q : Frac F} {a b : A} (h : ✓{n} (●F{dq} a) • ◯F{q} b) :
    some b ≼{n} some a := by
  rw [both_dfrac_validN] at h
  obtain ⟨_, ⟨mc, hmc⟩, hv⟩ := h
  match mc with
  | none => exact ⟨none, hmc.2⟩
  | some (_, cr) => exact ⟨some cr, hmc.2⟩

@[rocq_alias frac_auth_included]
theorem included [CMRA.Discrete A] {dq : DFrac F} {a b : A} (h : ✓ (●F{dq} a) • ◯F{q} b) :
      some b ≼ some a := by
  rw [both_dfrac_valid_discrete] at h
  obtain ⟨_, ⟨mc, hmc⟩, hv⟩ := h
  match mc with
  | none => exact ⟨none, hmc.2⟩
  | some (_, cr) => exact ⟨some cr, hmc.2⟩

@[rocq_alias frac_auth_includedN_total]
theorem includedN_total [IsTotal A] {dq : DFrac F} {a b : A} (h : ✓{n} (●F{dq} a) • ◯F{q} b) :
    b ≼{n} a :=
  some_incN_some_iff_isTotal.mp (includedN h)

@[rocq_alias frac_auth_included_total]
theorem included_total [CMRA.Discrete A] [IsTotal A] {dq : DFrac F} {a b : A}
    (h : ✓ (●F{dq} a) • ◯F{q} b) : b ≼ a :=
  inc_of_some_inc_some (included h)

/-! ## Auth-only validity -/

@[rocq_alias frac_auth_auth_dfrac_validN]
theorem auth_dfrac_validN {dq : DFrac F} {a : A} : (✓{n} ●F{dq} a) ↔ ✓ dq ∧ ✓{n} a := by
  rw [Auth.auth_dfrac_validN]
  exact ⟨fun ⟨hdq, ha⟩ => ⟨hdq, ha.2⟩, fun ⟨hdq, ha⟩ => ⟨hdq, UFraction.one_whole.1, ha⟩⟩

@[rocq_alias frac_auth_auth_validN]
theorem auth_validN {a : A} : (✓{n} (●F a : FracAuth (F := F))) ↔ ✓{n} a := by
  rw [auth_dfrac_validN]
  exact ⟨(·.2), (⟨DFrac.valid_own_one, ·⟩)⟩

@[rocq_alias frac_auth_auth_dfrac_valid]
theorem auth_dfrac_valid {dq : DFrac F} {a : A} : (✓ ●F{dq} a) ↔ ✓ dq ∧ ✓ a := by
  rw [Auth.auth_dfrac_valid]
  refine ⟨fun ⟨hq, ha⟩ => ?_, fun ⟨hq, ha⟩ => ?_⟩
  · exact ⟨hq, valid_iff_validN.mpr fun n => (valid_iff_validN.mp ha n).2⟩
  · exact ⟨hq, valid_iff_validN.mpr fun n => ⟨UFraction.one_whole.1, valid_iff_validN.mp ha n⟩⟩

@[rocq_alias frac_auth_auth_valid]
theorem auth_valid {a : A} : (✓ (●F a : FracAuth (F := F))) ↔ ✓ a := by
  rw [auth_dfrac_valid]
  exact ⟨(·.2), (⟨DFrac.valid_own_one, ·⟩)⟩

/-! ## Fragment-only validity -/

@[rocq_alias frac_auth_frag_validN]
theorem frag_validN {q : Frac F} {a : A} : (✓{n} ◯F{q} a) ↔ Fraction.Proper q.car ∧ ✓{n} a := by
  rw [Auth.frag_validN]; rfl

@[rocq_alias frac_auth_frag_valid]
theorem frag_valid {q : Frac F} {a : A} : (✓ ◯F{q} a) ↔ Fraction.Proper q.car ∧ ✓ a := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hq, ha⟩ => ?_⟩
  · exact (frag_validN.mp (valid_iff_validN.mp h 0)).1
  · exact valid_iff_validN.mpr fun n => (frag_validN.mp (valid_iff_validN.mp h n)).2
  · exact valid_iff_validN.mpr fun n => frag_validN.mpr ⟨hq, valid_iff_validN.mp ha n⟩

/-! ## Operations -/

@[rocq_alias frac_auth_auth_dfrac_op]
theorem auth_dfrac_op {dq1 dq2 : DFrac F} {a : A} : (●F{dq1 • dq2} a) ≡ (●F{dq1} a) • ●F{dq2} a :=
  Auth.auth_dfrac_op

@[rocq_alias frac_auth_frag_op]
theorem frag_op {q1 q2 : Frac F} {a1 a2 : A} : (◯F{q1 + q2} (a1 • a2)) ≡ (◯F{q1} a1) • ◯F{q2} a2 :=
  .rfl

/-! ## Auth-auth op validity -/

@[rocq_alias frac_auth_auth_dfrac_op_validN]
theorem auth_dfrac_op_validN {dq1 dq2 : DFrac F} {a b : A} (h : ✓{n} (●F{dq1} a) • ●F{dq2} b) :
    ✓ (dq1 • dq2) ∧ a ≡{n}≡ b := by
  rw [Auth.auth_dfrac_op_validN] at h
  exact ⟨h.1, h.2.1.2⟩

@[rocq_alias frac_auth_auth_op_validN]
theorem auth_op_validN {a b : A} (h : ✓{n} (●F a : FracAuth (F := F)) • ●F b) : False :=
  Auth.auth_op_validN.mp h

@[rocq_alias frac_auth_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid {dq1 dq2 : DFrac F} {a b : A} (h : ✓ (●F{dq1} a) • ●F{dq2} b) :
    ✓ (dq1 • dq2) ∧ a ≡ b := by
  rw [Auth.auth_dfrac_op_valid] at h
  exact ⟨h.1, h.2.1.2⟩

@[rocq_alias frac_auth_auth_op_valid]
theorem auth_op_valid {a b : A} (h : ✓ (●F a : FracAuth (F := F)) • ●F b) : False :=
  Auth.auth_op_valid.mp h

/-! ## Fragment-fragment op validity -/

@[rocq_alias frac_auth_frag_op_validN]
theorem frag_op_validN {q1 q2 : Frac F} {a b : A} :
    (✓{n} (◯F{q1} a) • ◯F{q2} b) ↔ Fraction.Proper (q1 + q2).car ∧ ✓{n} (a • b) := by
  show ✓{n} (◯F{q1 + q2} (a • b)) ↔ _
  exact frag_validN

@[rocq_alias frac_auth_frag_op_valid]
theorem frag_op_valid {q1 q2 : Frac F} {a b : A} :
    (✓ (◯F{q1} a) • ◯F{q2} b) ↔ Fraction.Proper (q1 + q2).car ∧ ✓ (a • b) := by
  show ✓ (◯F{q1 + q2} (a • b)) ↔ _
  exact frag_valid

/-! ## Updates -/

@[rocq_alias frac_auth_update]
theorem update {q : Frac F} {a b a' b' : A} (h : (a, b) ~l~> (a', b')) :
    ((●F a : FracAuth (F := F)) • ◯F{q} b) ~~> (●F a') • ◯F{q} b' :=
  auth_update (.option (.prod_2 _ q h))

@[rocq_alias frac_auth_update_1]
theorem update_full {a b a' : A} (ha' : ✓ a') :
    ((●F a : FracAuth (F := F)) • ◯F b) ~~> (●F a') • ◯F a' :=
   auth_update (.option (.exclusive ⟨UFraction.one_whole.1, ha'⟩))

@[rocq_alias frac_auth_update_auth_persist]
theorem update_auth_persist {dq : DFrac F} {a : A} : (●F{dq} a) ~~> ●F{.discard} a :=
  Auth.auth_update_auth_persist

@[rocq_alias frac_auth_updateP_auth_unpersist]
theorem updateP_auth_unpersist [IsSplitFraction F] {a : A} :
    (●F{.discard} a : FracAuth (F := F)) ~~>: fun k => ∃ q, k = ●F{.own q} a :=
  Auth.auth_updateP_auth_unpersist

@[rocq_alias frac_auth_updateP_both_unpersist]
theorem updateP_both_unpersist [IsSplitFraction F] {q : Frac F} {a b : A} :
    ((●F{DFrac.discard} a) • ◯F{q} b) ~~>: fun k => ∃ q', k = (●F{.own q'} a) • ◯F{q} b :=
  auth_updateP_both_unpersist

/-! ## Functors -/

@[rocq_alias frac_authURF]
abbrev FracAuthURF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  AuthURF (F := F) (OptionOF (ProdOF (COFE.constOF (Frac F)) T))

@[rocq_alias frac_authRF]
abbrev FracAuthF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  AuthRF (F := F) (OptionOF (ProdOF (COFE.constOF (Frac F)) T))

end FracAuth
