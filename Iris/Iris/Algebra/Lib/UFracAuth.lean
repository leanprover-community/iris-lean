/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.IsOp
public import Iris.Algebra.UFrac
import Iris.Algebra.LocalUpdates
meta import Iris.Std.RocqPorting

/-!
# Unbounded Fractional Authoritative Camera

The unbounded fractional authoritative camera supports authoritative elements and fragments whose
fractions may exceed one. In addition to the usual fractional-authoritative operations, an
authoritative element can allocate a new fragment by increasing its fraction and adding the
fragment's resource to its payload.
-/

open Iris OFE CMRA UCMRA Auth Option UFrac

/-! ## Definitions -/

@[rocq_alias ufrac_authR, rocq_alias ufrac_authUR]
public abbrev UFracAuth [CMRA A] := Auth (Option (UFrac × A))

namespace UFracAuth

variable [CMRA A]

@[rocq_alias ufrac_auth_auth]
public abbrev auth (q : Qp) (a : A) : UFracAuth (A := A) :=
  Auth.auth (.own 1) (some (⟨q⟩, a))

@[rocq_alias ufrac_auth_frag]
public abbrev frag (q : Qp) (a : A) : UFracAuth (A := A) :=
  Auth.frag (some (⟨q⟩, a))

notation "●U{" q "} " a => auth q a
notation "◯U{" q "} " a => frag q a

/-! ## NonExpansive instances -/

@[rocq_alias ufrac_auth_auth_ne]
instance auth_ne {q : Qp} : NonExpansive (auth q : A → UFracAuth) where
  ne _ _ _ h := Auth.auth_ne.ne ⟨.rfl, h⟩

#rocq_ignore ufrac_auth_auth_proper "Derivable from auth_ne with NonExpansive.eqv"

@[rocq_alias ufrac_auth_frag_ne]
instance frag_ne {q : Qp} : NonExpansive (frag q : A → UFracAuth) where
  ne _ _ _ h := Auth.frag_ne.ne ⟨.rfl, h⟩

#rocq_ignore ufrac_auth_frag_proper "Derivable from frag_ne with NonExpansive.eqv"

/-! ## Discrete instances -/

@[rocq_alias ufrac_auth_auth_discrete]
instance auth_discrete {q : Qp} {a : A} [DiscreteE a] : DiscreteE (●U{q} a : UFracAuth) :=
  letI _ : DiscreteE (unit : Option (UFrac × A)) := none_is_discrete
  by infer_instance

@[rocq_alias ufrac_auth_frag_discrete]
instance frag_discrete {q : Qp} {a : A} [DiscreteE a] : DiscreteE (◯U{q} a : UFracAuth) :=
  by infer_instance

/-! ## Validity -/

@[rocq_alias ufrac_auth_validN]
theorem validN {n : Nat} {a : A} {p : Qp} (ha : ✓{n} a) :
    ✓{n} ((●U{p} a : UFracAuth) • ◯U{p} a) := by
  simpa only [Auth.both_validN] using ⟨incN_refl _, ⟨trivial, ha⟩⟩

@[rocq_alias ufrac_auth_valid]
theorem valid {p : Qp} {a : A} (ha : ✓ a) : ✓ ((●U{p} a : UFracAuth) • ◯U{p} a) :=
  Auth.auth_both_valid_2 ⟨trivial, ha⟩ ⟨none, .rfl⟩

/-! ## Agreement -/

@[rocq_alias ufrac_auth_agreeN]
theorem agreeN {n : Nat} {p : Qp} {a b : A} (h : ✓{n} ((●U{p} a : UFracAuth) • ◯U{p} b)) :
    a ≡{n}≡ b := by
  obtain ⟨mc, hmc⟩ := (Auth.both_validN.mp h).1
  match mc with
  | none => exact hmc.2
  | some (r, _) =>
    have hp : p = p + r.frac := UFrac.ext_iff.mp hmc.1
    grind

@[rocq_alias ufrac_auth_agree]
theorem agree {p : Qp} {a b : A} (h : ✓ ((●U{p} a : UFracAuth) • ◯U{p} b)) : a ≡ b :=
  equiv_dist.mpr fun n => agreeN (valid_iff_validN.mp h n)

@[rocq_alias ufrac_auth_agree_L]
theorem agree_L {p : Qp} {a b : A} (h : ✓ ((●U{p} a : UFracAuth) • ◯U{p} b)) : a = b :=
  (agree h).to_eq

/-! ## Inclusion -/

@[rocq_alias ufrac_auth_includedN]
theorem includedN {n : Nat} {p q : Qp} {a b : A}
    (h : ✓{n} ((●U{p} a : UFracAuth) • ◯U{q} b)) : some b ≼{n} some a := by
  rw [Auth.both_validN] at h
  obtain ⟨⟨mc, hmc⟩, _⟩ := h
  match mc with
  | none => exact ⟨none, hmc.2⟩
  | some (_, cr) => exact ⟨some cr, hmc.2⟩

@[rocq_alias ufrac_auth_included]
theorem included [CMRA.Discrete A] {q p : Qp} {a b : A}
    (h : ✓ ((●U{p} a : UFracAuth) • ◯U{q} b)) : some b ≼ some a := by
  rw [Auth.auth_both_valid_discrete] at h
  obtain ⟨⟨mc, hmc⟩, _⟩ := h
  match mc with
  | none => exact ⟨none, fun n => (hmc n).2⟩
  | some (_, cr) => exact ⟨some cr, fun n => (hmc n).2⟩

@[rocq_alias ufrac_auth_includedN_total]
theorem includedN_total [IsTotal A] {n : Nat} {q p : Qp} {a b : A}
    (h : ✓{n} ((●U{p} a : UFracAuth) • ◯U{q} b)) : b ≼{n} a :=
  some_incN_some_iff_is_total.mp <| includedN h

@[rocq_alias ufrac_auth_included_total]
theorem included_total [CMRA.Discrete A] [IsTotal A] {q p : Qp} {a b : A}
    (h : ✓ ((●U{p} a : UFracAuth) • ◯U{q} b)) : b ≼ a :=
  inc_of_some_inc_some <| included h

/-! ## Auth-only validity -/

@[rocq_alias ufrac_auth_auth_validN]
theorem auth_validN {n : Nat} {q : Qp} {a : A} : (✓{n} (●U{q} a : UFracAuth)) ↔ ✓{n} a := by
  rw [Auth.auth_validN]
  exact ⟨(·.2), (⟨trivial, ·⟩)⟩

@[rocq_alias ufrac_auth_auth_valid]
theorem auth_valid {q : Qp} {a : A} : (✓ (●U{q} a : UFracAuth)) ↔ ✓ a := by
  rw [Auth.auth_valid]
  exact ⟨(·.2), (⟨trivial, ·⟩)⟩

/-! ## Fragment-only validity -/

@[rocq_alias ufrac_auth_frag_validN]
theorem frag_validN {n : Nat} {q : Qp} {a : A} : (✓{n} (◯U{q} a : UFracAuth)) ↔ ✓{n} a := by
  rw [Auth.frag_validN]
  exact ⟨(·.2), (⟨trivial, ·⟩)⟩

@[rocq_alias ufrac_auth_frag_valid]
theorem frag_valid {q : Qp} {a : A} : (✓ (◯U{q} a : UFracAuth)) ↔ ✓ a := by
  rw [Auth.frag_valid]
  exact ⟨(·.2), (⟨trivial, ·⟩)⟩

/-! ## Operations -/

@[rocq_alias ufrac_auth_frag_op]
theorem frag_op {q1 q2 : Qp} {a1 a2 : A} :
    (◯U{q1 + q2} (a1 • a2) : UFracAuth) ≡ (◯U{q1} a1) • ◯U{q2} a2 := .rfl

@[rocq_alias ufrac_auth_frag_op_validN]
theorem frag_op_validN {n : Nat} {q1 q2 : Qp} {a b : A} :
    (✓{n} ((◯U{q1} a : UFracAuth) • ◯U{q2} b)) ↔ ✓{n} (a • b) := frag_validN

@[rocq_alias ufrac_auth_frag_op_valid]
theorem frag_op_valid {q1 q2 : Qp} {a b : A} :
    (✓ ((◯U{q1} a : UFracAuth) • ◯U{q2} b)) ↔ ✓ (a • b) := frag_valid

/-! ## IsOp type class instances -/

@[rocq_alias ufrac_auth_is_op]
instance isOp_ufrac_auth {q q1 q2 : Qp} {a1 a2 : A} {a : outParam A}
    [h1 : IsOp io q q1 q2] [h2 : IsOp io a a1 a2] : IsOp io (◯U{q} a) (◯U{q1} a1) (◯U{q2} a2) where
  is_op := NonExpansive.eqv (OFE.some_eqv_some.mpr
    (NonExpansive₂.eqv (OFE.Equiv.of_eq (UFrac.ext_iff.mpr h1.is_op.to_eq)) h2.is_op))

set_option synthInstance.checkSynthOrder false in
@[rocq_alias ufrac_auth_is_op_core_id]
instance isOp_ufrac_auth_core_id {q q1 q2 : Qp} {a : A} [h1 : CoreId a] [h2 : IsOp io q q1 q2] :
    IsOp io (◯U{q} a) (◯U{q1} a) (◯U{q2} a) where
  is_op := NonExpansive.eqv (OFE.some_eqv_some.mpr
    (NonExpansive₂.eqv (OFE.Equiv.of_eq (UFrac.ext_iff.mpr h2.is_op.to_eq)) (op_self a).symm))

/-! ## Updates -/

@[rocq_alias ufrac_auth_update]
theorem update {p q : Qp} {a b a' b' : A} (h : (a, b) ~l~> (a', b')) :
    ((●U{p} a : UFracAuth) • ◯U{q} b) ~~> (●U{p} a') • ◯U{q} b' :=
  auth_update <| .option (.prod_2 _ _ h)

@[rocq_alias ufrac_auth_update_surplus]
theorem update_surplus {p q : Qp} {a b : A} (h : ✓ (a • b)) :
    (●U{p} a : UFracAuth) ~~> (●U{p + q} (a • b)) • ◯U{q} b := by
  refine Auth.auth_update_alloc (local_update_unital.mpr fun n mpa _ heq => ?_)
  refine ⟨⟨trivial, h.validN⟩, ?_⟩
  have hop : some ((⟨p + q⟩ : UFrac), a • b) ≡{n}≡ some ((⟨q⟩ : UFrac), b) • some ((⟨p⟩ : UFrac), a) :=
    ⟨CMRA.comm.dist, CMRA.op_commN⟩
  refine hop.trans ?_
  exact (heq.trans (CMRA.unit_left_id_dist mpa)).op_r

@[rocq_alias ufrac_auth_update_surplus_cancel]
theorem update_surplus_cancel {p q : Qp} {a b : A} (h : CMRA.Cancelable b) :
    ((●U{p + q} (a • b) : UFracAuth) • ◯U{q} b) ~~> ●U{p} a := by
  letI : CMRA.Cancelable b := h
  refine Auth.auth_update_dealloc (local_update_unital.mpr fun n mpa hv heq => ?_)
  match mpa with
  | none =>
    have hp : p + q = q := UFrac.ext_iff.mp heq.1
    grind
  | some (p', a') =>
    have hpq : p + q = q + p'.frac := UFrac.ext_iff.mp heq.1
    have hp : p = p'.frac := by grind
    refine ⟨⟨trivial, CMRA.validN_op_left hv.2⟩, ?_⟩
    refine ⟨OFE.Dist.of_eq (UFrac.ext_iff.mpr hp), ?_⟩
    refine CMRA.cancelableN ?_ (CMRA.op_commN.trans heq.2)
    exact (OFE.Dist.validN CMRA.op_commN).mp hv.2

/-! ## Functors -/

@[rocq_alias ufrac_authURF]
abbrev UFracAuthURF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  AuthURF (OptionOF (ProdOF (constOF UFrac) T))

#rocq_ignore ufrac_authURF_contractive "Contractiveness is bundled into Lean's RFunctor type class and inferred for AuthURF"

@[rocq_alias ufrac_authRF]
abbrev UFracAuthRF (T : COFE.OFunctorPre) [RFunctor T] : COFE.OFunctorPre :=
  AuthRF (OptionOF (ProdOF (constOF UFrac) T))

#rocq_ignore ufrac_authRF_contractive "Contractiveness is bundled into Lean's RFunctor type class and inferred for AuthRF"

end UFracAuth
